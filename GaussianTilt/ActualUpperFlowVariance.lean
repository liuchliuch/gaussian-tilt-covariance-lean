import GaussianTilt.ActualUpperFlow
import GaussianTilt.Whitening

/-!
# Reducing the upper-flow variance inputs to isotropic Letwin

This file proves every affine-transport, noncentered, and initial-variance step.
The sole remaining analytic input is the explicitly named proposition
`IsotropicQuadraticVarianceBound`. No proof of that proposition is assumed
implicitly, and no original numbered result is claimed here without it.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator

namespace GaussianTilt.Reference

/-- The compact isotropic specialization of the still-required analytic
quadratic-variance theorem. This is a proposition definition, not an axiom. -/
def IsotropicQuadraticVarianceBound : Prop :=
  ∀ (n : ℕ) (μ : Measure (Space n)), IsProbabilityMeasure μ →
    compactlySupported μ → isotropic μ → logconcave μ →
    ∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian →
      ProbabilityTheory.variance (fun x : Space n ↦ matrixQuadratic A (fun i ↦ x i)) μ ≤
        8 * Matrix.trace (A ^ 2)

/-- The centered covariance form follows by actual affine whitening. -/
theorem centered_quadratic_variance_of_isotropic_bound
    (hL : IsotropicQuadraticVarianceBound) {n : ℕ}
    (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hc : compactlySupported μ) (hl : logconcave μ)
    (hC : (covariance μ).PosDef) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) :
    ProbabilityTheory.variance
      (fun x : Space n ↦ matrixQuadratic B ((fun i ↦ x i) - meanVector μ (fun x ↦ fun i ↦ x i))) μ ≤
      8 * Matrix.trace ((B * covariance μ) ^ 2) := by
  obtain ⟨P, rfl⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported μ hc
  have hX (i : Fin n) : MemLp (fun x : Space n ↦ x i) 2 P.measure := by
    simpa only [P.tilt_zero] using
      P.memLp_continuous_tilt (f := fun x : Point n ↦ x i) (by fun_prop) 0 2
  have hcov : Whitening.covariance P.measure = covariance P.measure :=
    (covariance_eq_covarianceMatrix hX).symm
  have hC' : (Whitening.covariance P.measure).PosDef := hcov.symm ▸ hC
  have hBs : B.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hB
  have hA : (Whitening.root (Whitening.covariance P.measure) * B *
      Whitening.root (Whitening.covariance P.measure)).IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Whitening.sandwich_symm B (Whitening.covariance P.measure) hBs
  have h := hL n (Whitening.law P.measure) inferInstance
    (Whitening.law_compactlySupported hc) (Whitening.law_isotropic hX hC')
    (Whitening.law_logconcave hl hC') _ hA
  have ht := Whitening.quadratic_variance_transport hC' B
  simp only [Whitening.coordinates] at ht
  rw [Whitening.sandwich_trace_square B hC'.posSemidef] at h
  simp only [hcov] at h
  convert h using 1
  simpa only [hcov] using ht.symm

end GaussianTilt.Reference

namespace GaussianTilt.CompactProbability
variable {n : ℕ} (P : CompactProbability n)

/-- Every tilted noncentered quadratic variance follows from the sole
isotropic analytic inequality by whitening and the exact rank-one algebra. -/
theorem quadraticVarianceAlongTilt_of_isotropic_bound
    (hL : Reference.IsotropicQuadraticVarianceBound)
    (hl : Reference.logconcave P.measure) (hi : Reference.isotropic P.measure) :
    P.QuadraticVarianceAlongTilt := by
  intro t ht B hB
  have hBs : B.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hB
  have hcenter := Reference.centered_quadratic_variance_of_isotropic_bound hL (P.tilt t)
    (P.reference_tilt_compactlySupported t) (P.logconcave_tilt ht hl)
    (P.covariance_posDef hi t) B hB
  rw [P.reference_covariance_eq_covarianceMatrix t] at hcenter
  exact noncentered_variance_of_centered_bound
    (fun i ↦ P.memLp_continuous_tilt (f := fun x : Point n ↦ x i) (by fun_prop) t 2)
    B hBs (P.memLp_continuous_tilt
      (by unfold matrixQuadratic Matrix.mulVec dotProduct; fun_prop) t 2) hcenter

/-- The sharper initial radial bound needed by the entropy barrier. -/
theorem initial_radial_variance_of_isotropic_bound
    (hL : Reference.IsotropicQuadraticVarianceBound)
    (hl : Reference.logconcave P.measure) (hi : Reference.isotropic P.measure) :
    P.variance 0 energy ≤ 8 * (n : ℝ) := by
  have h := hL n P.measure inferInstance P.reference_compactlySupported hi hl 1
    Matrix.isHermitian_one
  have hp (x : Point n) : matrixQuadratic (1 : Matrix (Fin n) (Fin n) ℝ)
      (fun i ↦ x i) = energy x := by
    simp only [matrixQuadratic, Matrix.one_mulVec, dotProduct, energy_eq_sum_sq, pow_two]
  rw [P.variance_eq_probabilityVariance (P.memLp_continuous_tilt continuous_energy 0 2),
    P.tilt_zero]
  simpa only [hp, one_pow, Matrix.trace_one, Fintype.card_fin, Nat.cast_id] using h

/-- Complete actual flow from precisely the unresolved isotropic analytic input. -/
theorem scalarFlowInputs_of_isotropic_bound
    (hL : Reference.IsotropicQuadraticVarianceBound)
    (hl : Reference.logconcave P.measure) (hi : Reference.isotropic P.measure)
    (hn : 0 < n) :
    UpperDynamics.ScalarFlowInputs (n : ℝ) Paouris.spectralTiltConstant 2
      (fun t ↦ ‖P.momentMatrix t‖) P.momentHS P.entropy (fun t ↦ P.variance t energy) :=
  P.scalarFlowInputs_of_quadratic_variance hl hi hn
    (P.quadraticVarianceAlongTilt_of_isotropic_bound hL hl hi)
    (P.initial_radial_variance_of_isotropic_bound hL hl hi)

end GaussianTilt.CompactProbability
