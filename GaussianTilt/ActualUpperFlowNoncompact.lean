import GaussianTilt.ActualUpperFlowVariance
import GaussianTilt.NoncenteredMomentIntegrability

/-!
# The full noncompact quadratic estimate from compact isotropic Letwin

Actual whitening, fourth-moment integrability, compact approximation, covariance
transport, and the noncentered rank-one step are all proved here or imported.
The sole conditional analytic input is the compact isotropic variance theorem.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator

namespace GaussianTilt.Reference

/-- Original full noncompact isotropic variance scope follows from the compact
analytic theorem using the proved Paouris fourth-moment and actual truncation. -/
theorem isotropic_quadratic_variance_of_compact_bound
    (hL : IsotropicQuadraticVarianceBound) {n : ℕ}
    (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hl : logconcave μ) (hi : isotropic μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) :
    ProbabilityTheory.variance (fun x : Space n ↦ matrixQuadratic B (fun i ↦ x i)) μ ≤
      8 * Matrix.trace (B ^ 2) := by
  have hBs : B.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hB
  apply Whitening.isotropic_quadratic_bound_of_compact (C := 8) ?_ μ hl hi B hBs
  intro ν hν hc hl hi A hA
  exact hL n ν hν hc hi hl A (by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA)

/-- Centered quadratic covariance form for every nondegenerate logconcave law,
with no compactness or integrability assumption hidden in the statement. -/
theorem centered_quadratic_variance_of_isotropic_compact_bound
    (hL : IsotropicQuadraticVarianceBound) {n : ℕ}
    (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hl : logconcave μ) (hC : (covariance μ).PosDef)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) :
    ProbabilityTheory.variance
      (fun x : Space n ↦ matrixQuadratic B ((fun i ↦ x i) - meanVector μ (fun x ↦ fun i ↦ x i))) μ ≤
      8 * Matrix.trace ((B * covariance μ) ^ 2) := by
  have hX := posDef_coordinate_memLp hC
  have hcov : Whitening.covariance μ = covariance μ :=
    (covariance_eq_covarianceMatrix hX).symm
  have hC' := posDef_whitening_covariance hC
  have hBs : B.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hB
  have hA : (Whitening.root (Whitening.covariance μ) * B *
      Whitening.root (Whitening.covariance μ)).IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Whitening.sandwich_symm B (Whitening.covariance μ) hBs
  have h := isotropic_quadratic_variance_of_compact_bound hL (Whitening.law μ)
    (Whitening.law_logconcave hl hC') (Whitening.law_isotropic hX hC') _ hA
  have ht := Whitening.quadratic_variance_transport hC' B
  simp only [Whitening.coordinates] at ht
  rw [Whitening.sandwich_trace_square B hC'.posSemidef] at h
  simp only [hcov] at h
  convert h using 1
  simpa only [hcov] using ht.symm

/-- Original Lemma 2.6 at its full noncompact scope, conditional only on the
compact isotropic analytic theorem. All other inputs are proved from the law. -/
theorem original2_6_of_isotropic_bound
    (hL : IsotropicQuadraticVarianceBound) {n : ℕ}
    (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hl : logconcave μ) (hC : (covariance μ).PosDef)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) :
    ProbabilityTheory.variance (fun x : Space n ↦ matrixQuadratic B (fun i ↦ x i)) μ ≤
      10 * Matrix.trace ((B * secondMomentMatrix μ (fun x : Space n ↦ fun i ↦ x i)) ^ 2) := by
  have hX := posDef_coordinate_memLp hC
  have hBs : B.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hB
  have hc := centered_quadratic_variance_of_isotropic_compact_bound hL μ hl hC B hB
  rw [covariance_eq_covarianceMatrix hX] at hc
  exact noncentered_variance_of_centered_bound hX B hBs
    (centered_quadratic_memLp_of_logconcave_posDef hl hC B) hc

end GaussianTilt.Reference
