import Mathlib

/-! # Euclidean operator norm and trace of positive semidefinite matrices -/

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace GaussianTilt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagonal_opNorm_le {d : ι → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ i, |d i| ≤ C) : ‖Matrix.diagonal d‖ ≤ C := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  change ‖WithLp.ofLp (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (Matrix.diagonal d) x) i‖ ^ 2 ≤ _
  rw [Matrix.ofLp_toEuclideanCLM]
  simp only [Matrix.mulVec_diagonal, PiLp.ofLp_apply]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hd i) 2) (sq_nonneg _)

lemma posSemidef_opNorm_le_trace {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    ‖A‖ ≤ Matrix.trace A := by
  have hspec := hA.isHermitian.spectral_theorem
  calc
    ‖A‖ = ‖Matrix.diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues)‖ := by
      conv_lhs => rw [hspec]
      rw [CStarRing.norm_mul_mem_unitary _ (unitary.star_mem _),
        CStarRing.norm_coe_unitary_mul]
      exact hA.isHermitian.eigenvectorUnitary.prop
    _ ≤ Matrix.trace A := by
      apply diagonal_opNorm_le hA.trace_nonneg
      intro i
      change |hA.isHermitian.eigenvalues i| ≤ Matrix.trace A
      rw [abs_of_nonneg (hA.eigenvalues_nonneg i)]
      rw [hA.isHermitian.trace_eq_sum_eigenvalues]
      change hA.isHermitian.eigenvalues i ≤ ∑ j, hA.isHermitian.eigenvalues j
      exact Finset.single_le_sum (fun j _ ↦ hA.eigenvalues_nonneg j) (Finset.mem_univ i)
end GaussianTilt
