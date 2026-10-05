import GaussianTilt.Quadratic

/-! # Cauchy--Schwarz for covariance, with all moment conditions explicit -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace GaussianTilt
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma covariance_sq_le_variance_mul {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (ProbabilityTheory.covariance f g μ) ^ 2 ≤
      ProbabilityTheory.variance f μ * ProbabilityTheory.variance g μ := by
  have h (c : ℝ) : 0 ≤ ProbabilityTheory.variance f μ * (c * c) +
      (2 * ProbabilityTheory.covariance f g μ) * c + ProbabilityTheory.variance g μ := by
    have hv := variance_nonneg (fun ω ↦ c * f ω + g ω) μ
    rw [variance_fun_add (hf.const_mul c) hg, variance_mul, covariance_mul_left] at hv
    nlinarith
  have hd := discrim_le_zero h
  dsimp [discrim] at hd
  nlinarith

lemma abs_covariance_le_of_variance_bounds {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfA : ProbabilityTheory.variance f μ ≤ A ^ 2)
    (hgB : ProbabilityTheory.variance g μ ≤ B ^ 2) :
    |ProbabilityTheory.covariance f g μ| ≤ A * B := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA hB)).mp
  rw [sq_abs, mul_pow]
  exact (covariance_sq_le_variance_mul hf hg).trans
    (mul_le_mul hfA hgB (variance_nonneg g μ) (sq_nonneg A))

end GaussianTilt
