import GaussianTilt.LetwinIntegration

/-! # Integral vector Cauchy–Schwarz for the Stein coupling -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianTilt.Letwin

/-- Cauchy–Schwarz for a finite vector of actual square-integrable functions.
The proof integrates a nonnegative square and uses its discriminant. -/
theorem integral_sum_mul_sq_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {a b : ι → Ω → ℝ}
    (ha : ∀ i, MemLp (a i) 2 μ) (hb : ∀ i, MemLp (b i) 2 μ) :
    (∫ x, ∑ i, a i x * b i x ∂μ) ^ 2 ≤
      (∫ x, ∑ i, (a i x) ^ 2 ∂μ) * (∫ x, ∑ i, (b i x) ^ 2 ∂μ) := by
  let A := ∫ x, ∑ i, (a i x) ^ 2 ∂μ
  let B := ∫ x, ∑ i, (b i x) ^ 2 ∂μ
  let C := ∫ x, ∑ i, a i x * b i x ∂μ
  have ha2 : Integrable (fun x => ∑ i, (a i x) ^ 2) μ :=
    integrable_finset_sum _ fun i _ => (ha i).integrable_sq
  have hb2 : Integrable (fun x => ∑ i, (b i x) ^ 2) μ :=
    integrable_finset_sum _ fun i _ => (hb i).integrable_sq
  have hab : Integrable (fun x => ∑ i, a i x * b i x) μ :=
    integrable_finset_sum _ fun i _ => (ha i).integrable_mul (hb i)
  have hp : ∀ t : ℝ, 0 ≤ B * (t * t) + (-2 * C) * t + A := by
    intro t
    have hnonneg : 0 ≤ ∫ x, ∑ i, (a i x - t * b i x) ^ 2 ∂μ :=
      integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
    have heq : (fun x => ∑ i, (a i x - t * b i x) ^ 2) =
        (fun x => (∑ i, (a i x) ^ 2) - 2 * t * (∑ i, a i x * b i x) +
          t ^ 2 * (∑ i, (b i x) ^ 2)) := by
      funext x
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq] at hnonneg
    have hsplit := integral_add (ha2.sub (hab.const_mul (2 * t))) (hb2.const_mul (t ^ 2))
    simp only [Pi.sub_apply] at hsplit
    rw [hsplit, integral_sub ha2 (hab.const_mul (2 * t)),
      integral_const_mul, integral_const_mul] at hnonneg
    change 0 ≤ A - 2 * t * C + t ^ 2 * B at hnonneg
    nlinarith
  have h := discrim_le_zero hp
  dsimp [discrim] at h
  change C ^ 2 ≤ A * B
  nlinarith

end GaussianTilt.Letwin
