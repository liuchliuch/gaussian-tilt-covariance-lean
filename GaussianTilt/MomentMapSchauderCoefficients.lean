import GaussianTilt.MomentMapSchauderLinearization

/-!
# Quantitative bounds for the genuine elliptic linearization coefficient

The inverse difference identity gives explicit entrywise Hölder control.
This is proved for actual matrix inverses and their interval integrals.
-/
noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Quantitative inverse continuity, with a dimension-explicit constant.
All bounds are literal entrywise bounds, so no unproved norm equivalence
or elliptic estimate is hidden in the statement. -/
lemma abs_inv_entry_sub_le {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hAi : ∀ i j, |A⁻¹ i j| ≤ M) (hBi : ∀ i j, |B⁻¹ i j| ≤ M)
    (hAB : ∀ i j, |A i j - B i j| ≤ D) (i j : ι) :
    |A⁻¹ i j - B⁻¹ i j| ≤ (Fintype.card ι : ℝ) ^ 2 * M ^ 2 * D := by
  have he := Matrix.inv_sub_inv (A := A) (B := B) (iff_of_true hA.isUnit hB.isUnit)
  have heij := congrArg (fun C : Matrix ι ι ℝ => C i j) he
  simp only [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_mul] at heij
  rw [heij]
  calc
    |∑ k, ∑ l, A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| ≤
        ∑ k, ∑ l, |A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _k : ι, ∑ _l : ι, M * D * M := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      simp only [abs_mul]
      apply mul_le_mul (mul_le_mul (hAi i l) ?_ (abs_nonneg _) hM) (hBi k j)
        (abs_nonneg _) (mul_nonneg hM hD)
      simpa only [abs_sub_comm] using hAB l k
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Taking a convex matrix segment preserves a common entry-difference
bound at its two endpoints. -/
lemma abs_matrixSegment_entry_sub_le {A B C D : Matrix ι ι ℝ} {H : ℝ}
    (hAC : ∀ i j, |A i j - C i j| ≤ H)
    (hBD : ∀ i j, |B i j - D i j| ≤ H)
    {t : ℝ} (ht : t ∈ Icc 0 1) (i j : ι) :
    |matrixSegment A B t i j - matrixSegment C D t i j| ≤ H := by
  have h1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  calc
    _ = |(1 - t) * (A i j - C i j) + t * (B i j - D i j)| := by
      simp only [matrixSegment, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      congr 1
      ring
    _ ≤ |(1 - t) * (A i j - C i j)| + |t * (B i j - D i j)| := abs_add_le _ _
    _ = (1 - t) * |A i j - C i j| + t * |B i j - D i j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg ht.1]
    _ ≤ (1 - t) * H + t * H := add_le_add
      (mul_le_mul_of_nonneg_left (hAC i j) h1) (mul_le_mul_of_nonneg_left (hBD i j) ht.1)
    _ = H := by ring

/-- Hölder moduli of the Hessian endpoints transfer to the exact averaged
inverse coefficient, with no smoothness assumptions beyond those displayed. -/
theorem abs_averagedInverse_entry_sub_le {A B C D : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
    {M H : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hiAB : ∀ t ∈ Icc 0 1, ∀ i j, |(matrixSegment A B t)⁻¹ i j| ≤ M)
    (hiCD : ∀ t ∈ Icc 0 1, ∀ i j, |(matrixSegment C D t)⁻¹ i j| ≤ M)
    (hAC : ∀ i j, |A i j - C i j| ≤ H)
    (hBD : ∀ i j, |B i j - D i j| ≤ H) (i j : ι) :
    |averagedInverse A B i j - averagedInverse C D i j| ≤
      (Fintype.card ι : ℝ) ^ 2 * M ^ 2 * H := by
  simp only [averagedInverse]
  rw [← intervalIntegral.integral_sub (intervalIntegrable_inv_matrixSegment hA hB i j)
    (intervalIntegrable_inv_matrixSegment hC hD i j)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (C := (Fintype.card ι : ℝ) ^ 2 * M ^ 2 * H)
    (f := fun t => (matrixSegment A B t)⁻¹ i j - (matrixSegment C D t)⁻¹ i j) ?_
  · simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hb
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)
    simpa only [Real.norm_eq_abs] using abs_inv_entry_sub_le
      (matrixSegment_posDef hA hB ht') (matrixSegment_posDef hC hD ht') hM hH
      (hiAB t ht') (hiCD t ht') (abs_matrixSegment_entry_sub_le hAC hBD ht') i j

end GaussianTilt.MomentMapSchauder
