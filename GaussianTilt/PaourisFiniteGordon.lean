import GaussianTilt.PaourisSoftMinMax

/-!
# Finite Gaussian min/max comparison

This file applies the proved Gaussian covariance interpolation identity to
the actual soft-min/max Hessian. Increment variances are the squared norms of
the coefficient differences, computed from the specified linear images.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris

variable {d n k : ℕ}

/-- Squared coefficient difference, i.e. the increment variance of coordinates
of the specified standard Gaussian linear image. -/
def incrementVariance (A : Reference.Space d →L[ℝ] Reference.Space n) (i j : Fin n) : ℝ :=
  ∑ l : Fin d, ((A (coordinateVector l)) i - (A (coordinateVector l)) j) ^ 2

@[simp] lemma incrementVariance_self
    (A : Reference.Space d →L[ℝ] Reference.Space n) (i : Fin n) :
    incrementVariance A i i = 0 := by simp [incrementVariance]

/-- Cancellation of a bilinear form's diagonal covariance terms when its
coefficient matrix has zero row and column sums. -/
lemma matrix_increment_identity (H : Fin n → Fin n → ℝ)
    (hrow : ∀ i, ∑ j, H i j = 0) (hcol : ∀ j, ∑ i, H i j = 0)
    (u : Reference.Space n) :
    (∑ i, ∑ j, (u i - u j) ^ 2 * H i j) =
      -2 * ∑ i, ∑ j, u i * u j * H i j := by
  have h₁ : (∑ i, ∑ j, (u i) ^ 2 * H i j) = 0 := by
    simp_rw [← Finset.mul_sum, hrow, mul_zero]
    simp
  have h₂ : (∑ i, ∑ j, (u j) ^ 2 * H i j) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hcol, mul_zero]
    simp
  calc
    _ = ∑ i, ∑ j, ((u i) ^ 2 * H i j + (u j) ^ 2 * H i j -
        2 * (u i * u j * H i j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [h₁, h₂]
      simp_rw [← Finset.mul_sum]
      ring

lemma softMinMax_hessian_diagonal_increment [NeZero k]
    (row : Fin n → Fin k) (hrow : Function.Surjective row)
    {β : ℝ} (hβ : β ≠ 0) (x u : Reference.Space n) :
    fderiv ℝ (fderiv ℝ (softMinMax row β)) x u u =
      -(1 / 2 : ℝ) * ∑ i, ∑ j, (u i - u j) ^ 2 * softMinMaxHessian row β x i j := by
  have h := matrix_increment_identity (softMinMaxHessian row β x)
    (softMinMaxHessian_sum_row row hrow β x)
    (softMinMaxHessian_sum_column row hrow β x) u
  rw [bilinearForm_apply_eq_sum_coordinates]
  simp_rw [softMinMax_hessian_coordinate row hrow hβ,
    softMinMaxHessian_symm row β x]
  linarith

/-- Exact conversion from Hessian/covariance contraction to increment variances. -/
theorem softMinMax_covariance_contraction [NeZero k]
    (row : Fin n → Fin k) (hrow : Function.Surjective row)
    {β : ℝ} (hβ : β ≠ 0) (x : Reference.Space n)
    (A B : Reference.Space d →L[ℝ] Reference.Space n) :
    (∑ l : Fin d,
      (fderiv ℝ (fderiv ℝ (softMinMax row β)) x (A (coordinateVector l)) (A (coordinateVector l)) -
       fderiv ℝ (fderiv ℝ (softMinMax row β)) x (B (coordinateVector l)) (B (coordinateVector l)))) =
      -(1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
        (incrementVariance A i j - incrementVariance B i j) * softMinMaxHessian row β x i j := by
  simp_rw [softMinMax_hessian_diagonal_increment row hrow hβ]
  simp_rw [← mul_sub, ← Finset.mul_sum]
  congr 1
  simp_rw [← Finset.sum_sub_distrib]
  have hpoint (l : Fin d) (i j : Fin n) :
      ((A (coordinateVector l)) i - (A (coordinateVector l)) j) ^ 2 * softMinMaxHessian row β x i j -
        ((B (coordinateVector l)) i - (B (coordinateVector l)) j) ^ 2 * softMinMaxHessian row β x i j =
      (((A (coordinateVector l)) i - (A (coordinateVector l)) j) ^ 2 -
        ((B (coordinateVector l)) i - (B (coordinateVector l)) j) ^ 2) * softMinMaxHessian row β x i j := by ring
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul, Finset.sum_sub_distrib]
  rfl

/-- Finite Gordon comparison for the smooth min/max approximation. The
within-row and cross-row hypotheses concern the actual coefficient
increment variances and imply the comparison; no Gaussian comparison is
assumed. -/
theorem softMinMax_gaussian_comparison [NeZero k]
    (row : Fin n → Fin k) (hrow : Function.Surjective row) {β : ℝ} (hβ : 0 < β)
    (A B : Reference.Space d →L[ℝ] Reference.Space n)
    (hsep : ∀ l : Fin d, A (coordinateVector l) = 0 ∨ B (coordinateVector l) = 0)
    (hwithin : ∀ i j, row i = row j → incrementVariance A i j ≤ incrementVariance B i j)
    (hcross : ∀ i j, row i ≠ row j → incrementVariance B i j ≤ incrementVariance A i j) :
    gaussianExpectation (softMinMax row β) A ≤ gaussianExpectation (softMinMax row β) B := by
  apply gaussian_smooth_comparison ((softMinMax_contDiff row hrow β).of_le (by simp))
    (softMinMax_lipschitz row hrow hβ.ne')
    (H := ⟨4 * β * (n : ℝ) ^ 2, by positivity⟩)
    (fun x ↦ softMinMax_hessian_norm_le row hrow hβ x) B A
    (fun l ↦ (hsep l).symm)
  intro x
  change 0 ≤ ∑ l : Fin d,
    (fderiv ℝ (fderiv ℝ (softMinMax row β)) x (B (coordinateVector l)) (B (coordinateVector l)) -
      fderiv ℝ (fderiv ℝ (softMinMax row β)) x (A (coordinateVector l)) (A (coordinateVector l)))
  rw [softMinMax_covariance_contraction row hrow hβ.ne']
  apply mul_nonneg_of_nonpos_of_nonpos (by norm_num)
  apply Finset.sum_nonpos
  intro i _
  apply Finset.sum_nonpos
  intro j _
  by_cases hij : i = j
  · subst j
    simp
  · by_cases hr : row i = row j
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hwithin i j hr))
        (softMinMax_hessian_same_row_nonpos row hrow hβ.le x hij hr)
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hcross i j hr))
        (softMinMax_hessian_cross_row_nonneg row hrow hβ.le x hr)

lemma row_fiber_nonempty (row : Fin n → Fin k) (hrow : Function.Surjective row) (i : Fin k) :
    (Finset.univ.filter (fun j ↦ row j = i)).Nonempty := by
  obtain ⟨j, hj⟩ := hrow i
  exact ⟨j, by simp [hj]⟩

/-- Exact maximum of the coordinates belonging to a row. -/
def rowMaximum (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (x : Reference.Space n) (i : Fin k) : ℝ :=
  (Finset.univ.filter (fun j ↦ row j = i)).sup' (row_fiber_nonempty row hrow i) (fun j ↦ x j)

/-- The original finite min/max observable. -/
def finiteMinMax [NeZero k] (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (x : Reference.Space n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (rowMaximum row hrow x)

lemma coordinate_le_rowMaximum (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (x : Reference.Space n) (j : Fin n) : x j ≤ rowMaximum row hrow x (row j) :=
  Finset.le_sup' (fun j ↦ x j) (by simp)

lemma rowMaximum_attained (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (x : Reference.Space n) (i : Fin k) :
    ∃ j, row j = i ∧ rowMaximum row hrow x i = x j := by
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' (row_fiber_nonempty row hrow i) (fun j ↦ x j)
  exact ⟨j, (Finset.mem_filter.mp hj).2, heq⟩

lemma finiteMinMax_le_row [NeZero k] (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (x : Reference.Space n) (i : Fin k) : finiteMinMax row hrow x ≤ rowMaximum row hrow x i :=
  Finset.inf'_le _ (Finset.mem_univ _)

lemma finiteMinMax_attained [NeZero k] (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (x : Reference.Space n) : ∃ i, finiteMinMax row hrow x = rowMaximum row hrow x i := by
  obtain ⟨i, _, heq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (rowMaximum row hrow x)
  exact ⟨i, heq⟩

lemma rowMaximum_le_add (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (x y : Reference.Space n) (ε : ℝ) (hxy : ∀ j, x j ≤ y j + ε) (i : Fin k) :
    rowMaximum row hrow x i ≤ rowMaximum row hrow y i + ε := by
  apply Finset.sup'_le
  intro j hj
  have hji := (Finset.mem_filter.mp hj).2
  have h := coordinate_le_rowMaximum row hrow y j
  rw [hji] at h
  linarith [hxy j]

lemma finiteMinMax_le_add [NeZero k] (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (x y : Reference.Space n) (ε : ℝ) (hxy : ∀ j, x j ≤ y j + ε) :
    finiteMinMax row hrow x ≤ finiteMinMax row hrow y + ε := by
  obtain ⟨i, hi⟩ := finiteMinMax_attained row hrow y
  have h := rowMaximum_le_add row hrow x y ε hxy i
  have h' := finiteMinMax_le_row row hrow x i
  linarith

/-- Finite min/max is globally 1-Lipschitz, hence Gaussian integrable. -/
theorem finiteMinMax_lipschitz [NeZero k] (row : Fin n → Fin k)
    (hrow : Function.Surjective row) : LipschitzWith 1 (finiteMinMax row hrow) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  rw [NNReal.coe_one, one_mul, Real.norm_eq_abs]
  have hxy : ∀ j, x j ≤ y j + ‖x - y‖ := by
    intro j
    have h := PiLp.norm_apply_le (x - y) j
    simp only [PiLp.sub_apply, Real.norm_eq_abs] at h
    have hh := le_abs_self (x j - y j)
    linarith
  have hyx : ∀ j, y j ≤ x j + ‖x - y‖ := by
    intro j
    have h := PiLp.norm_apply_le (x - y) j
    simp only [PiLp.sub_apply, Real.norm_eq_abs] at h
    have hh := neg_le_abs (x j - y j)
    linarith
  exact abs_le.mpr ⟨by linarith [finiteMinMax_le_add row hrow y x _ hyx],
    by linarith [finiteMinMax_le_add row hrow x y _ hxy]⟩

lemma dimension_pos_of_surjective_rows [NeZero k] (row : Fin n → Fin k)
    (hrow : Function.Surjective row) : 0 < n := by
  obtain ⟨j, _⟩ := hrow ⟨0, NeZero.pos k⟩
  exact lt_of_le_of_lt (Nat.zero_le j.val) j.isLt

lemma rowExpSum_ge_exp_max (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) (x : Reference.Space n) (i : Fin k) :
    Real.exp (β * rowMaximum row hrow x i) ≤ rowExpSum row β x i := by
  obtain ⟨j, hj, hmax⟩ := rowMaximum_attained row hrow x i
  rw [hmax]
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun l : Fin n ↦ if row l = i then Real.exp (β * x l) else 0)
    (fun l _ ↦ by dsimp; split_ifs <;> positivity) (Finset.mem_univ j)
  simpa only [rowExpSum, if_pos hj] using h

lemma rowExpSum_le_card_exp_max (row : Fin n → Fin k) (hrow : Function.Surjective row)
    {β : ℝ} (hβ : 0 ≤ β) (x : Reference.Space n) (i : Fin k) :
    rowExpSum row β x i ≤ (n : ℝ) * Real.exp (β * rowMaximum row hrow x i) := by
  calc
    _ ≤ ∑ _j : Fin n, Real.exp (β * rowMaximum row hrow x i) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : row j = i
      · rw [if_pos hj]
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hβ
        simpa only [hj] using coordinate_le_rowMaximum row hrow x j
      · rw [if_neg hj]
        positivity
    _ = _ := by simp

/-- Uniform lower error bound for the soft min/max approximation. -/
theorem softMinMax_lower_approx [NeZero k] (row : Fin n → Fin k)
    (hrow : Function.Surjective row) {β : ℝ} (hβ : 0 < β) (x : Reference.Space n) :
    finiteMinMax row hrow x - Real.log (k : ℝ) / β ≤ softMinMax row β x := by
  have hk : (0 : ℝ) < k := by exact_mod_cast NeZero.pos k
  have hu : inverseRowSum row β x ≤ (k : ℝ) * Real.exp (-β * finiteMinMax row hrow x) := by
    calc
      _ ≤ ∑ _i : Fin k, Real.exp (-β * finiteMinMax row hrow x) := by
        apply Finset.sum_le_sum
        intro i _
        have hmax : Real.exp (β * finiteMinMax row hrow x) ≤ rowExpSum row β x i :=
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (finiteMinMax_le_row row hrow x i)
            hβ.le)).trans (rowExpSum_ge_exp_max row hrow β x i)
        rw [neg_mul, Real.exp_neg]
        exact (inv_le_inv₀ (rowExpSum_pos row hrow β x i) (Real.exp_pos _)).mpr hmax
      _ = _ := by simp
  have hl := Real.log_le_log (inverseRowSum_pos row hrow β x) hu
  rw [Real.log_mul hk.ne' (Real.exp_ne_zero _), Real.log_exp] at hl
  have hm := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hβ.le)
  unfold softMinMax
  field_simp at hm ⊢
  nlinarith

/-- Uniform upper error bound for the soft min/max approximation. -/
theorem softMinMax_upper_approx [NeZero k] (row : Fin n → Fin k)
    (hrow : Function.Surjective row) {β : ℝ} (hβ : 0 < β) (x : Reference.Space n) :
    softMinMax row β x ≤ finiteMinMax row hrow x + Real.log (n : ℝ) / β := by
  have hn : (0 : ℝ) < n := by exact_mod_cast dimension_pos_of_surjective_rows row hrow
  obtain ⟨i, hi⟩ := finiteMinMax_attained row hrow x
  have hS := rowExpSum_le_card_exp_max row hrow hβ.le x i
  rw [← hi] at hS
  have hlower : ((n : ℝ) * Real.exp (β * finiteMinMax row hrow x))⁻¹ ≤ inverseRowSum row β x := by
    have h := (inv_le_inv₀ (mul_pos hn (Real.exp_pos _)) (rowExpSum_pos row hrow β x i)).mpr hS
    exact h.trans (Finset.single_le_sum (fun j _ ↦ (inv_pos.mpr
      (rowExpSum_pos row hrow β x j)).le) (Finset.mem_univ i))
  have hl := Real.log_le_log (inv_pos.mpr (mul_pos hn (Real.exp_pos _))) hlower
  rw [Real.log_inv, Real.log_mul hn.ne' (Real.exp_ne_zero _), Real.log_exp] at hl
  have hm := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hβ.le)
  unfold softMinMax
  field_simp at hm ⊢
  nlinarith

/-- Passage to zero smoothing error, with no exchange of a limit and an
integral required because the approximation error is uniform. -/
lemma le_of_uniform_div_error {a b c : ℝ} (hc : 0 ≤ c)
    (h : ∀ β : ℝ, 0 < β → a ≤ b + c / β) : a ≤ b := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let β := (c + 1) / ε
  have hβ : 0 < β := div_pos (by linarith) hε
  have herr : c / β ≤ ε := by
    apply (div_le_iff₀ hβ).mpr
    dsimp [β]
    field_simp
    linarith
  exact (h β hβ).trans (add_le_add_left herr b)

/-- The finite Gordon min/max comparison theorem for actual standard
Gaussian linear images with independent column blocks. The conclusion is
about the exact finite minimum of row maxima, not its smooth surrogate. -/
theorem finite_gordon_comparison [NeZero k]
    (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (A B : Reference.Space d →L[ℝ] Reference.Space n)
    (hsep : ∀ l : Fin d, A (coordinateVector l) = 0 ∨ B (coordinateVector l) = 0)
    (hwithin : ∀ i j, row i = row j → incrementVariance A i j ≤ incrementVariance B i j)
    (hcross : ∀ i j, row i ≠ row j → incrementVariance B i j ≤ incrementVariance A i j) :
    gaussianExpectation (finiteMinMax row hrow) A ≤
      gaussianExpectation (finiteMinMax row hrow) B := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast dimension_pos_of_surjective_rows row hrow
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast NeZero.pos k
  apply le_of_uniform_div_error
    (c := Real.log (n : ℝ) + Real.log (k : ℝ))
    (add_nonneg (Real.log_nonneg hn) (Real.log_nonneg hk))
  intro β hβ
  have hA := gaussian_linear_image_integrable (finiteMinMax_lipschitz row hrow) A
  have hB := gaussian_linear_image_integrable (finiteMinMax_lipschitz row hrow) B
  have hsA := gaussian_linear_image_integrable (softMinMax_lipschitz row hrow hβ.ne') A
  have hsB := gaussian_linear_image_integrable (softMinMax_lipschitz row hrow hβ.ne') B
  have hlow := integral_mono (hA.sub (integrable_const (Real.log (k : ℝ) / β))) hsA
    (fun x ↦ softMinMax_lower_approx row hrow hβ (A x))
  have hupp := integral_mono hsB (hB.add (integrable_const (Real.log (n : ℝ) / β)))
    (fun x ↦ softMinMax_upper_approx row hrow hβ (B x))
  simp only [Pi.sub_apply, Pi.add_apply] at hlow hupp
  rw [integral_sub hA (integrable_const _)] at hlow
  rw [integral_add hB (integrable_const _)] at hupp
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hlow hupp
  have hcomp := softMinMax_gaussian_comparison row hrow hβ A B hsep hwithin hcross
  dsimp [gaussianExpectation] at hcomp ⊢
  rw [add_div]
  linarith

end GaussianTilt.Paouris
