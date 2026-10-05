import GaussianTilt.PaourisInterpolation

/-!
# Finite soft-min/max functions for Gaussian comparison

Rows are encoded by a surjective partition of the finite coordinate index.
The smooth function is `-β⁻¹ log (∑ rows (∑ row exp (β x))⁻¹)`.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris

variable {n k : ℕ}

/-- Exponential sum in one row of the finite min/max array. -/
def rowExpSum (row : Fin n → Fin k) (β : ℝ) (x : Reference.Space n) (i : Fin k) : ℝ :=
  ∑ j : Fin n, if row j = i then Real.exp (β * x j) else 0

def inverseRowSum (row : Fin n → Fin k) (β : ℝ) (x : Reference.Space n) : ℝ :=
  ∑ i : Fin k, (rowExpSum row β x i)⁻¹

/-- Smooth approximation of the minimum over rows of the maximum in a row. -/
def softMinMax (row : Fin n → Fin k) (β : ℝ) (x : Reference.Space n) : ℝ :=
  -β⁻¹ * Real.log (inverseRowSum row β x)

def rowWeight (row : Fin n → Fin k) (β : ℝ) (x : Reference.Space n) (i : Fin k) : ℝ :=
  (rowExpSum row β x i)⁻¹ / inverseRowSum row β x

def withinRowWeight (row : Fin n → Fin k) (β : ℝ) (x : Reference.Space n) (j : Fin n) : ℝ :=
  Real.exp (β * x j) / rowExpSum row β x (row j)

def softMinMaxWeight (row : Fin n → Fin k) (β : ℝ) (x : Reference.Space n) (j : Fin n) : ℝ :=
  rowWeight row β x (row j) * withinRowWeight row β x j

lemma rowExpSum_pos (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) (x : Reference.Space n) (i : Fin k) : 0 < rowExpSum row β x i := by
  obtain ⟨j, hj⟩ := hrow i
  unfold rowExpSum
  apply Finset.sum_pos'
  · intro l _
    split_ifs <;> positivity
  · exact ⟨j, Finset.mem_univ _, by rw [if_pos hj]; exact Real.exp_pos _⟩

lemma inverseRowSum_pos [NeZero k] (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) (x : Reference.Space n) : 0 < inverseRowSum row β x := by
  exact Finset.sum_pos (fun i _ ↦ inv_pos.mpr (rowExpSum_pos row hrow β x i)) Finset.univ_nonempty

lemma rowWeight_pos [NeZero k] (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) (x : Reference.Space n) (i : Fin k) : 0 < rowWeight row β x i :=
  div_pos (inv_pos.mpr (rowExpSum_pos row hrow β x i)) (inverseRowSum_pos row hrow β x)

lemma withinRowWeight_pos (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) (x : Reference.Space n) (j : Fin n) : 0 < withinRowWeight row β x j :=
  div_pos (Real.exp_pos _) (rowExpSum_pos row hrow β x _)

lemma softMinMaxWeight_pos [NeZero k] (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) (x : Reference.Space n) (j : Fin n) : 0 < softMinMaxWeight row β x j :=
  mul_pos (rowWeight_pos row hrow β x _) (withinRowWeight_pos row hrow β x j)

lemma sum_rowWeight [NeZero k] (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) (x : Reference.Space n) : (∑ i, rowWeight row β x i) = 1 := by
  unfold rowWeight
  rw [← Finset.sum_div]
  exact div_self (inverseRowSum_pos row hrow β x).ne'

lemma sum_withinRowWeight (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) (x : Reference.Space n) (i : Fin k) :
    (∑ j, if row j = i then withinRowWeight row β x j else 0) = 1 := by
  have heq : (fun j ↦ if row j = i then withinRowWeight row β x j else 0) =
      (fun j ↦ (if row j = i then Real.exp (β * x j) else 0) / rowExpSum row β x i) := by
    ext j
    by_cases hj : row j = i <;> simp [hj, withinRowWeight]
  rw [heq, ← Finset.sum_div]
  exact div_self (rowExpSum_pos row hrow β x i).ne'

lemma sum_softMinMaxWeight [NeZero k] (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) (x : Reference.Space n) : (∑ j, softMinMaxWeight row β x j) = 1 := by
  have hgroup : (∑ j, softMinMaxWeight row β x j) =
      ∑ i : Fin k, ∑ j : Fin n, if row j = i then softMinMaxWeight row β x j else 0 := by
    rw [Finset.sum_comm]
    simp
  rw [hgroup]
  have hrowSum (i : Fin k) :
      (∑ j : Fin n, if row j = i then softMinMaxWeight row β x j else 0) = rowWeight row β x i := by
    have heq : (fun j ↦ if row j = i then softMinMaxWeight row β x j else 0) =
        (fun j ↦ rowWeight row β x i * (if row j = i then withinRowWeight row β x j else 0)) := by
      ext j
      by_cases hj : row j = i <;> simp [hj, softMinMaxWeight]
    rw [heq, ← Finset.mul_sum, sum_withinRowWeight row hrow β x i, mul_one]
  simp_rw [hrowSum]
  exact sum_rowWeight row hrow β x

lemma rowWeight_le_one [NeZero k] (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) (x : Reference.Space n) (i : Fin k) : rowWeight row β x i ≤ 1 := by
  rw [← sum_rowWeight row hrow β x]
  exact Finset.single_le_sum (fun j _ ↦ (rowWeight_pos row hrow β x j).le) (Finset.mem_univ _)

lemma withinRowWeight_le_one (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) (x : Reference.Space n) (j : Fin n) : withinRowWeight row β x j ≤ 1 := by
  unfold withinRowWeight
  apply (div_le_one (rowExpSum_pos row hrow β x _)).mpr
  unfold rowExpSum
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun l : Fin n ↦ if row l = row j then Real.exp (β * x l) else 0)
    (fun l _ ↦ by dsimp; split_ifs <;> positivity) (Finset.mem_univ j)
  simpa only [if_pos rfl] using h

lemma softMinMaxWeight_le_one [NeZero k] (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) (x : Reference.Space n) (j : Fin n) : softMinMaxWeight row β x j ≤ 1 := by
  rw [← sum_softMinMaxWeight row hrow β x]
  exact Finset.single_le_sum (fun l _ ↦ (softMinMaxWeight_pos row hrow β x l).le) (Finset.mem_univ _)

/-- Coordinate direction in the fixed Euclidean basis. -/
def coordinateVector (j : Fin n) : Reference.Space n := (EuclideanSpace.basisFun (Fin n) ℝ) j

lemma coordinateVector_apply (j l : Fin n) : coordinateVector j l = if l = j then 1 else 0 := by
  simp [coordinateVector, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply]

lemma rowExpSum_contDiff (row : Fin n → Fin k) (β : ℝ) (i : Fin k) :
    ContDiff ℝ ⊤ (fun x : Reference.Space n ↦ rowExpSum row β x i) := by
  unfold rowExpSum
  apply ContDiff.sum
  intro j _
  by_cases hj : row j = i
  · simp only [if_pos hj]
    have hp : ContDiff ℝ ⊤ (fun y : Reference.Space n ↦ y j) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff
    exact (contDiff_const.mul hp).exp
  · simp only [if_neg hj]
    exact contDiff_const

lemma inverseRowSum_contDiff (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) : ContDiff ℝ ⊤ (inverseRowSum row β) := by
  unfold inverseRowSum
  apply ContDiff.sum
  intro i _
  exact (rowExpSum_contDiff row β i).inv (fun x ↦ (rowExpSum_pos row hrow β x i).ne')

lemma softMinMax_contDiff [NeZero k] (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) : ContDiff ℝ ⊤ (softMinMax row β) :=
  contDiff_const.mul ((inverseRowSum_contDiff row hrow β).log
    (fun x ↦ (inverseRowSum_pos row hrow β x).ne'))

lemma coordinateLine_hasDerivAt (x : Reference.Space n) (j : Fin n) :
    HasDerivAt (fun t : ℝ ↦ x + t • coordinateVector j) (coordinateVector j) 0 := by
  simpa only [one_smul] using
    ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector j)).const_add x

lemma coordinateLine_apply_hasDerivAt (x : Reference.Space n) (j l : Fin n) :
    HasDerivAt (fun t : ℝ ↦ (x + t • coordinateVector j) l) (if l = j then 1 else 0) 0 := by
  have h := (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) l).hasFDerivAt.comp_hasDerivAt 0
    (coordinateLine_hasDerivAt x j)
  simpa only [PiLp.proj_apply, coordinateVector_apply] using h

lemma rowExpSum_line_hasDerivAt (row : Fin n → Fin k) (β : ℝ)
    (x : Reference.Space n) (j : Fin n) (i : Fin k) :
    HasDerivAt (fun t : ℝ ↦ rowExpSum row β (x + t • coordinateVector j) i)
      (if row j = i then β * Real.exp (β * x j) else 0) 0 := by
  have hd (l : Fin n) : HasDerivAt
      (fun t : ℝ ↦ if row l = i then Real.exp (β * (x + t • coordinateVector j) l) else 0)
      (if l = j then (if row j = i then β * Real.exp (β * x j) else 0) else 0) 0 := by
    by_cases hl : l = j
    · subst l
      by_cases hi : row j = i
      · simp only [if_pos hi]
        convert ((coordinateLine_apply_hasDerivAt x j j).const_mul β).exp using 1 <;>
          simp [mul_comm]
      · simp only [if_neg hi]
        exact hasDerivAt_const _ _
    · by_cases hi : row l = i
      · simp only [if_pos hi, if_neg hl]
        convert ((coordinateLine_apply_hasDerivAt x j l).const_mul β).exp using 1 <;>
          simp [hl]
      · simp only [if_neg hi, if_neg hl]
        exact hasDerivAt_const _ _
  simpa only [rowExpSum, Finset.sum_ite_eq', Finset.mem_univ, if_true] using
    HasDerivAt.fun_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin n))) ↦ hd l)

lemma inverseRowSum_line_hasDerivAt (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) (x : Reference.Space n) (j : Fin n) :
    HasDerivAt (fun t : ℝ ↦ inverseRowSum row β (x + t • coordinateVector j))
      (-(β * Real.exp (β * x j)) / rowExpSum row β x (row j) ^ 2) 0 := by
  have hd (i : Fin k) := (rowExpSum_line_hasDerivAt row β x j i).inv
    (by simpa using (rowExpSum_pos row hrow β x i).ne')
  have heq (i : Fin k) :
      -(if row j = i then β * Real.exp (β * x j) else 0) /
        rowExpSum row β (x + (0 : ℝ) • coordinateVector j) i ^ 2 =
      if i = row j then -(β * Real.exp (β * x j)) / rowExpSum row β x (row j) ^ 2 else 0 := by
    by_cases hi : i = row j <;> simp [hi, eq_comm]
  have h := HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) ↦ hd i)
  simp_rw [heq] at h
  simpa only [inverseRowSum, Pi.inv_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

lemma softMinMax_line_hasDerivAt [NeZero k] (row : Fin n → Fin k) (hrow : Function.Surjective row)
    {β : ℝ} (hβ : β ≠ 0) (x : Reference.Space n) (j : Fin n) :
    HasDerivAt (fun t : ℝ ↦ softMinMax row β (x + t • coordinateVector j))
      (softMinMaxWeight row β x j) 0 := by
  have h := ((inverseRowSum_line_hasDerivAt row hrow β x j).log
    (by simpa using (inverseRowSum_pos row hrow β x).ne')).const_mul (-β⁻¹)
  convert h using 1
  have hS := (rowExpSum_pos row hrow β x (row j)).ne'
  have hZ := (inverseRowSum_pos row hrow β x).ne'
  simp only [softMinMaxWeight, rowWeight, withinRowWeight, zero_smul, add_zero]
  field_simp

/-- Coordinate derivative of the actual smooth min/max function. -/
theorem softMinMax_fderiv_coordinate [NeZero k] (row : Fin n → Fin k)
    (hrow : Function.Surjective row) {β : ℝ} (hβ : β ≠ 0)
    (x : Reference.Space n) (j : Fin n) :
    fderiv ℝ (softMinMax row β) x (coordinateVector j) = softMinMaxWeight row β x j := by
  have hdiff : Differentiable ℝ (softMinMax row β) :=
    (softMinMax_contDiff row hrow β).differentiable (by simp)
  have hd := (hdiff (x + (0 : ℝ) • coordinateVector j)).hasFDerivAt.comp_hasDerivAt 0
    (coordinateLine_hasDerivAt x j)
  have hline := softMinMax_line_hasDerivAt row hrow hβ x j
  simp only [zero_smul, add_zero, Function.comp_apply] at hd
  exact hd.unique hline

lemma softMinMaxWeight_eq (row : Fin n → Fin k) (β : ℝ) (x : Reference.Space n) (i : Fin n) :
    softMinMaxWeight row β x i =
      Real.exp (β * x i) / (rowExpSum row β x (row i) ^ 2 * inverseRowSum row β x) := by
  unfold softMinMaxWeight rowWeight withinRowWeight
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

lemma softMinMaxWeight_contDiff [NeZero k] (row : Fin n → Fin k) (hrow : Function.Surjective row)
    (β : ℝ) (i : Fin n) : ContDiff ℝ ⊤ (fun x ↦ softMinMaxWeight row β x i) := by
  simp_rw [softMinMaxWeight_eq, div_eq_mul_inv]
  have hp : ContDiff ℝ ⊤ (fun x : Reference.Space n ↦ Real.exp (β * x i)) :=
    (contDiff_const.mul (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).contDiff).exp
  exact hp.mul (((rowExpSum_contDiff row β (row i)).pow 2).mul
    (inverseRowSum_contDiff row hrow β) |>.inv fun x ↦
      mul_ne_zero (pow_ne_zero _ (rowExpSum_pos row hrow β x _).ne')
        (inverseRowSum_pos row hrow β x).ne')

/-- Explicit mixed derivative of the soft min/max function. -/
def softMinMaxHessian (row : Fin n → Fin k) (β : ℝ) (x : Reference.Space n) (i j : Fin n) : ℝ :=
  β * softMinMaxWeight row β x i *
    ((if i = j then 1 else 0) -
      (if row i = row j then 2 * withinRowWeight row β x j else 0) +
        softMinMaxWeight row β x j)

lemma softMinMaxWeight_line_hasDerivAt [NeZero k] (row : Fin n → Fin k)
    (hrow : Function.Surjective row) (β : ℝ) (x : Reference.Space n) (i j : Fin n) :
    HasDerivAt (fun t : ℝ ↦ softMinMaxWeight row β (x + t • coordinateVector j) i)
      (softMinMaxHessian row β x i j) 0 := by
  have hE : HasDerivAt (fun t : ℝ ↦ Real.exp (β * (x + t • coordinateVector j) i))
      (β * Real.exp (β * x i) * (if i = j then 1 else 0)) 0 := by
    convert ((coordinateLine_apply_hasDerivAt x j i).const_mul β).exp using 1
    simp only [zero_smul, add_zero]
    ring
  have hS := rowExpSum_line_hasDerivAt row β x j (row i)
  have hZ := inverseRowSum_line_hasDerivAt row hrow β x j
  have hden : rowExpSum row β (x + (0 : ℝ) • coordinateVector j) (row i) ^ 2 *
      inverseRowSum row β (x + (0 : ℝ) • coordinateVector j) ≠ 0 := by
    simpa using mul_ne_zero (pow_ne_zero 2 (rowExpSum_pos row hrow β x _).ne')
      (inverseRowSum_pos row hrow β x).ne'
  have hd := hE.div ((hS.pow 2).mul hZ) hden
  simp_rw [softMinMaxWeight_eq]
  convert hd using 1
  have hi := (rowExpSum_pos row hrow β x (row i)).ne'
  have hj := (rowExpSum_pos row hrow β x (row j)).ne'
  have hz := (inverseRowSum_pos row hrow β x).ne'
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply, zero_smul, add_zero,
    softMinMaxHessian, softMinMaxWeight_eq, withinRowWeight, Nat.cast_ofNat,
    Nat.reduceSub, pow_one]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, ↓reduceIte]
    field_simp
    <;> ring
  · by_cases hrij : row i = row j
    · simp only [if_neg hij, hrij, ↓reduceIte]
      field_simp
      <;> ring
    · simp only [if_neg hij, if_neg hrij, if_neg (Ne.symm hrij)]
      field_simp
      <;> ring

/-- Hessian coefficients are proved to be the actual iterated Fréchet
partial derivatives, not supplied as a Hessian specification. -/
theorem softMinMax_hessian_coordinate [NeZero k] (row : Fin n → Fin k)
    (hrow : Function.Surjective row) {β : ℝ} (hβ : β ≠ 0)
    (x : Reference.Space n) (i j : Fin n) :
    fderiv ℝ (fderiv ℝ (softMinMax row β)) x (coordinateVector j) (coordinateVector i) =
      softMinMaxHessian row β x i j := by
  have hdf : Differentiable ℝ (fderiv ℝ (softMinMax row β)) :=
    ((softMinMax_contDiff row hrow β).fderiv_right (m := 1) (by simp)).differentiable le_rfl
  have hcomp := ((hdf x).hasFDerivAt.clm_apply (hasFDerivAt_const (coordinateVector i) x)).fderiv
  have hfun : (fun y ↦ fderiv ℝ (softMinMax row β) y (coordinateVector i)) =
      (fun y ↦ softMinMaxWeight row β y i) :=
    funext fun y ↦ softMinMax_fderiv_coordinate row hrow hβ y i
  rw [hfun] at hcomp
  have heval := congrArg (fun L ↦ L (coordinateVector j)) hcomp
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply] at heval
  have hdiff : Differentiable ℝ (fun y ↦ softMinMaxWeight row β y i) :=
    (softMinMaxWeight_contDiff row hrow β i).differentiable (by simp)
  have hd := (hdiff (x + (0 : ℝ) • coordinateVector j)).hasFDerivAt.comp_hasDerivAt 0
    (coordinateLine_hasDerivAt x j)
  simp only [zero_smul, add_zero] at hd
  exact heval.symm.trans (hd.unique (softMinMaxWeight_line_hasDerivAt row hrow β x i j))

/-- Cross-row mixed Hessian coefficients are nonnegative. -/
theorem softMinMax_hessian_cross_row_nonneg [NeZero k] (row : Fin n → Fin k)
    (hrow : Function.Surjective row) {β : ℝ} (hβ : 0 ≤ β)
    (x : Reference.Space n) {i j : Fin n} (hij : row i ≠ row j) :
    0 ≤ softMinMaxHessian row β x i j := by
  have hne : i ≠ j := fun h ↦ hij (congrArg row h)
  simp only [softMinMaxHessian, if_neg hne, if_neg hij, sub_self, zero_add]
  exact mul_nonneg (mul_nonneg hβ (softMinMaxWeight_pos row hrow β x i).le)
    (softMinMaxWeight_pos row hrow β x j).le

/-- Distinct coordinates within a row have nonpositive mixed Hessian. -/
theorem softMinMax_hessian_same_row_nonpos [NeZero k] (row : Fin n → Fin k)
    (hrow : Function.Surjective row) {β : ℝ} (hβ : 0 ≤ β)
    (x : Reference.Space n) {i j : Fin n} (hne : i ≠ j) (hij : row i = row j) :
    softMinMaxHessian row β x i j ≤ 0 := by
  have hp := rowWeight_le_one row hrow β x (row j)
  have hq := (withinRowWeight_pos row hrow β x j).le
  have hm := mul_le_mul_of_nonneg_right hp hq
  have hbracket : -(2 * withinRowWeight row β x j) + softMinMaxWeight row β x j ≤ 0 := by
    unfold softMinMaxWeight
    nlinarith
  simp only [softMinMaxHessian, if_neg hne, if_pos hij, zero_sub]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg hβ (softMinMaxWeight_pos row hrow β x i).le) hbracket

/-- Hessian rows sum to zero, expressing translation equivariance of min/max. -/
lemma softMinMaxHessian_sum_row [NeZero k] (row : Fin n → Fin k)
    (hrow : Function.Surjective row) (β : ℝ) (x : Reference.Space n) (i : Fin n) :
    (∑ j, softMinMaxHessian row β x i j) = 0 := by
  have hrowSum : (∑ j : Fin n, if row i = row j then 2 * withinRowWeight row β x j else 0) = 2 := by
    have h := sum_withinRowWeight row hrow β x (row i)
    calc
      _ = 2 * ∑ j : Fin n, if row j = row i then withinRowWeight row β x j else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : row i = row j <;> simp [hj, Ne.symm, eq_comm]
      _ = 2 := by rw [h]; ring
  simp only [softMinMaxHessian, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    hrowSum, sum_softMinMaxWeight row hrow β x]
  ring

lemma softMinMaxHessian_symm (row : Fin n → Fin k)
    (β : ℝ) (x : Reference.Space n) (i j : Fin n) :
    softMinMaxHessian row β x i j = softMinMaxHessian row β x j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · by_cases hr : row i = row j
    · simp only [softMinMaxHessian, if_neg hij, if_neg (Ne.symm hij),
        softMinMaxWeight, hr, ↓reduceIte]
      ring
    · simp only [softMinMaxHessian, if_neg hij, if_neg (Ne.symm hij),
        if_neg hr, if_neg (Ne.symm hr)]
      ring

lemma softMinMaxHessian_sum_column [NeZero k] (row : Fin n → Fin k)
    (hrow : Function.Surjective row) (β : ℝ) (x : Reference.Space n) (j : Fin n) :
    (∑ i, softMinMaxHessian row β x i j) = 0 := by
  simp_rw [softMinMaxHessian_symm row β x]
  exact softMinMaxHessian_sum_row row hrow β x j

lemma softMinMaxHessian_abs_le [NeZero k] (row : Fin n → Fin k)
    (hrow : Function.Surjective row) {β : ℝ} (hβ : 0 ≤ β)
    (x : Reference.Space n) (i j : Fin n) :
    |softMinMaxHessian row β x i j| ≤ 4 * β := by
  have hwi := (softMinMaxWeight_pos row hrow β x i).le
  have hwi' := softMinMaxWeight_le_one row hrow β x i
  have hwj := (softMinMaxWeight_pos row hrow β x j).le
  have hwj' := softMinMaxWeight_le_one row hrow β x j
  have hqj := (withinRowWeight_pos row hrow β x j).le
  have hqj' := withinRowWeight_le_one row hrow β x j
  have hδ : (if i = j then (1 : ℝ) else 0) ∈ Icc (0 : ℝ) 1 := by split_ifs <;> norm_num
  have hrowδ : (if row i = row j then 2 * withinRowWeight row β x j else 0) ∈ Icc (0 : ℝ) 2 := by
    split_ifs <;> constructor <;> linarith
  have hb : |(if i = j then (1 : ℝ) else 0) -
      (if row i = row j then 2 * withinRowWeight row β x j else 0) +
        softMinMaxWeight row β x j| ≤ 4 := by
    apply abs_le.mpr
    constructor <;> linarith [hδ.1, hδ.2, hrowδ.1, hrowδ.2]
  rw [softMinMaxHessian, abs_mul, abs_of_nonneg (mul_nonneg hβ hwi)]
  have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg hβ hwi)
  have hm' := mul_le_mul_of_nonneg_left hwi' hβ
  nlinarith

/-- Expansion of an actual continuous linear functional in Euclidean coordinates. -/
lemma linearForm_apply_eq_sum_coordinates (L : Reference.Space n →L[ℝ] ℝ)
    (v : Reference.Space n) : L v = ∑ i : Fin n, v i * L (coordinateVector i) := by
  have heq : (∑ i : Fin n, v i • coordinateVector i) = v := by
    simpa only [coordinateVector, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  calc
    L v = L (∑ i : Fin n, v i • coordinateVector i) := congrArg L heq.symm
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

/-- Coordinate expansion for continuous bilinear forms. -/
lemma bilinearForm_apply_eq_sum_coordinates
    (Q : Reference.Space n →L[ℝ] Reference.Space n →L[ℝ] ℝ)
    (u v : Reference.Space n) :
    Q u v = ∑ i : Fin n, ∑ j : Fin n,
      u i * v j * Q (coordinateVector i) (coordinateVector j) := by
  have heq : (∑ i : Fin n, u i • coordinateVector i) = u := by
    simpa only [coordinateVector, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr u
  calc
    Q u v = (Q (∑ i, u i • coordinateVector i)) v := by rw [heq]
    _ = ∑ i, u i * Q (coordinateVector i) v := by
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
    _ = ∑ i, u i * (∑ j, v j * Q (coordinateVector i) (coordinateVector j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [linearForm_apply_eq_sum_coordinates (Q (coordinateVector i)) v]
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

/-- The soft min/max approximation is globally Euclidean 1-Lipschitz. -/
theorem softMinMax_lipschitz [NeZero k] (row : Fin n → Fin k)
    (hrow : Function.Surjective row) {β : ℝ} (hβ : β ≠ 0) :
    LipschitzWith 1 (softMinMax row β) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((softMinMax_contDiff row hrow β).differentiable (by simp))
  intro x
  apply NNReal.coe_le_coe.mp
  change ‖fderiv ℝ (softMinMax row β) x‖ ≤ 1
  apply (fderiv ℝ (softMinMax row β) x).opNorm_le_bound (by norm_num)
  intro v
  rw [one_mul, Real.norm_eq_abs, linearForm_apply_eq_sum_coordinates]
  simp_rw [softMinMax_fderiv_coordinate row hrow hβ]
  calc
    |∑ i, v i * softMinMaxWeight row β x i| ≤
        ∑ i, |v i * softMinMaxWeight row β x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖v‖ * softMinMaxWeight row β x i := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (softMinMaxWeight_pos row hrow β x i).le]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i)
        (softMinMaxWeight_pos row hrow β x i).le
    _ = ‖v‖ := by rw [← Finset.mul_sum, sum_softMinMaxWeight row hrow β x, mul_one]

/-- A uniform global Hessian bound needed for dominated Gaussian interpolation. -/
theorem softMinMax_hessian_norm_le [NeZero k] (row : Fin n → Fin k)
    (hrow : Function.Surjective row) {β : ℝ} (hβ : 0 < β) (x : Reference.Space n) :
    ‖fderiv ℝ (fderiv ℝ (softMinMax row β)) x‖ ≤ 4 * β * (n : ℝ) ^ 2 := by
  apply (fderiv ℝ (fderiv ℝ (softMinMax row β)) x).opNorm_le_bound (by positivity)
  intro u
  apply (fderiv ℝ (fderiv ℝ (softMinMax row β)) x u).opNorm_le_bound (by positivity)
  intro v
  rw [Real.norm_eq_abs, bilinearForm_apply_eq_sum_coordinates]
  simp_rw [softMinMax_hessian_coordinate row hrow hβ.ne']
  calc
    |∑ i, ∑ j, u i * v j * softMinMaxHessian row β x j i| ≤
        ∑ i, ∑ j, |u i * v j * softMinMaxHessian row β x j i| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖u‖ * ‖v‖ * (4 * β) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      exact mul_le_mul
        (mul_le_mul (PiLp.norm_apply_le u i) (PiLp.norm_apply_le v j)
          (abs_nonneg _) (norm_nonneg _))
        (softMinMaxHessian_abs_le row hrow hβ.le x j i) (abs_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (4 * β * (n : ℝ) ^ 2 * ‖u‖) * ‖v‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end GaussianTilt.Paouris
