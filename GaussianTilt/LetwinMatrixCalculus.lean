import GaussianTilt.LetwinDiffusion

/-!
# Matrix calculus for the Monge--Ampère diffusion

Jacobi's formula is proved from the derivative of the continuous multilinear
determinant. Inverse differentiation is proved by differentiating the actual
matrix inverse identity.
-/
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.Letwin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant as a continuous multilinear function of its rows. -/
def determinantMultilinear : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

@[simp] lemma determinantMultilinear_apply (A : Matrix ι ι ℝ) : determinantMultilinear A = A.det := rfl

lemma determinant_update_row (A D : Matrix ι ι ℝ) (i : ι) :
    Matrix.det (Function.update A i (D i)) = ∑ j, A.adjugate j i * D i j := by
  change (A.updateRow i (D i)).det = _
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  rfl

/-- Jacobi's formula, including at singular matrices, for actual Fréchet
matrix derivatives. -/
theorem fderiv_determinant_apply (A D : Matrix ι ι ℝ) :
    fderiv ℝ Matrix.det A D = Matrix.trace (A.adjugate * D) := by
  change fderiv ℝ determinantMultilinear A D = _
  rw [(determinantMultilinear.hasFDerivAt A).fderiv,
    ContinuousMultilinearMap.linearDeriv_apply]
  simp only [determinantMultilinear_apply, determinant_update_row, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]

lemma contDiff_matrix_det {n : ℕ} {k : WithTop ℕ∞}
    {H : CoordinateSpace n → Matrix ι ι ℝ}
    (hH : ∀ i j, ContDiff ℝ k (fun x => H x i j)) :
    ContDiff ℝ k (fun x => (H x).det) := by
  exact determinantMultilinear.contDiff.comp (contDiff_pi.mpr fun i => contDiff_pi.mpr (hH i))

lemma contDiff_matrix_adjugate {n : ℕ} {k : WithTop ℕ∞}
    {H : CoordinateSpace n → Matrix ι ι ℝ}
    (hH : ∀ i j, ContDiff ℝ k (fun x => H x i j)) (i j : ι) :
    ContDiff ℝ k (fun x => (H x).adjugate i j) := by
  simp_rw [Matrix.adjugate_apply]
  apply contDiff_matrix_det
  intro a b
  by_cases ha : a = j
  · subst a
    simpa using (contDiff_const : ContDiff ℝ k (fun _ : CoordinateSpace n => (Pi.single i (1 : ℝ) : ι → ℝ) b))
  · simpa [Matrix.updateRow_apply, ha] using hH a b

/-- Every inverse entry is smooth where the determinant is nonzero; the proof
uses the actual adjugate formula, not an assumed inverse regularity theorem. -/
lemma contDiff_matrix_inv {n : ℕ} {k : WithTop ℕ∞}
    {H : CoordinateSpace n → Matrix ι ι ℝ}
    (hH : ∀ i j, ContDiff ℝ k (fun x => H x i j))
    (hdet : ∀ x, (H x).det ≠ 0) (i j : ι) :
    ContDiff ℝ k (fun x => (H x)⁻¹ i j) := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((contDiff_matrix_det hH).inv hdet).mul (contDiff_matrix_adjugate hH i j)

lemma coordinateDerivative_sum {n : ℕ} {κ : Type*} [Fintype κ]
    (F : κ → CoordinateSpace n → ℝ) (hF : ∀ a, Differentiable ℝ (F a))
    (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => ∑ a, F a y) x = ∑ a, coordinateDerivative i (F a) x := by
  unfold coordinateDerivative
  rw [fderiv_fun_sum (fun a _ => hF a x)]
  simp only [ContinuousLinearMap.sum_apply]

/-- Coordinate derivative of a matrix field, entry by entry. -/
def matrixCoordinateDerivative {n : ℕ}
    (H : CoordinateSpace n → Matrix ι ι ℝ) (i : Fin n) (x : CoordinateSpace n) : Matrix ι ι ℝ :=
  fun a b => coordinateDerivative i (fun y => H y a b) x

omit [DecidableEq ι] in
lemma matrixCoordinateDerivative_eq_fderiv {n : ℕ}
    {H : CoordinateSpace n → Matrix ι ι ℝ}
    (hH : ∀ a b, Differentiable ℝ (fun x => H x a b)) (i : Fin n) (x : CoordinateSpace n) :
    matrixCoordinateDerivative H i x = fderiv ℝ H x (Pi.single i 1) := by
  have hrow (a : ι) : Differentiable ℝ (fun y => H y a) := differentiable_pi.mpr (hH a)
  change _ = fderiv ℝ (fun y a b => H y a b) x (Pi.single i 1)
  rw [fderiv_pi (fun a => hrow a x)]
  ext a b
  simp only [ContinuousLinearMap.pi_apply]
  rw [fderiv_pi (fun b => hH a b x)]
  rfl

omit [DecidableEq ι] in
lemma matrixCoordinateDerivative_mul {n : ℕ}
    {H K : CoordinateSpace n → Matrix ι ι ℝ}
    (hH : ∀ a b, Differentiable ℝ (fun x => H x a b))
    (hK : ∀ a b, Differentiable ℝ (fun x => K x a b)) (i : Fin n) (x : CoordinateSpace n) :
    matrixCoordinateDerivative (fun y => H y * K y) i x =
      matrixCoordinateDerivative H i x * K x + H x * matrixCoordinateDerivative K i x := by
  ext a b
  simp only [matrixCoordinateDerivative, Matrix.mul_apply, Matrix.add_apply]
  rw [coordinateDerivative_sum (fun j y => H y a j * K y j b) (fun j => (hH a j).mul (hK j b))]
  simp only [coordinateDerivative_mul (hH _ _) (hK _ _), Finset.sum_add_distrib]

/-- Differentiation of the actual nonsingular matrix inverse. -/
theorem matrixCoordinateDerivative_inv {n : ℕ}
    {H : CoordinateSpace n → Matrix ι ι ℝ}
    (hH : ∀ a b, ContDiff ℝ 1 (fun x => H x a b)) (hdet : ∀ x, (H x).det ≠ 0)
    (i : Fin n) (x : CoordinateSpace n) :
    matrixCoordinateDerivative (fun y => (H y)⁻¹) i x =
      -((H x)⁻¹ * matrixCoordinateDerivative H i x * (H x)⁻¹) := by
  have hHi := fun a b => (contDiff_matrix_inv hH hdet a b).differentiable le_rfl
  have hHd := fun a b => (hH a b).differentiable le_rfl
  have hu (y : CoordinateSpace n) : IsUnit (H y).det := isUnit_iff_ne_zero.mpr (hdet y)
  have hid : (fun y => (H y)⁻¹ * H y) = fun _ => (1 : Matrix ι ι ℝ) :=
    funext fun y => Matrix.nonsing_inv_mul (H y) (hu y)
  have hz : matrixCoordinateDerivative (fun y => (H y)⁻¹ * H y) i x = 0 := by
    rw [hid]
    ext a b
    simp [matrixCoordinateDerivative, coordinateDerivative]
  rw [matrixCoordinateDerivative_mul hHi hHd] at hz
  have hzero := congrArg (fun M => M * (H x)⁻¹) hz
  dsimp only at hzero
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu x),
    Matrix.mul_one, Matrix.zero_mul] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

/-- The determinant chain rule in coordinate form. -/
theorem coordinateDerivative_det {n : ℕ}
    {H : CoordinateSpace n → Matrix ι ι ℝ}
    (hH : ∀ a b, Differentiable ℝ (fun x => H x a b)) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => (H y).det) x =
      Matrix.trace ((H x).adjugate * matrixCoordinateDerivative H i x) := by
  have hHd : Differentiable ℝ H := differentiable_pi.mpr fun a => differentiable_pi.mpr (hH a)
  change fderiv ℝ (Matrix.det ∘ H) x (Pi.single i 1) = _
  have hdet : DifferentiableAt ℝ Matrix.det (H x) :=
    (determinantMultilinear.hasFDerivAt (H x)).differentiableAt
  rw [fderiv_comp x hdet (hHd x)]
  rw [ContinuousLinearMap.comp_apply, fderiv_determinant_apply,
    ← matrixCoordinateDerivative_eq_fderiv hH]

/-- Jacobi's logarithmic derivative in the nonsingular case. -/
theorem coordinateDerivative_logdet {n : ℕ}
    {H : CoordinateSpace n → Matrix ι ι ℝ}
    (hH : ∀ a b, ContDiff ℝ 1 (fun x => H x a b)) (hdet : ∀ x, (H x).det ≠ 0)
    (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => Real.log (H y).det) x =
      Matrix.trace ((H x)⁻¹ * matrixCoordinateDerivative H i x) := by
  have hd := ((contDiff_matrix_det hH).differentiable le_rfl x).hasFDerivAt.log (hdet x)
  unfold coordinateDerivative
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  change (H x).det⁻¹ * coordinateDerivative i (fun y => (H y).det) x = _
  rw [coordinateDerivative_det (fun a b => (hH a b).differentiable le_rfl),
    Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.trace_smul]
  rfl

lemma fderiv_apply_eq_sum_coordinates {n : ℕ} (f : CoordinateSpace n → ℝ)
    (x v : CoordinateSpace n) :
    fderiv ℝ f x v = ∑ i, v i * coordinateDerivative i f x := by
  have hv : (∑ i, v i • (Pi.single i 1 : CoordinateSpace n)) = v := by
    ext j
    simp [Pi.single_apply]
  calc
    fderiv ℝ f x v = fderiv ℝ f x (∑ i, v i • (Pi.single i 1 : CoordinateSpace n)) := by rw [hv]
    _ = _ := by simp [coordinateDerivative]

lemma coordinateDerivative_comp_gradient {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hV : ∀ y, DifferentiableAt ℝ V (coordinateGradient φ y)) (j : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative j (V ∘ coordinateGradient φ) x =
      ∑ a, coordinateDerivative a V (coordinateGradient φ x) * coordinateHessian φ x a j := by
  have hg (a : Fin n) : Differentiable ℝ (coordinateDerivative a φ) :=
    (contDiff_coordinateDerivative hφ (m := 1) (by norm_num) a).differentiable le_rfl
  have hgrad : Differentiable ℝ (coordinateGradient φ) := differentiable_pi.mpr hg
  unfold coordinateDerivative
  rw [fderiv_comp x (hV _) (hgrad x), ContinuousLinearMap.comp_apply]
  rw [fderiv_apply_eq_sum_coordinates]
  change (∑ a, (fderiv ℝ (fun y a => coordinateDerivative a φ y) x (Pi.single j 1)) a *
    coordinateDerivative a V (coordinateGradient φ x)) = _
  rw [fderiv_pi (fun a => hg a x)]
  simp only [ContinuousLinearMap.pi_apply, coordinateHessian, coordinateDerivative, mul_comm]

/-- Third derivatives commute in the last two slots, by Schwarz applied to
an actual first coordinate derivative. -/
lemma coordinateThirdDerivative_swap_last {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (x : CoordinateSpace n) (a b i : Fin n) :
    coordinateThirdDerivative φ x a b i = coordinateThirdDerivative φ x a i b := by
  have h := coordinateHessian_isSymm
    (contDiff_coordinateDerivative hφ (m := 2) (by norm_num) a) x
  exact (h.apply i b)

lemma contDiff_coordinateHessian {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (a b : Fin n) :
    ContDiff ℝ 1 (fun x => coordinateHessian φ x a b) :=
  contDiff_coordinateDerivative (contDiff_coordinateDerivative hφ (m := 2) (by norm_num) a)
    (m := 1) (by norm_num) b

/-- The first derivative of the actual Monge--Ampère equation. -/
theorem differentiated_mongeAmpere {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (hV : ∀ y, DifferentiableAt ℝ V (coordinateGradient φ y))
    (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    (j : Fin n) (x : CoordinateSpace n) :
    Matrix.trace ((coordinateHessian φ x)⁻¹ * matrixCoordinateDerivative (coordinateHessian φ) j x) =
      -coordinateDerivative j φ x +
      ∑ a, coordinateDerivative a V (coordinateGradient φ x) * coordinateHessian φ x a j := by
  rw [← coordinateDerivative_logdet (contDiff_coordinateHessian hφ) hdet]
  have heq : (fun y => Real.log (coordinateHessian φ y).det) =
      (fun y => -φ y + (V ∘ coordinateGradient φ) y) := funext hMA
  rw [heq]
  have hφd := hφ.differentiable (by norm_num)
  have hgrad : Differentiable ℝ (coordinateGradient φ) := differentiable_pi.mpr
    (fun a => (contDiff_coordinateDerivative hφ (m := 1) (by norm_num) a).differentiable le_rfl)
  have hcomp : Differentiable ℝ (V ∘ coordinateGradient φ) :=
    fun y => (hV y).comp y (hgrad y)
  have hadd : coordinateDerivative j (fun y => -φ y + (V ∘ coordinateGradient φ) y) x =
      -coordinateDerivative j φ x + coordinateDerivative j (V ∘ coordinateGradient φ) x := by
    unfold coordinateDerivative
    rw [fderiv_fun_add (f := fun y => -φ y) (hφd.neg x) (hcomp x), fderiv_fun_neg]
    simp
  rw [hadd, coordinateDerivative_comp_gradient (hφ.of_le (by norm_num)) hV]

end GaussianTilt.Letwin
