import GaussianTilt.MomentMapSchauderCoordinateBridge

/-! # Matrix calculus in arbitrary real normed source coordinates

These are genuine Fréchet derivatives of the determinant and inverse,
proved from the determinant multilinear map and the inverse identity.
-/
noncomputable section
set_option maxSynthPendingDepth 1000
open Matrix Set
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.Letwin
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

lemma contDiff_matrix_det_field {k : WithTop ℕ∞} {H : E → Matrix ι ι ℝ}
    (hH : ∀ i j, ContDiff ℝ k (fun x => H x i j)) : ContDiff ℝ k (fun x => (H x).det) := by
  exact (determinantMultilinear (ι := ι)).contDiff.comp (contDiff_pi.mpr (fun i => contDiff_pi.mpr (hH i)))

lemma contDiff_matrix_adjugate_field {k : WithTop ℕ∞} {H : E → Matrix ι ι ℝ}
    (hH : ∀ i j, ContDiff ℝ k (fun x => H x i j)) (i j : ι) :
    ContDiff ℝ k (fun x => (H x).adjugate i j) := by
  simp_rw [Matrix.adjugate_apply]
  apply contDiff_matrix_det_field
  intro a b
  by_cases ha : a=j
  · subst a
    simpa using (contDiff_const : ContDiff ℝ k (fun _ : E => (Pi.single i (1 : ℝ) : ι → ℝ) b))
  · simpa [Matrix.updateRow_apply, ha] using hH a b

lemma contDiff_matrix_inv_field {k : WithTop ℕ∞} {H : E → Matrix ι ι ℝ}
    (hH : ∀ i j, ContDiff ℝ k (fun x => H x i j))
    (hdet : ∀ x, (H x).det ≠ 0) (i j : ι) :
    ContDiff ℝ k (fun x => (H x)⁻¹ i j) := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((contDiff_matrix_det_field hH).inv hdet).mul (contDiff_matrix_adjugate_field hH i j)

def matrixDirectionalDerivative (H : E → Matrix ι ι ℝ) (v x : E) : Matrix ι ι ℝ :=
  fun a b => fderiv ℝ (fun y => H y a b) x v

lemma matrixDirectionalDerivative_eq_fderiv {H : E → Matrix ι ι ℝ}
    (hH : ∀ a b, Differentiable ℝ (fun x => H x a b)) (v x : E) :
    matrixDirectionalDerivative H v x=fderiv ℝ H x v := by
  have hrow (a : ι) : Differentiable ℝ (fun y => H y a) := differentiable_pi.mpr (hH a)
  change _=fderiv ℝ (fun y a b => H y a b) x v
  rw [fderiv_pi (fun a => hrow a x)]
  ext a b
  simp only [ContinuousLinearMap.pi_apply]
  rw [fderiv_pi (fun b => hH a b x)]
  rfl

lemma matrixDirectionalDerivative_mul {H K : E → Matrix ι ι ℝ}
    (hH : ∀ a b, Differentiable ℝ (fun x => H x a b))
    (hK : ∀ a b, Differentiable ℝ (fun x => K x a b)) (v x : E) :
    matrixDirectionalDerivative (fun y => H y*K y) v x=
      matrixDirectionalDerivative H v x*K x+H x*matrixDirectionalDerivative K v x := by
  ext a b
  simp only [matrixDirectionalDerivative, Matrix.mul_apply, Matrix.add_apply]
  rw [fderiv_fun_sum (A := fun j y => H y a j*K y j b) (fun j _ => (hH a j x).mul (hK j b x))]
  simp only [ContinuousLinearMap.sum_apply, fderiv_fun_mul (hH _ _ x) (hK _ _ x),
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- The actual inverse derivative in every source direction. -/
theorem matrixDirectionalDerivative_inv {H : E → Matrix ι ι ℝ}
    (hH : ∀ a b, ContDiff ℝ 1 (fun x => H x a b)) (hdet : ∀ x, (H x).det ≠ 0)
    (v x : E) :
    matrixDirectionalDerivative (fun y => (H y)⁻¹) v x=
      -((H x)⁻¹*matrixDirectionalDerivative H v x*(H x)⁻¹) := by
  have hHi := fun a b => (contDiff_matrix_inv_field hH hdet a b).differentiable le_rfl
  have hHd := fun a b => (hH a b).differentiable le_rfl
  have hu (y : E) : IsUnit (H y).det := isUnit_iff_ne_zero.mpr (hdet y)
  have hid : (fun y => (H y)⁻¹*H y)=(fun _ => (1 : Matrix ι ι ℝ)) :=
    funext (fun y => Matrix.nonsing_inv_mul (H y) (hu y))
  have hz : matrixDirectionalDerivative (fun y => (H y)⁻¹*H y) v x=0 := by
    rw [hid]
    ext a b
    simp [matrixDirectionalDerivative]
  rw [matrixDirectionalDerivative_mul hHi hHd] at hz
  have hzero := congrArg (fun M => M*(H x)⁻¹) hz
  dsimp only at hzero
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu x), Matrix.mul_one, Matrix.zero_mul] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

lemma fderiv_matrix_det_field_apply {H : E → Matrix ι ι ℝ}
    (hH : ∀ a b, Differentiable ℝ (fun x => H x a b)) (v x : E) :
    fderiv ℝ (fun y => (H y).det) x v=Matrix.trace ((H x).adjugate*matrixDirectionalDerivative H v x) := by
  have hHd : Differentiable ℝ H := differentiable_pi.mpr (fun a => differentiable_pi.mpr (hH a))
  change fderiv ℝ (Matrix.det ∘ H) x v=_
  have hdet : DifferentiableAt ℝ (Matrix.det : Matrix ι ι ℝ → ℝ) (H x) :=
    (determinantMultilinear.hasFDerivAt (H x)).differentiableAt
  rw [fderiv_comp x hdet (hHd x),
    ContinuousLinearMap.comp_apply, fderiv_determinant_apply, ← matrixDirectionalDerivative_eq_fderiv hH]

/-- Jacobi's formula for the true source log determinant, in arbitrary
directions rather than a coordinate-only surrogate. -/
theorem fderiv_matrix_logdet_field_apply {H : E → Matrix ι ι ℝ}
    (hH : ∀ a b, ContDiff ℝ 1 (fun x => H x a b)) (hdet : ∀ x, (H x).det ≠ 0)
    (v x : E) :
    fderiv ℝ (fun y => Real.log (H y).det) x v=Matrix.trace ((H x)⁻¹*matrixDirectionalDerivative H v x) := by
  have hd := ((contDiff_matrix_det_field hH).differentiable le_rfl x).hasFDerivAt.log (hdet x)
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_matrix_det_field_apply (fun a b => (hH a b).differentiable le_rfl),
    Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.trace_smul]
  rfl

/-- The inverse derivative as an explicit finite sum of actual derivative
functionals, ready for Hölder product estimates. -/
theorem fderiv_matrix_inv_field {H : E → Matrix ι ι ℝ}
    (hH : ∀ a b, ContDiff ℝ 1 (fun x => H x a b)) (hdet : ∀ x, (H x).det ≠ 0)
    (x : E) (i j : ι) :
    fderiv ℝ (fun y => (H y)⁻¹ i j) x=
      -(∑ a, ∑ b, ((H x)⁻¹ i a*(H x)⁻¹ b j) • fderiv ℝ (fun y => H y a b) x) := by
  ext v
  have hh := congrFun (congrFun (matrixDirectionalDerivative_inv hH hdet v x) i) j
  simp only [matrixDirectionalDerivative, Matrix.neg_apply, Matrix.mul_apply,
    Finset.sum_mul] at hh
  rw [Finset.sum_comm] at hh
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  convert hh using 1
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end GaussianTilt.MomentMapSchauder
