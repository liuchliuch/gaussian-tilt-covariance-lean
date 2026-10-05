import GaussianTilt.MomentMapSchauderLinearization

/-!
# The actual finite-difference elliptic equation for a C² moment map

Only second derivatives are used to derive the linear equation.  The
coefficient is the integral of inverse interpolated Hessians, rather than
an inverse chosen by a mean-value assertion.
-/
noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.Letwin

/-- A finite increment divided by a scalar step.  Keeping the displacement
separate also covers a scalar step times any coordinate direction. -/
def sourceDifferenceQuotient {n : ℕ} (u : CoordinateSpace n → ℝ)
    (h : CoordinateSpace n) (s : ℝ) (x : CoordinateSpace n) : ℝ :=
  s⁻¹ * (u (x + h) - u x)

lemma contDiff_sourceDifferenceQuotient {n : ℕ} {u : CoordinateSpace n → ℝ}
    {k : WithTop ℕ∞} (hu : ContDiff ℝ k u) (h : CoordinateSpace n) (s : ℝ) :
    ContDiff ℝ k (sourceDifferenceQuotient u h s) :=
  contDiff_const.mul ((hu.comp (contDiff_id.add contDiff_const)).sub hu)

lemma coordinateDerivative_sourceDifferenceQuotient {n : ℕ} {u : CoordinateSpace n → ℝ}
    (hu : Differentiable ℝ u) (h : CoordinateSpace n) (s : ℝ) (i : Fin n)
    (x : CoordinateSpace n) :
    coordinateDerivative i (sourceDifferenceQuotient u h s) x =
      sourceDifferenceQuotient (coordinateDerivative i u) h s x := by
  have htrans : Differentiable ℝ (fun y => u (y + h)) :=
    hu.comp (differentiable_id.add (differentiable_const h))
  unfold sourceDifferenceQuotient coordinateDerivative
  rw [fderiv_const_mul (a := fun y => u (y + h) - u y) ((htrans x).sub (hu x)),
    fderiv_fun_sub (htrans x) (hu x), fderiv_comp_add_right]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]

/-- Difference quotients commute with the literal coordinate Hessian using
C² regularity alone. -/
lemma coordinateHessian_sourceDifferenceQuotient {n : ℕ} {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) (h : CoordinateSpace n) (s : ℝ) (x : CoordinateSpace n) :
    coordinateHessian (sourceDifferenceQuotient u h s) x =
      s⁻¹ • (coordinateHessian u (x + h) - coordinateHessian u x) := by
  ext i j
  have hui := (contDiff_coordinateDerivative hu (m := 1) (by norm_num) i).differentiable le_rfl
  change coordinateDerivative j (coordinateDerivative i (sourceDifferenceQuotient u h s)) x = _
  have he : coordinateDerivative i (sourceDifferenceQuotient u h s) =
      sourceDifferenceQuotient (coordinateDerivative i u) h s := by
    funext y
    exact coordinateDerivative_sourceDifferenceQuotient (hu.differentiable (by norm_num)) h s i y
  rw [he, coordinateDerivative_sourceDifferenceQuotient hui]
  rfl

/-- The coefficient field arising by integrating Jacobi's formula between
actual Hessians at `x` and `x+h`. -/
def sourceDifferenceCoefficient {n : ℕ} (u : CoordinateSpace n → ℝ)
    (h : CoordinateSpace n) (x : CoordinateSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  averagedInverse (coordinateHessian u x) (coordinateHessian u (x + h))

/-- Trace-form linear equation for the actual finite difference.  Crucially,
this theorem does not ask for third derivatives of the moment potential. -/
theorem sourceDifferenceQuotient_trace_equation {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hH : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    (h : CoordinateSpace n) (s : ℝ) (x : CoordinateSpace n) :
    Matrix.trace (sourceDifferenceCoefficient φ h x *
      coordinateHessian (sourceDifferenceQuotient φ h s) x) =
      -sourceDifferenceQuotient φ h s x +
        sourceDifferenceQuotient (fun y => V (coordinateGradient φ y)) h s x := by
  rw [coordinateHessian_sourceDifferenceQuotient hφ,
    Matrix.mul_smul, Matrix.trace_smul]
  change s⁻¹ * Matrix.trace (averagedInverse (coordinateHessian φ x)
    (coordinateHessian φ (x + h)) * (coordinateHessian φ (x + h) - coordinateHessian φ x)) = _
  rw [← logdet_sub_eq_trace_averagedInverse (hH x) (hH (x + h)), hMA (x + h), hMA x]
  simp only [sourceDifferenceQuotient]
  ring

/-- The literal nondivergence-form PDE, with the coefficient and the second
partial derivatives spelled out in the indices used by elliptic estimates. -/
theorem sourceDifferenceQuotient_elliptic_equation {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hH : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    (h : CoordinateSpace n) (s : ℝ) (x : CoordinateSpace n) :
    (∑ i, ∑ j, sourceDifferenceCoefficient φ h x i j *
      coordinateDerivative j (coordinateDerivative i (sourceDifferenceQuotient φ h s)) x) =
      -sourceDifferenceQuotient φ h s x +
        sourceDifferenceQuotient (fun y => V (coordinateGradient φ y)) h s x := by
  have hsym := coordinateHessian_isSymm (contDiff_sourceDifferenceQuotient hφ h s) x
  have he := sourceDifferenceQuotient_trace_equation hφ hH hMA h s x
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hsym.apply i j]
  rfl

end GaussianTilt.MomentMapSchauder
