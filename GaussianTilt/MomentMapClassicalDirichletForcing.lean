import GaussianTilt.MomentMapClassicalDirichletContinuationData

/-!
# Actual differentiated equations with variable logarithmic forcing

The continuation path is spatially variable. These identities keep the
first and second forcing derivatives instead of using unit-density
cancellations. The inverse Hessian is required only where the actual
local equation holds; a smooth adjugate auxiliary field avoids assumptions
outside that neighborhood.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateDerivative_logdet_at_point
    {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hH : ∀ a b, ContDiff ℝ 1 (fun x => H x a b)) {x : CoordinateSpace n}
    (hdet : (H x).det ≠ 0) (i : Fin n) :
    coordinateDerivative i (fun y => Real.log (H y).det) x =
      Matrix.trace ((H x)⁻¹ * matrixCoordinateDerivative H i x) := by
  have hd := ((contDiff_matrix_det hH).differentiable le_rfl x).hasFDerivAt.log hdet
  unfold coordinateDerivative
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  change (H x).det⁻¹ * coordinateDerivative i (fun y => (H y).det) x = _
  rw [coordinateDerivative_det (fun a b => (hH a b).differentiable le_rfl),
    Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.trace_smul]
  rfl

/-- First differentiation of `det Hess u = exp F`, retaining the true
spatial derivative of the logarithmic right-hand side. -/
theorem variable_density_first_trace {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y)) (i : Fin n) :
    trace ((coordinateHessian u x)⁻¹ * matrixCoordinateDerivative (coordinateHessian u) i x) =
      coordinateDerivative i F x := by
  have he : (fun y => Real.log (coordinateHessian u y).det) =ᶠ[𝓝 x] F := by
    filter_upwards [hMA] with y hy
    rw [hy, Real.log_exp]
  rw [← coordinateDerivative_logdet_at_point
    (contDiff_coordinateHessian (contDiff_infty.mp hu 3))
    (by rw [hMA.self_of_nhds]; exact (Real.exp_pos _).ne')]
  exact coordinateDerivative_congr_nhds he i

/-- The twice-differentiated equation for a variable density. The positive
third-derivative Gram contraction and the actual Hessian of `F` are both
present; the latter vanishes only for genuinely constant forcing. -/
theorem variable_density_second_trace {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y)) (i j : Fin n) :
    linearizedMA (coordinateHessian u x)⁻¹ (fun y => coordinateHessian u y i j) x =
      trace ((coordinateHessian u x)⁻¹ * matrixCoordinateDerivative (coordinateHessian u) j x *
        (coordinateHessian u x)⁻¹ * matrixCoordinateDerivative (coordinateHessian u) i x) +
      coordinateHessian F x i j := by
  let H := coordinateHessian u
  let K := fun y => Real.exp (-F y) • (H y).adjugate
  have hHd (a b : Fin n) : Differentiable ℝ (fun y => H y a b) :=
    (smooth_coordinateHessian hu a b).differentiable (by simp)
  have hKd (a b : Fin n) : Differentiable ℝ (fun y => K y a b) := by
    have hc := contDiff_matrix_adjugate (fun c d => smooth_coordinateHessian hu c d) a b
    exact ((hF.neg.exp).mul hc).differentiable (by simp)
  have hKinv {y : CoordinateSpace n} (hy : (H y).det = Real.exp (F y)) : K y = (H y)⁻¹ := by
    rw [Matrix.inv_def, hy, Ring.inverse_eq_inv', ← Real.exp_neg]
  have hKx := hKinv hMA.self_of_nhds
  have hdet : (H x).det ≠ 0 := by rw [hMA.self_of_nhds]; exact (Real.exp_pos _).ne'
  have hHI : H x * (H x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hprod : (fun y => K y * H y) =ᶠ[𝓝 x] (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    filter_upwards [hMA] with y hy
    rw [hKinv hy, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (by
      rw [hy]; exact (Real.exp_pos _).ne'))]
  have hzero : matrixCoordinateDerivative (fun y => K y * H y) j x = 0 := by
    ext a b
    change coordinateDerivative j (fun y => (K y * H y) a b) x = 0
    rw [coordinateDerivative_congr_nhds (hprod.mono (fun y hy => congrFun (congrFun hy a) b))]
    simp [coordinateDerivative]
  rw [matrixCoordinateDerivative_mul hKd hHd] at hzero
  have hzero' := congrArg (fun M => M * (H x)⁻¹) hzero
  dsimp only at hzero'
  rw [Matrix.add_mul, Matrix.mul_assoc, hHI, Matrix.mul_one, Matrix.zero_mul, hKx] at hzero'
  have hDK : matrixCoordinateDerivative K j x =
      -((H x)⁻¹ * matrixCoordinateDerivative H j x * (H x)⁻¹) :=
    eq_neg_of_add_eq_zero_left hzero'
  have htr : (fun y => trace (K y * matrixCoordinateDerivative H i y)) =ᶠ[𝓝 x]
      coordinateDerivative i F := by
    filter_upwards [hMA.eventually_nhds] with y hy
    rw [hKinv hy.self_of_nhds]
    exact variable_density_first_trace hu hy i
  have hD (a b : Fin n) : Differentiable ℝ (fun y => matrixCoordinateDerivative H i y a b) :=
    (smooth_coordinateDerivative (smooth_coordinateHessian hu a b) i).differentiable (by simp)
  have hP (a b : Fin n) : Differentiable ℝ
      (fun y => (K y * matrixCoordinateDerivative H i y) a b) := by
    simp only [Matrix.mul_apply]
    apply Differentiable.fun_sum
    intro c _
    exact (hKd a c).mul (hD c b)
  have heq := coordinateDerivative_congr_nhds htr j
  rw [coordinateDerivative_trace hP, matrixCoordinateDerivative_mul hKd hD,
    hDK, hKx, matrixCoordinateDerivative_hessian_exchange hu] at heq
  simp only [Matrix.neg_mul, Matrix.trace_add, Matrix.trace_neg] at heq
  change -_ + linearizedMA (H x)⁻¹ (fun y => coordinateHessian u y i j) x =
    coordinateHessian F x i j at heq
  change linearizedMA (H x)⁻¹ (fun y => coordinateHessian u y i j) x = _
  linarith

end GaussianTilt.MomentMapRegularity
