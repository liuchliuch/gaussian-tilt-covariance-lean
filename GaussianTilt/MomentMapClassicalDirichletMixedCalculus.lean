import GaussianTilt.MomentMapClassicalDirichletForcing
import GaussianTilt.MomentMapRegularityConstantDensityPogorelov

/-!
# The genuine cancellation for tangential derivative equations

Differentiating a boundary-tangent vector field introduces apparent second
source derivatives. The actual inverse-Hessian identity cancels them, so the
forcing depends only on the source gradient and fixed chart derivatives.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateHessian_mul_at {f g : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    coordinateHessian (fun y => f y * g y) x =
      f x • coordinateHessian g x + g x • coordinateHessian f x +
        vecMulVec (coordinateGradient f x) (coordinateGradient g x) +
        vecMulVec (coordinateGradient g x) (coordinateGradient f x) := by
  ext i j
  have hfd := hf.differentiableAt (by norm_num)
  have hgd := hg.differentiableAt (by norm_num)
  have hfdi := (contDiffAt_coordinateDerivative hf (m := 1) (by norm_num) i).differentiableAt le_rfl
  have hgdi := (contDiffAt_coordinateDerivative hg (m := 1) (by norm_num) i).differentiableAt le_rfl
  have he : coordinateDerivative i (fun y => f y * g y) =ᶠ[𝓝 x]
      (fun y => coordinateDerivative i f y * g y + f y * coordinateDerivative i g y) := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hyf hyg
    exact coordinateDerivative_mul_at (hyf.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) i
  change coordinateDerivative j (coordinateDerivative i (fun y => f y * g y)) x = _
  rw [coordinateDerivative_congr_nhds he,
    coordinateDerivative_add_at (hfdi.fun_mul hgd) (hfd.fun_mul hgdi),
    coordinateDerivative_mul_at hfdi hgd, coordinateDerivative_mul_at hfd hgdi]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    coordinateHessian, coordinateGradient, smul_eq_mul]
  ring

/-- Product rule for the actual nondivergence operator. -/
lemma linearizedMA_mul_at {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {f g : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    linearizedMA A (fun y => f y * g y) x =
      f x * linearizedMA A g x + g x * linearizedMA A f x +
        2 * (coordinateGradient f x ⬝ᵥ (A *ᵥ coordinateGradient g x)) := by
  rw [linearizedMA, coordinateHessian_mul_at hf hg]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, smul_eq_mul]
  have he : (A *ᵥ coordinateGradient f x) ⬝ᵥ coordinateGradient g x =
      coordinateGradient f x ⬝ᵥ (A *ᵥ coordinateGradient g x) :=
    (symmetric_dot_mulVec A hA _ _).symm
  rw [he, dotProduct_comm (A *ᵥ coordinateGradient g x)]
  unfold linearizedMA
  ring

lemma linearizedMA_sub_at (A : Matrix (Fin n) (Fin n) ℝ)
    {f g : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    linearizedMA A (fun y => f y - g y) x = linearizedMA A f x - linearizedMA A g x := by
  simp only [linearizedMA, coordinateHessian_sub_at hf hg, Matrix.mul_sub, Matrix.trace_sub]

/-- The once-differentiated variable-density equation as an actual
linear equation for a source derivative. -/
lemma linearizedMA_coordinateDerivative_variable_density {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y)) (i : Fin n) :
    linearizedMA (coordinateHessian u x)⁻¹ (coordinateDerivative i u) x = coordinateDerivative i F x := by
  rw [linearizedMA, hessian_coordinateDerivative_eq_matrixDerivative hu]
  exact variable_density_first_trace hu hMA i

/-- Multiplication by a chart coefficient has an exact cancellation:
`A Hess u = I` reduces the cross term to one derivative of the coefficient. -/
theorem linearizedMA_chart_times_derivative {u F β : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {x : CoordinateSpace n} (hβ : ContDiffAt ℝ 2 β x)
    (hH : (coordinateHessian u x).PosDef)
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y)) (i : Fin n) :
    linearizedMA (coordinateHessian u x)⁻¹ (fun y => β y * coordinateDerivative i u y) x =
      β x * coordinateDerivative i F x + coordinateDerivative i u x *
        linearizedMA (coordinateHessian u x)⁻¹ β x + 2 * coordinateDerivative i β x := by
  have hAs : ((coordinateHessian u x)⁻¹).IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using hH.inv.isHermitian
  rw [linearizedMA_mul_at hAs hβ
    ((contDiff_infty.mp (smooth_coordinateDerivative hu i) 2).contDiffAt),
    linearizedMA_coordinateDerivative_variable_density hu hMA]
  have hv : (coordinateHessian u x)⁻¹ *ᵥ coordinateGradient (coordinateDerivative i u) x = Pi.single i 1 := by
    rw [gradient_coordinateDerivative_eq_hessian_column (contDiff_infty.mp hu 2), Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'), Matrix.one_mulVec]
  rw [hv, dotProduct_single, mul_one]
  rfl

/-- The actual local tangential vector field equation used for mixed
boundary Hessian estimates. No second-derivative bound on `u` is assumed. -/
theorem linearizedMA_tangential_derivative {u F β : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {x : CoordinateSpace n} (hβ : ContDiffAt ℝ 2 β x)
    (hH : (coordinateHessian u x).PosDef)
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y)) (a j : Fin n) :
    linearizedMA (coordinateHessian u x)⁻¹
      (fun y => coordinateDerivative a u y - β y * coordinateDerivative j u y) x =
      coordinateDerivative a F x - β x * coordinateDerivative j F x -
        coordinateDerivative j u x * linearizedMA (coordinateHessian u x)⁻¹ β x -
        2 * coordinateDerivative j β x := by
  rw [linearizedMA_sub_at _ ((contDiff_infty.mp (smooth_coordinateDerivative hu a) 2).contDiffAt)
      (hβ.mul ((contDiff_infty.mp (smooth_coordinateDerivative hu j) 2).contDiffAt)),
    linearizedMA_coordinateDerivative_variable_density hu hMA,
    linearizedMA_chart_times_derivative hu hβ hH hMA]
  ring

end GaussianTilt.MomentMapRegularity
