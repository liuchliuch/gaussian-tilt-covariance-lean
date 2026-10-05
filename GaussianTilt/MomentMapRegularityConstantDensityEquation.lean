import GaussianTilt.MomentMapRegularityConstantDensityCalculus
import GaussianTilt.MomentMapPogorelovAlgebra

/-! # Actual differentiated unit-density identities and local logarithmic tests -/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The nondivergence-form linearized Monge--Ampère operator at one point. -/
def linearizedMA (A : Matrix (Fin n) (Fin n) ℝ) (f : CoordinateSpace n → ℝ)
    (x : CoordinateSpace n) : ℝ := trace (A * coordinateHessian f x)

lemma linearizedMA_log_at (A : Matrix (Fin n) (Fin n) ℝ)
    {f : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : ContDiffAt ℝ 2 f x) (hx : f x ≠ 0) :
    linearizedMA A (fun y => Real.log (f y)) x = linearizedMA A f x / f x -
      (coordinateGradient f x ⬝ᵥ (A *ᵥ coordinateGradient f x)) / (f x)^2 := by
  have he : coordinateHessian (fun y => Real.log (f y)) x =
      (f x)⁻¹ • coordinateHessian f x -
      ((f x)^2)⁻¹ • vecMulVec (coordinateGradient f x) (coordinateGradient f x) := by
    ext i j
    rw [coordinateHessian_log_at hf hx]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, coordinateGradient,
      smul_eq_mul, div_eq_mul_inv]
    ring
  unfold linearizedMA
  rw [he, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm (A *ᵥ coordinateGradient f x)]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

lemma linearizedMA_half_sq_at (A : Matrix (Fin n) (Fin n) ℝ)
    {f : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : ContDiffAt ℝ 2 f x) :
    linearizedMA A (fun y => (f y)^2 / 2) x =
      f x * linearizedMA A f x + coordinateGradient f x ⬝ᵥ (A *ᵥ coordinateGradient f x) := by
  have he : coordinateHessian (fun y => (f y)^2 / 2) x =
      f x • coordinateHessian f x + vecMulVec (coordinateGradient f x) (coordinateGradient f x) := by
    ext i j
    rw [coordinateHessian_half_sq_at hf]
    rfl
  unfold linearizedMA
  rw [he, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm (A *ᵥ coordinateGradient f x)]
  rfl

lemma linearizedMA_add_at (A : Matrix (Fin n) (Fin n) ℝ)
    {f g : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    linearizedMA A (fun y => f y + g y) x = linearizedMA A f x + linearizedMA A g x := by
  simp only [linearizedMA, coordinateHessian_add_at hf hg, Matrix.mul_add, Matrix.trace_add]

lemma linearizedMA_nonpos_at_max {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) {f : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : ContDiffAt ℝ 2 f x) (hx : IsLocalMax f x) : linearizedMA A f x ≤ 0 := by
  have h := trace_mul_nonneg_of_posSemidef A (-coordinateHessian f x) hA
    (neg_hessian_posSemidef_of_isLocalMax_at hf hx)
  simpa only [linearizedMA, Matrix.mul_neg, Matrix.trace_neg, neg_nonneg] using h

/-- Differentiating the literal constant determinant equation once gives
zero inverse-Hessian trace of every directional third derivative. The
constant equation is only needed in a neighborhood of the point. -/
theorem constant_density_first_trace_of_nonsingular {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hdet : ∀ y, (coordinateHessian u y).det ≠ 0)
    {x : CoordinateSpace n} (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1)
    (i : Fin n) :
    trace ((coordinateHessian u x)⁻¹ * matrixCoordinateDerivative (coordinateHessian u) i x) = 0 := by
  have he : (fun y => Real.log (coordinateHessian u y).det) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hMA] with y hy
    simp only [hy, Real.log_one]
  rw [← coordinateDerivative_logdet (contDiff_coordinateHessian (contDiff_infty.mp hu 3)) hdet]
  rw [coordinateDerivative_congr_nhds he]
  simp [coordinateDerivative]

/-- Twice differentiating the actual constant determinant equation produces
the positive third-derivative contraction that drives Pogorelov's estimate. -/
theorem constant_density_second_trace_of_nonsingular {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hdet : ∀ y, (coordinateHessian u y).det ≠ 0)
    {x : CoordinateSpace n} (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1)
    (i : Fin n) :
    linearizedMA (coordinateHessian u x)⁻¹ (fun y => coordinateHessian u y i i) x =
      trace ((coordinateHessian u x)⁻¹ * matrixCoordinateDerivative (coordinateHessian u) i x *
        (coordinateHessian u x)⁻¹ * matrixCoordinateDerivative (coordinateHessian u) i x) := by
  have he : (fun y => Real.log (coordinateHessian u y).det) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hMA] with y hy
    simp only [hy, Real.log_one]
  have htr : (fun y => trace ((coordinateHessian u y)⁻¹ *
      matrixCoordinateDerivative (coordinateHessian u) i y)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
    rw [← coordinateDerivative_logdet (contDiff_coordinateHessian (contDiff_infty.mp hu 3)) hdet]
    unfold coordinateDerivative
    rw [hy]
    simp
  have hz := coordinateDerivative_congr_nhds htr i
  change coordinateDerivative i (fun y => trace (inverseHessian u y *
    matrixCoordinateDerivative (coordinateHessian u) i y)) x = _ at hz
  rw [second_logdet_trace_identity hu hdet] at hz
  simp [coordinateDerivative] at hz
  change -_ + linearizedMA (coordinateHessian u x)⁻¹ (fun y => coordinateHessian u y i i) x = 0 at hz
  dsimp only [inverseHessian] at hz
  linarith

lemma hessian_coordinateDerivative_eq_matrixDerivative {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (i : Fin n) (x : CoordinateSpace n) :
    coordinateHessian (coordinateDerivative i u) x = matrixCoordinateDerivative (coordinateHessian u) i x := by
  ext a b
  change coordinateThirdDerivative u x i a b = coordinateThirdDerivative u x a b i
  exact coordinateThirdDerivative_cycle (contDiff_infty.mp hu 3) x i a b

lemma gradient_hessian_diagonal_eq_matrixDerivative_column {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (i : Fin n) (x : CoordinateSpace n) :
    coordinateGradient (fun y => coordinateHessian u y i i) x =
      matrixCoordinateDerivative (coordinateHessian u) i x *ᵥ Pi.single i 1 := by
  rw [Matrix.mulVec_single_one]
  ext a
  change coordinateThirdDerivative u x i i a = coordinateThirdDerivative u x a i i
  exact (coordinateThirdDerivative_cycle (contDiff_infty.mp hu 3) x i i a).trans
    (coordinateThirdDerivative_symm (contDiff_infty.mp hu 2) x i a i)

lemma matrix_inv_eq_adjugate_of_det_one {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.det = 1) :
    H⁻¹ = H.adjugate := by
  rw [Matrix.inv_def, hH]
  simp

/-- The first differentiated unit-density equation uses no invertibility
assumption outside the actual neighborhood where the equation holds. -/
theorem constant_density_first_trace {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1) (i : Fin n) :
    trace ((coordinateHessian u x)⁻¹ * matrixCoordinateDerivative (coordinateHessian u) i x) = 0 := by
  have he : (fun y => (coordinateHessian u y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := hMA
  have hd := coordinateDerivative_congr_nhds he i
  rw [coordinateDerivative_det (fun a b => (smooth_coordinateHessian hu a b).differentiable (by simp))] at hd
  rw [matrix_inv_eq_adjugate_of_det_one hMA.self_of_nhds]
  simpa [coordinateDerivative] using hd

/-- The actual differentiated unit-density equation gives the exact positive
third-derivative trace contraction. The adjugate provides a globally smooth
auxiliary field, so no inverse-field condition outside the domain is needed. -/
theorem constant_density_second_trace {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1) (i : Fin n) :
    linearizedMA (coordinateHessian u x)⁻¹ (fun y => coordinateHessian u y i i) x =
      trace ((coordinateHessian u x)⁻¹ * matrixCoordinateDerivative (coordinateHessian u) i x *
        (coordinateHessian u x)⁻¹ * matrixCoordinateDerivative (coordinateHessian u) i x) := by
  let H := coordinateHessian u
  let K := fun y => (H y).adjugate
  have hH (a b : Fin n) : Differentiable ℝ (fun y => H y a b) :=
    (smooth_coordinateHessian hu a b).differentiable (by simp)
  have hK (a b : Fin n) : Differentiable ℝ (fun y => K y a b) :=
    (contDiff_matrix_adjugate (fun c d => (smooth_coordinateHessian hu c d).of_le
      (show (1 : WithTop ℕ∞) ≤ ∞ by simp)) a b).differentiable le_rfl
  have hKx : K x = (H x)⁻¹ := (matrix_inv_eq_adjugate_of_det_one hMA.self_of_nhds).symm
  have hHI : (H x) * (H x)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (by rw [hMA.self_of_nhds]; norm_num))
  have hprod : (fun y => K y * H y) =ᶠ[𝓝 x] (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    filter_upwards [hMA] with y hy
    dsimp [K, H]
    rw [Matrix.adjugate_mul, hy]
    simp
  have hzero : matrixCoordinateDerivative (fun y => K y * H y) i x = 0 := by
    ext a b
    change coordinateDerivative i (fun y => (K y * H y) a b) x = 0
    have he := hprod.mono (fun y hy => congrFun (congrFun hy a) b)
    rw [coordinateDerivative_congr_nhds he i]
    simp [coordinateDerivative]
  rw [matrixCoordinateDerivative_mul hK hH] at hzero
  have hzero' := congrArg (fun M => M * (H x)⁻¹) hzero
  dsimp only at hzero'
  rw [Matrix.add_mul, Matrix.mul_assoc, hHI, Matrix.mul_one, Matrix.zero_mul, hKx] at hzero'
  have hDK : matrixCoordinateDerivative K i x =
      -((H x)⁻¹ * matrixCoordinateDerivative H i x * (H x)⁻¹) :=
    eq_neg_of_add_eq_zero_left hzero'
  have he : (fun y => (H y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := hMA
  have htr : (fun y => trace (K y * matrixCoordinateDerivative H i y)) =ᶠ[𝓝 x]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
    rw [← coordinateDerivative_det hH]
    unfold coordinateDerivative
    rw [hy]
    simp
  have hD (a b : Fin n) : Differentiable ℝ (fun y => matrixCoordinateDerivative H i y a b) :=
    (smooth_coordinateDerivative (smooth_coordinateHessian hu a b) i).differentiable (by simp)
  have hF (a b : Fin n) : Differentiable ℝ
      (fun y => (K y * matrixCoordinateDerivative H i y) a b) := by
    simp only [Matrix.mul_apply]
    apply Differentiable.fun_sum
    intro c _
    exact (hK a c).mul (hD c b)
  have hdiff := coordinateDerivative_congr_nhds htr i
  rw [coordinateDerivative_trace hF, matrixCoordinateDerivative_mul hK hD,
    hDK, hKx, matrixCoordinateDerivative_hessian_exchange hu] at hdiff
  simp only [Matrix.neg_mul, Matrix.trace_add, Matrix.trace_neg] at hdiff
  have hc : coordinateDerivative i (fun _ : CoordinateSpace n => (0 : ℝ)) x = 0 := by
    simp [coordinateDerivative]
  rw [hc] at hdiff
  change -_ + linearizedMA (coordinateHessian u x)⁻¹ (fun y => coordinateHessian u y i i) x = 0 at hdiff
  dsimp only [H] at hdiff
  linarith

end GaussianTilt.MomentMapRegularity
