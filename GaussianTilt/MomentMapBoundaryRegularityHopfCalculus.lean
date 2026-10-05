import GaussianTilt.MomentMapBoundaryRegularityBernsteinBall
import GaussianTilt.EllipticRegularityDistribution

/-! # Constructed exponential annulus barriers -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateHessian_exp {f : CoordinateSpace n → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : CoordinateSpace n) :
    coordinateHessian (fun y => Real.exp (f y)) x =
      Real.exp (f x) • (coordinateHessian f x + vecMulVec (coordinateGradient f x) (coordinateGradient f x)) := by
  ext i j
  have he : coordinateDerivative i (fun y => Real.exp (f y)) =
      fun y => Real.exp (f y) * coordinateDerivative i f y :=
    funext (coordinateDerivative_exp (hf.differentiable (by simp)) i)
  change coordinateDerivative j (coordinateDerivative i (fun y => Real.exp (f y))) x = _
  have hexp : Differentiable ℝ (fun y => Real.exp (f y)) := (Real.contDiff_exp.comp hf).differentiable (by simp)
  rw [he, coordinateDerivative_mul hexp
      ((smooth_coordinateDerivative hf i).differentiable (by simp)),
    coordinateDerivative_exp (hf.differentiable (by simp))]
  change Real.exp (f x) * coordinateDerivative j f x * coordinateDerivative i f x +
    Real.exp (f x) * coordinateHessian f x i j =
    Real.exp (f x) * (coordinateHessian f x i j + coordinateDerivative i f x * coordinateDerivative j f x)
  ring

lemma linearizedMA_exp (A : Matrix (Fin n) (Fin n) ℝ)
    {f : CoordinateSpace n → ℝ} (hf : ContDiff ℝ ∞ f) (x : CoordinateSpace n) :
    linearizedMA A (fun y => Real.exp (f y)) x =
      Real.exp (f x) * (linearizedMA A f x + coordinateGradient f x ⬝ᵥ (A *ᵥ coordinateGradient f x)) := by
  simp only [linearizedMA, coordinateHessian_exp hf, Matrix.mul_smul, Matrix.mul_add,
    Matrix.trace_smul, Matrix.trace_add, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, smul_eq_mul]
  rw [dotProduct_comm (A *ᵥ coordinateGradient f x)]

/-- A smooth radial barrier vanishing on the outer sphere. -/
def hopfExponentialBarrier (c : CoordinateSpace n) (a R : ℝ) (x : CoordinateSpace n) : ℝ :=
  Real.exp (a * (calabiBallCutoff c R x - R^2)) - Real.exp (-a*R^2)

lemma contDiff_hopfExponentialBarrier (c : CoordinateSpace n) (a R : ℝ) :
    ContDiff ℝ ∞ (hopfExponentialBarrier c a R) :=
  (Real.contDiff_exp.comp (contDiff_const.mul ((contDiff_calabiBallCutoff c R).sub contDiff_const))).sub contDiff_const

lemma hopfExponentialBarrier_eq_norm (c : CoordinateSpace n) (a R : ℝ) (x : CoordinateSpace n) :
    hopfExponentialBarrier c a R x =
      Real.exp (-a * ‖(coordinateEquiv n).symm x - (coordinateEquiv n).symm c‖^2) - Real.exp (-a*R^2) := by
  unfold hopfExponentialBarrier
  rw [calabiBallCutoff_eq_norm]
  congr 2
  ring

lemma linearizedMA_hopfExponentialBarrier (A : Matrix (Fin n) (Fin n) ℝ)
    (c : CoordinateSpace n) (a R : ℝ) (x : CoordinateSpace n) :
    linearizedMA A (hopfExponentialBarrier c a R) x =
      Real.exp (-a * ‖(coordinateEquiv n).symm x - (coordinateEquiv n).symm c‖^2) *
        (4*a^2*((x-c) ⬝ᵥ (A *ᵥ (x-c))) - 2*a*A.trace) := by
  let f : CoordinateSpace n → ℝ := fun y => a * (calabiBallCutoff c R y - R^2)
  have hf : ContDiff ℝ ∞ f := contDiff_const.mul ((contDiff_calabiBallCutoff c R).sub contDiff_const)
  have hg : coordinateGradient f x = (-2*a) • (x-c) := by
    ext i
    change coordinateDerivative i f x = _
    rw [coordinateDerivative_const_mul_at ((contDiff_calabiBallCutoff c R).differentiable (by simp) x |>.sub_const _) a]
    have he : coordinateDerivative i (fun y => calabiBallCutoff c R y - R^2) x =
        coordinateDerivative i (calabiBallCutoff c R) x := by simp [coordinateDerivative, fderiv_sub_const]
    rw [he, coordinateDerivative_calabiBallCutoff]
    change a * (-2 * (x i-c i)) = (-2*a) * (x i-c i)
    ring
  have hl : linearizedMA A f x = -2*a*A.trace := by
    rw [linearizedMA_const_mul_at _ (contDiff_infty.mp ((contDiff_calabiBallCutoff c R).sub contDiff_const) 2).contDiffAt,
      linearizedMA_sub_at _ (contDiff_infty.mp (contDiff_calabiBallCutoff c R) 2).contDiffAt contDiffAt_const,
      linearizedMA_calabiBallCutoff, linearizedMA_const]
    ring
  change linearizedMA A (fun y => Real.exp (f y) - Real.exp (-a*R^2)) x = _
  have hexp : ContDiffAt ℝ 2 (fun y => Real.exp (f y)) x := (contDiff_infty.mp (Real.contDiff_exp.comp hf) 2).contDiffAt
  rw [linearizedMA_sub_at _ hexp contDiffAt_const,
    linearizedMA_exp _ hf, linearizedMA_const, sub_zero, hg, hl]
  have he : f x = -a * ‖(coordinateEquiv n).symm x - (coordinateEquiv n).symm c‖^2 := by
    dsimp [f]
    rw [calabiBallCutoff_eq_norm]
    ring_nf
    rfl
  rw [he]
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- Actual strict positive forcing on an annulus follows from the two
ellipticity bounds and an explicit choice of the exponential parameter. -/
theorem hopfExponentialBarrier_forcing_lower {A : Matrix (Fin n) (Fin n) ℝ}
    (c x : CoordinateSpace n) {a R r lam N : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hlam : 0 ≤ lam)
    (hlo : lam * ‖(coordinateEquiv n).symm (x-c)‖^2 ≤ (x-c) ⬝ᵥ (A *ᵥ (x-c)))
    (htrace : A.trace ≤ N)
    (hinner : r ≤ ‖(coordinateEquiv n).symm x - (coordinateEquiv n).symm c‖)
    (houter : ‖(coordinateEquiv n).symm x - (coordinateEquiv n).symm c‖ ≤ R)
    (hsize : 2*N+1 ≤ 4*a*lam*r^2) :
    a * Real.exp (-a*R^2) ≤ linearizedMA A (hopfExponentialBarrier c a R) x := by
  rw [linearizedMA_hopfExponentialBarrier]
  have hr2 := pow_le_pow_left₀ hr hinner 2
  have hR2 := pow_le_pow_left₀ (norm_nonneg _) houter 2
  rw [map_sub] at hlo
  have hq : a ≤ 4*a^2*((x-c) ⬝ᵥ (A *ᵥ (x-c))) - 2*a*A.trace := by
    have h1 := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 4*a^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ 4*a^2*lam by positivity)
    have h3 := mul_le_mul_of_nonneg_left hsize ha.le
    have h4 := mul_le_mul_of_nonneg_left htrace (show 0 ≤ 2*a by positivity)
    nlinarith
  have he : Real.exp (-a*R^2) ≤ Real.exp (-a*‖(coordinateEquiv n).symm x - (coordinateEquiv n).symm c‖^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_left he ha.le).trans (by
    rw [mul_comm a]
    exact mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le)

end GaussianTilt.MomentMapRegularity
