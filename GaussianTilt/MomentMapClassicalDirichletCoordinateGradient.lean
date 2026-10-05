import GaussianTilt.MomentMapClassicalDirichletMixedPatches
import GaussianTilt.MomentMapClassicalDirichletBoundaryCharts

/-!
# Genuine uniform coordinate gradient estimates

The actual differentiated PDE and the defining-function trace barrier
propagate the first boundary jet bounds throughout the body. No upper or
lower source Hessian estimate is used.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Both coordinate boundary gradient bounds follow from the actual zero
level set, scaled barriers, and a normalized transverse direction. -/
theorem boundary_coordinate_derivative_bound_of_barriers
    {u w : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hu : DifferentiableAt ℝ u x) (hw : ContDiffAt ℝ 2 w x)
    (hw0 : w x = 0) (hreg : coordinateGradient w x ≠ 0)
    (hzero : ∀ y, w y = 0 → u y = 0)
    {a b W : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbar : ∀ y, w y ≤ 0 → b*w y ≤ u y ∧ u y ≤ a*w y)
    (hW : ∀ i, |coordinateDerivative i w x| ≤ W) (i : Fin n) :
    |coordinateDerivative i u x| ≤ b*W := by
  have hj : ∃ j, coordinateDerivative j w x ≠ 0 := by
    by_contra! hh
    exact hreg (funext hh)
  obtain ⟨j,hj⟩ := hj
  let e := (coordinateDerivative j w x)⁻¹ • (Pi.single j 1 : CoordinateSpace n)
  have he : fderiv ℝ w x e = 1 := by
    simp only [e,map_smul,smul_eq_mul]
    exact inv_mul_cancel₀ hj
  have hlevel : ∀ᶠ y in 𝓝 x, w y = w x → u y = u x :=
    Eventually.of_forall (fun y hy => (hzero y (hy.trans hw0)).trans (hzero x hw0).symm)
  have hfirst := fderiv_eq_smul_of_level_constant hu hw he hlevel
  have hmul := normal_multiplier_bounds_of_barriers hu (hw.differentiableAt (by norm_num)) he
    (hzero x hw0) hw0 (Eventually.of_forall (fun y hy => hbar y hy.le))
  have hcoord : coordinateDerivative i u x = fderiv ℝ u x e * coordinateDerivative i w x :=
    congrArg (fun D : CoordinateSpace n →L[ℝ] ℝ => D (Pi.single i 1)) hfirst
  rw [hcoord, abs_mul, abs_of_nonneg (ha.trans hmul.1)]
  exact mul_le_mul hmul.2 (hW i) (abs_nonneg _) hb

/-- Uniform source gradient control from the real first differentiated
Monge--Ampère equation and the already controlled boundary first jet. -/
theorem coordinate_gradient_bound_from_boundary [NeZero n]
    {w u F : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hS : IsCompact {y | w y ≤ 0})
    {κ K D G : ℝ} (hκ : 0 < κ) (hK : 0 ≤ K)
    (hHw : ∀ y ∈ {y | w y ≤ 0},
      (coordinateHessian w y - κ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hH : ∀ y ∈ interior {y | w y ≤ 0}, (coordinateHessian u y).PosDef)
    (hMA : ∀ y ∈ interior {y | w y ≤ 0}, (coordinateHessian u y).det = Real.exp (F y))
    (hKF : ∀ y ∈ interior {y | w y ≤ 0}, ∀ i, |coordinateDerivative i F y| ≤ K)
    (hD : ∀ y ∈ interior {y | w y ≤ 0}, (coordinateHessian u y).det ≤ D)
    (hb : ∀ y ∈ frontier {y | w y ≤ 0}, ∀ i, |coordinateDerivative i u y| ≤ G) :
    ∀ x ∈ {y | w y ≤ 0}, ∀ i,
      |coordinateDerivative i u x| ≤ G - (K*max 1 D/κ)*w x := by
  let B := K*max 1 D/κ
  have hmax : 0 ≤ max 1 D := zero_le_one.trans (le_max_left _ _)
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hK hmax) hκ.le
  have hBκ : B*κ = K*max 1 D := div_mul_cancel₀ _ hκ.ne'
  have hu2 (i : Fin n) : ContDiff ℝ 2 (coordinateDerivative i u) :=
    contDiff_infty.mp (smooth_coordinateDerivative hu i) 2
  have hw2 : ContDiff ℝ 2 w := contDiff_infty.mp hw 2
  intro x hx i
  have hsign (s : ℝ) (hs : |s| ≤ 1) : s*coordinateDerivative i u x - G + B*w x ≤ 0 := by
    apply classical_dirichlet_maximum_principle hS
      ((continuous_const.mul (hu2 i).continuous).sub continuous_const |>.add (continuous_const.mul hw.continuous)).continuousOn
      (fun y _ => ((contDiffAt_const.mul (hu2 i).contDiffAt).sub contDiffAt_const).add
        (contDiffAt_const.mul hw2.contDiffAt))
      (fun y hy => (hH y hy).inv) ?_ ?_ x hx
    · intro y hy
      have hnear : ∀ᶠ z in 𝓝 y, (coordinateHessian u z).det = Real.exp (F z) := by
        filter_upwards [isOpen_interior.mem_nhds hy] with z hz
        exact hMA z hz
      rw [linearizedMA_add_at _ ((contDiffAt_const.mul (hu2 i).contDiffAt).sub contDiffAt_const)
        (contDiffAt_const.mul hw2.contDiffAt),
        linearizedMA_sub_at _ (contDiffAt_const.mul (hu2 i).contDiffAt) contDiffAt_const,
        linearizedMA_const_mul_at _ (hu2 i).contDiffAt, linearizedMA_const,
        linearizedMA_const_mul_at _ hw2.contDiffAt,
        linearizedMA_coordinateDerivative_variable_density hu hnear]
      have hl := linearizedMA_lower_of_hessian_lower (hH y hy).inv.posSemidef (hHw y (interior_subset hy))
      have htr := trace_inverse_lower_of_det_upper (hH y hy) (hD y hy)
      have h1 := mul_le_mul_of_nonneg_left hl hB
      have h2 := mul_le_mul_of_nonneg_left htr hK
      have hsF : |s*coordinateDerivative i F y| ≤ K := by
        rw [abs_mul]
        exact (mul_le_mul hs (hKF y hy i) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      have he := congrArg (fun z => z*(coordinateHessian u y)⁻¹.trace) hBκ
      nlinarith [neg_abs_le (s*coordinateDerivative i F y)]
    · intro y hy
      have hw0 : w y = 0 := frontier_le_subset_eq hw.continuous continuous_const hy
      have hsU : s*coordinateDerivative i u y ≤ G := by
        calc
          _ ≤ |s*coordinateDerivative i u y| := le_abs_self _
          _ = |s| * |coordinateDerivative i u y| := abs_mul _ _
          _ ≤ 1*G := mul_le_mul hs (hb y hy i) (abs_nonneg _) zero_le_one
          _ = G := one_mul _
      simpa [hw0] using sub_nonpos.mpr hsU
  have hp := hsign 1 (by norm_num)
  have hm := hsign (-1) (by norm_num)
  apply abs_le.mpr
  constructor <;> dsimp only [B] at * <;> nlinarith

end GaussianTilt.MomentMapRegularity
