import GaussianTilt.MomentMapBoundaryRegularityLocalOperations
import GaussianTilt.MomentMapBoundaryRegularityZeroBoundary

/-! # Genuine affine recentering of the intrinsic flat boundary system -/
noncomputable section
set_option maxHeartbeats 1000000
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateDerivative_ellipticRescale_at {v : CoordinateSpace n → ℝ}
    {c x : CoordinateSpace n} {r : ℝ} (hv : DifferentiableAt ℝ v (ellipticRescalePoint c r x))
    (i : Fin n) :
    coordinateDerivative i (fun y => v (ellipticRescalePoint c r y)) x =
      r*coordinateDerivative i v (ellipticRescalePoint c r x) := by
  have hp : HasFDerivAt (ellipticRescalePoint c r)
      (r • ContinuousLinearMap.id ℝ (CoordinateSpace n)) x := by
    simpa [ellipticRescalePoint] using ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul r).const_add c
  have he := (hv.hasFDerivAt.comp x hp).fderiv
  simp only [Function.comp_def] at he
  unfold coordinateDerivative
  rw [he]
  simp

lemma coordinateHessian_ellipticRescale_on {v : CoordinateSpace n → ℝ} {U : Set (CoordinateSpace n)}
    (hU : IsOpen U) (hv : ContDiffOn ℝ ∞ v U) {c x : CoordinateSpace n} {r : ℝ}
    (hx : ellipticRescalePoint c r x ∈ U) :
    coordinateHessian (fun y => v (ellipticRescalePoint c r y)) x =
      r^2 • coordinateHessian v (ellipticRescalePoint c r x) := by
  obtain ⟨w, hw, he⟩ := exists_global_smooth_eq_near_compact_coordinate hU hv isCompact_singleton
    (show {ellipticRescalePoint c r x} ⊆ U from singleton_subset_iff.mpr hx)
  have heq := he (ellipticRescalePoint c r x) (mem_singleton _)
  have hp : (fun y => w (ellipticRescalePoint c r y)) =ᶠ[𝓝 x]
      (fun y => v (ellipticRescalePoint c r y)) :=
    (contDiff_ellipticRescalePoint c r).continuous.continuousAt.tendsto.eventually heq
  rw [← coordinateHessian_congr_nhds hp, ← coordinateHessian_congr_nhds heq]
  exact coordinateHessian_ellipticRescale hw c r x

lemma ellipticRescalePoint_flat_coordinate {j : Fin n} {c : CoordinateSpace n}
    (hc : c j = 0) (r : ℝ) (y : CoordinateSpace n) : ellipticRescalePoint c r y j = r*y j := by
  simp [ellipticRescalePoint, hc]

lemma ellipticRescalePoint_flat_maps {j : Fin n} {c : CoordinateSpace n} {r : ℝ}
    (hc : c j = 0) (hr : 0 < r) (hcr : ‖(coordinateEquiv n).symm c‖ + r ≤ 1) :
    MapsTo (ellipticRescalePoint c r) (flatHalfBall j) (flatHalfBall j) ∧
      MapsTo (ellipticRescalePoint c r) (flatClosedHalfBall j) (flatClosedHalfBall j) := by
  have hb (y : CoordinateSpace n) : ‖(coordinateEquiv n).symm (ellipticRescalePoint c r y)‖ ≤
      ‖(coordinateEquiv n).symm c‖ + r*‖(coordinateEquiv n).symm y‖ := by
    simpa only [ellipticRescalePoint, map_add, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr] using
      norm_add_le ((coordinateEquiv n).symm c) (r • (coordinateEquiv n).symm y)
  constructor
  · intro y hy
    constructor
    · have hm := mul_lt_mul_of_pos_left hy.1 hr
      linarith [hb y]
    · rw [ellipticRescalePoint_flat_coordinate hc]
      exact mul_pos hr hy.2
  · intro y hy
    constructor
    · have hm := mul_le_mul_of_nonneg_left hy.1 hr.le
      linarith [hb y]
    · rw [ellipticRescalePoint_flat_coordinate hc]
      exact mul_nonneg hr.le hy.2

/-- Translation along the plane and positive dilation preserve the actual
local system. The forcing acquires exactly one power of the radius because
the solution is divided by that radius; weighted coefficient bounds are unchanged. -/
theorem LocalFlatEllipticSystem.recenter {j : Fin n} {u f : CoordinateSpace n → ℝ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {lam Λ K M r : ℝ}
    (h : LocalFlatEllipticSystem j u f A lam Λ K M) {c : CoordinateSpace n}
    (hc : c j = 0) (hr : 0 < r) (hcr : ‖(coordinateEquiv n).symm c‖ + r ≤ 1) :
    LocalFlatEllipticSystem j (fun y => r⁻¹*u (ellipticRescalePoint c r y))
      (fun y => r*f (ellipticRescalePoint c r y))
      (fun y => A (ellipticRescalePoint c r y)) lam Λ K (r*M) := by
  let P := ellipticRescalePoint c r
  have hP : ContDiff ℝ ∞ P := contDiff_ellipticRescalePoint c r
  obtain ⟨hs, hcl⟩ := ellipticRescalePoint_flat_maps hc hr hcr
  refine ⟨continuousOn_const.mul (h.continuous_boundary.comp hP.continuous.continuousOn hcl),
    contDiffOn_const.mul (h.smooth_interior.comp hP.contDiffOn hs),
    contDiffOn_const.mul (h.forcing_smooth.comp hP.contDiffOn hs),
    fun a b => (h.coefficient_smooth a b).comp hP.contDiffOn hs,
    fun y hy => h.positive _ (hs hy), fun y hy => h.elliptic _ (hs hy), ?_, ?_, ?_, ?_⟩
  · intro y hy k a b
    have hAd := (h.coefficient_smooth a b).contDiffAt ((isOpen_flatHalfBall j).mem_nhds (hs hy))
    change y j*|coordinateDerivative k (fun z => A (P z) a b) y| ≤ K
    rw [coordinateDerivative_ellipticRescale_at (hAd.differentiableAt (by simp)), abs_mul, abs_of_pos hr]
    have hh := h.coefficient_bound (P y) (hs hy) k a b
    dsimp only [P, matrixCoordinateDerivative] at hh
    rw [ellipticRescalePoint_flat_coordinate hc] at hh
    exact (by nlinarith : y j * (r * |coordinateDerivative k (fun z => A z a b) (P y)|) ≤ K)
  · intro y hy
    rw [abs_mul, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (h.forcing_bound _ (hs hy)) hr.le
  · intro y hy k
    have hfd := (h.contDiffAt_f (hs hy)).differentiableAt (by simp)
    have hfp : DifferentiableAt ℝ (fun z => f (ellipticRescalePoint c r z)) y :=
      hfd.comp y (hP.differentiable (by simp) y)
    rw [coordinateDerivative_const_mul_at hfp, coordinateDerivative_ellipticRescale_at hfd,
      abs_mul, abs_mul, abs_of_pos hr]
    have hh := mul_le_mul_of_nonneg_left (h.forcing_derivative_bound _ (hs hy) k) hr.le
    rw [ellipticRescalePoint_flat_coordinate hc] at hh
    nlinarith
  · intro y hy
    have hud := h.contDiffAt_u (hs hy)
    have hup : ContDiffAt ℝ 2 (fun z => u (P z)) y :=
      (contDiffAt_infty.mp hud 2).comp y (contDiff_infty.mp hP 2).contDiffAt
    rw [linearizedMA_const_mul_at _ hup]
    have hl : linearizedMA (A (P y)) (fun z => u (P z)) y = r^2*linearizedMA (A (P y)) u (P y) := by
      dsimp only [P]
      simp only [linearizedMA, coordinateHessian_ellipticRescale_on (isOpen_flatHalfBall j) h.smooth_interior (hs hy),
        Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [hl, h.equation _ (hs hy)]
    field_simp

end GaussianTilt.MomentMapRegularity
