import GaussianTilt.MomentMapRegularityConstantDensityMass
import GaussianTilt.MomentMapClassicalDirichletOperator

/-!
# Lower contact sets for the nonconvex ABP estimate

No convexity of the tested function is assumed. Interior supporting planes
force positive semidefinite Hessians, and compact minimization supplies the
whole ball of small slopes when a negative interior value lies below a
nonnegative boundary.
-/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped Topology BigOperators ContDiff Gradient ENNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The lower contact set of an arbitrary differentiable function. -/
def lowerContactSet (S : Set (E n)) (u : E n → ℝ) : Set (E n) :=
  {x | x ∈ interior S ∧ SupportsOn S u (gradient u x) x}

lemma measurableSet_lowerContactSet {S : Set (E n)} {u : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) : MeasurableSet (lowerContactSet S u) := by
  have hg := (contDiff_gradient_of_smooth hu).continuous
  have hc : IsClosed {x | SupportsOn S u (gradient u x) x} := by
    simp only [SupportsOn, setOf_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro _hy
    exact isClosed_le
      (hu.continuous.add (hg.inner (continuous_const.sub continuous_id))) continuous_const
  exact isOpen_interior.measurableSet.inter hc.measurableSet

lemma coordinateHessian_continuousLinearMap (L : CoordinateSpace n →L[ℝ] ℝ)
    (x : CoordinateSpace n) : coordinateHessian L x = 0 := by
  ext i j
  have he : coordinateDerivative i L = fun _ => L (Pi.single i 1) := by
    funext y
    simp [coordinateDerivative]
  change coordinateDerivative j (coordinateDerivative i L) x = 0
  rw [he]
  simp [coordinateDerivative]

/-- A lower supporting plane yields actual Hessian positivity, even when
`u` is not convex away from the contact point. -/
theorem hessian_posSemidef_of_lower_contact {S : Set (E n)} {u : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) {x : E n} (hx : x ∈ lowerContactSet S u) :
    (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosSemidef := by
  let e := coordinateEquiv n
  let U := coordinatePullback u
  let L : CoordinateSpace n →L[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ (E n) (gradient u x)).comp e.symm.toContinuousLinearMap
  have hU : ContDiff ℝ 2 U := (contDiff_infty.mp hu 2).comp e.symm.contDiff
  have hmax : IsLocalMax (fun y => L y - U y) (e x) := by
    have hn : ∀ᶠ y in 𝓝 (e x), e.symm y ∈ S := by
      exact e.symm.continuousAt.tendsto.eventually
        (by simpa only [e.symm_apply_apply] using mem_interior_iff_mem_nhds.mp hx.1)
    filter_upwards [hn] with y hy
    have hh := hx.2 (e.symm y) hy
    change inner ℝ (gradient u x) (e.symm y) - u (e.symm y) ≤
      inner ℝ (gradient u x) (e.symm (e x)) - u (e.symm (e x))
    rw [e.symm_apply_apply]
    rw [inner_sub_right] at hh
    linarith
  have hp := neg_hessian_posSemidef_of_isLocalMax (L.contDiff.sub hU) hmax
  rw [coordinateHessian_sub_at L.contDiff.contDiffAt hU.contDiffAt,
    coordinateHessian_continuousLinearMap, zero_sub, neg_neg] at hp
  exact hp

/-- The entire local subgradient image is the true gradient image of the
lower contact set. This does not require convexity. -/
lemma subgradientImageOn_interior_eq_gradient_contact {S : Set (E n)} {u : E n → ℝ}
    (hu : Differentiable ℝ u) :
    subgradientImageOn S u (interior S) = gradient u '' lowerContactSet S u := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    have he := supportsOn_eq_gradient hx (hu x) hp
    exact ⟨x, ⟨hx, he ▸ hp⟩, he.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx.1, hx.2⟩

/-- Sliding small-slope planes gives the geometric core of ABP. -/
theorem ball_subset_gradient_lowerContactSet {S : Set (E n)} {u : E n → ℝ}
    (hS : IsCompact S) (hu : ContDiff ℝ ∞ u) {x : E n} (hx : x ∈ S)
    {D : ℝ} (hD : 0 < D) (hdiam : Metric.diam S ≤ D) (hneg : u x < 0)
    (hb : ∀ y ∈ frontier S, 0 ≤ u y) :
    Metric.ball 0 (-u x / D) ⊆ gradient u '' lowerContactSet S u := by
  rw [← subgradientImageOn_interior_eq_gradient_contact (hu.differentiable (by simp))]
  intro p hp
  apply alexandrovOn_slope_mem_subgradientImage hu.continuous.continuousOn hS hx
  intro y hy
  have hyS : y ∈ S := hS.isClosed.frontier_subset hy
  have hd : ‖y - x‖ ≤ D := by
    rw [← dist_eq_norm]
    exact (Metric.dist_le_diam_of_mem hS.isBounded hyS hx).trans hdiam
  have hp' : ‖p‖ < -u x / D := by simpa only [Metric.mem_ball, dist_zero_right] using hp
  have hi : inner ℝ p (y - x) < -u x := by
    calc
      _ ≤ ‖p‖ * ‖y - x‖ := real_inner_le_norm _ _
      _ ≤ ‖p‖ * D := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ < (-u x / D) * D := mul_lt_mul_of_pos_right hp' hD
      _ = -u x := div_mul_cancel₀ _ hD.ne'
  linarith [hb y hy]

/-- The smooth area inequality bounds the volume of all contact slopes by
the actual Hessian determinant on the contact set. -/
theorem gradient_lowerContactSet_volume_le {S : Set (E n)} {u : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) :
    volume (gradient u '' lowerContactSet S u) ≤
      ∫⁻ x in lowerContactSet S u,
        ENNReal.ofReal (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det := by
  have hC := measurableSet_lowerContactSet (S := S) hu
  have harea := addHaar_image_le_lintegral_abs_det_fderiv volume hC
    (fun x _ => ((contDiff_gradient_of_smooth hu).differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt)
  refine harea.trans_eq ?_
  apply setLIntegral_congr_fun hC
  intro x hx
  dsimp only
  rw [determinant_fderiv_gradient_eq_coordinateHessian hu,
    abs_of_nonneg (hessian_posSemidef_of_lower_contact hu hx).det_nonneg]

end GaussianTilt.MomentMapRegularity
