import GaussianTilt.MomentMapRegularityConstantDensityCalabiBounds

/-!
# Quantitative third derivatives from normalized section geometry

A positive-depth point has an explicit neighborhood of positive-depth
points by convexity and the actual zero-boundary mass estimate. Pogorelov
supplies the Hessian bound on that neighborhood, and the actual Calabi
estimate then controls every third derivative at its center.
-/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators Topology ContDiff Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Elementary convex control of the upward oscillation on an inscribed ball. -/
lemma convex_value_rise_on_inscribed_ball {S : Set (E n)} {u : E n → ℝ}
    (hu : ConvexOn ℝ S u) {x y : E n} {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hb : Metric.closedBall x r ⊆ S) (huM : ∀ z ∈ S, |u z| ≤ M)
    (hy : ‖y-x‖ ≤ r) : r * (u y - u x) ≤ 2 * M * ‖y-x‖ := by
  by_cases hxy : y = x
  · subst y; simp
  have hd : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let t := ‖y-x‖ / r
  let z := x + (r / ‖y-x‖) • (y-x)
  have ht0 : 0 ≤ t := (div_pos hd hr).le
  have ht1 : t ≤ 1 := (div_le_one hr).mpr hy
  have hxS : x ∈ S := hb (Metric.mem_closedBall_self hr.le)
  have hzS : z ∈ S := by
    apply hb
    rw [Metric.mem_closedBall, dist_eq_norm]
    dsimp [z]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hd),
      div_mul_cancel₀ _ hd.ne']
  have he : (1-t) • x + t • z = y := by
    ext i
    change (1-t)*x i+t*(x i+(r/‖y-x‖)*(y i-x i))=y i
    dsimp [t]
    field_simp
    ring
  have hc := hu.2 hxS hzS (sub_nonneg.mpr ht1) ht0 (by ring : (1-t)+t=1)
  rw [he] at hc
  simp only [smul_eq_mul] at hc
  have hxlow := (abs_le.mp (huM x hxS)).1
  have hzup := (abs_le.mp (huM z hzS)).2
  have hup : u y - u x ≤ 2 * M * t := by
    have htz := mul_le_mul_of_nonneg_left hzup ht0
    have htx := mul_le_mul_of_nonneg_left hxlow ht0
    nlinarith
  calc
    r * (u y-u x) ≤ r*(2*M*t) := mul_le_mul_of_nonneg_left hup hr.le
    _ = _ := by dsimp [t]; field_simp

/-- An explicit neighborhood radius on which a threefold-depth point
retains the twofold depth needed for the Hessian estimate. -/
def sectionThirdDerivativeRadius (n : ℕ) (D M δ : ℝ) : ℝ :=
  min (sectionDepthRadius n D M δ)
    (δ * sectionDepthRadius n D M δ / (2 * sectionAbsoluteBound n D M))

lemma sectionThirdDerivativeRadius_pos {D M δ : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hδ : 0 < δ) :
    0 < sectionThirdDerivativeRadius n D M δ := by
  unfold sectionThirdDerivativeRadius
  exact lt_min (sectionDepthRadius_pos hD hM hδ)
    (div_pos (mul_pos hδ (sectionDepthRadius_pos hD hM hδ))
      (mul_pos (by norm_num) (sectionAbsoluteBound_pos hD hM)))

/-- The explicit neighborhood preserves positive section depth. -/
theorem neighborhood_depth_of_alexandrov_mass [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) {u : E n → ℝ} (hu : ConvexOn ℝ S u) (huc : ContinuousOn u S)
    (hb : ∀ x ∈ frontier S, u x = 0) {D M δ : ℝ}
    (hD : 0 ≤ D) (hdiam : Metric.diam S ≤ D) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hmass : volume (subgradientImageOn S u (interior S)) ≤ ENNReal.ofReal M)
    {x : E n} (hx : x ∈ S) (hdepth : 3 * δ ≤ -u x) {y : E n}
    (hy : ‖y-x‖ < sectionThirdDerivativeRadius n D M δ) :
    y ∈ interior S ∧ 2 * δ ≤ -u y := by
  let r := sectionDepthRadius n D M δ
  let B := sectionAbsoluteBound n D M
  have hr : 0 < r := sectionDepthRadius_pos hD hM hδ
  have hB : 0 < B := sectionAbsoluteBound_pos hD hM
  have hball : Metric.closedBall x r ⊆ S :=
    closedBall_subset_of_alexandrov_depth hS hu huc hb hD hdiam hM hδ hmass hx (by linarith)
  have hyr : ‖y-x‖ ≤ r := hy.le.trans (min_le_left _ _)
  have hyS : y ∈ S := hball (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hyr)
  have habs : ∀ z ∈ S, |u z| ≤ B := by
    intro z hz
    apply (alexandrovOn_uniform_abs_bound hS hu huc hb hM hmass z hz).trans
    dsimp [B, sectionAbsoluteBound]
    gcongr
  have hrise := convex_value_rise_on_inscribed_ball hu hr hB.le hball habs hyr
  have hyr' : ‖y-x‖ ≤ δ * r / (2 * B) := hy.le.trans (min_le_right _ _)
  have hproduct := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hB)).mp hyr'
  have hurise : u y - u x ≤ δ := by nlinarith
  have hydepth : 2 * δ ≤ -u y := by linarith
  refine ⟨?_, hydepth⟩
  by_contra hnot
  have hzero := hb y ⟨subset_closure hyS, hnot⟩
  linarith

/-- Full quantitative third-derivative a priori estimate for a smooth
unit-density solution. Neither gradient, Hessian, inverse ellipticity,
Calabi energy nor third-derivative bounds are assumed. -/
theorem smooth_constant_density_thirdDerivative_bound_at_depth [NeZero n]
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u) {S : Set (E n)} (hS : IsCompact S)
    (hc : ConvexOn ℝ S u) (hb : ∀ y ∈ frontier S, u y = 0)
    (hH : ∀ y ∈ interior S,
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).PosDef)
    (hMA : ∀ y ∈ interior S,
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).det = 1)
    {D M δ : ℝ} (hD : 0 ≤ D) (hdiam : Metric.diam S ≤ D) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hmass : volume (subgradientImageOn S u (interior S)) ≤ ENNReal.ofReal M)
    {x : E n} (hx : x ∈ S) (hdepth : 3 * δ ≤ -u x) (i j k : Fin n) :
    |coordinateThirdDerivative (coordinatePullback u) (coordinateEquiv n x) i j k| ≤
      calabiThirdDerivativeBound n (sectionInteriorHessianBound n D M δ)
        (sectionThirdDerivativeRadius n D M δ) := by
  let e := coordinateEquiv n
  let U := coordinatePullback u
  have hU : ContDiff ℝ ∞ U := hu.comp e.symm.contDiff
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnear {z : CoordinateSpace n}
      (hz : ‖e.symm z - e.symm (e x)‖ < sectionThirdDerivativeRadius n D M δ) :
      e.symm z ∈ interior S ∧ 2 * δ ≤ -u (e.symm z) := by
    rw [e.symm_apply_apply] at hz
    exact neighborhood_depth_of_alexandrov_mass hS hc hu.continuous.continuousOn hb hD hdiam hM hδ hmass hx hdepth hz
  apply thirdDerivative_bound_on_ball_of_hessian_bound hn hU (e x)
    (sectionThirdDerivativeRadius_pos hD hM hδ)
  · intro z hz
    simpa [e] using hH (e.symm z) (hnear hz).1
  · intro z hz
    simpa [e] using hMA (e.symm z) (hnear hz).1
  · intro z hz a b
    have hh := smooth_constant_density_hessian_bound_at_depth hu hS hc hb hH hMA hD hdiam hM hδ hmass
      (interior_subset (hnear hz).1) (hnear hz).2 a b
    simpa [U, e] using hh

end GaussianTilt.MomentMapRegularity
