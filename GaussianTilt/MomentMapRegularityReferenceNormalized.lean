import GaussianTilt.MomentMapRegularityReferenceInterior

/-! # Actual physical-scale bounds on normalized zero-boundary references

Comparison with the unit paraboloid on a genuine inscribed ball forces a
quantitative positive depth. The local Pogorelov--Calabi bounds then depend
only on the actual inner and outer radii, not on an assumed Hessian or shape
of the original moment source.
-/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff Gradient ENNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma unit_density_reference_inscribed_ball_bound [NeZero n]
    {u : E n → ℝ} (hu : Continuous u) {S : Set (E n)} (hS : IsCompact S)
    (hc : ConvexOn ℝ S u) (hb : ∀ y ∈ frontier S, u y = 0)
    (huid : ∀ A, IsCompact A → A ⊆ interior S → volume (subgradientImageOn S u A) = volume A)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hSR : S ⊆ Metric.closedBall 0 R)
    (hrS : Metric.closedBall (0 : E n) r ⊆ interior S) :
    ∀ x ∈ Metric.closedBall (0 : E n) r, u x ≤ ‖x‖^2/2-r^2/2 := by
  have hn : S.Nonempty := ⟨0,interior_subset (hrS (Metric.mem_closedBall_self hr.le))⟩
  have hnonpos := alexandrovOn_unit_density_barriers hu hS hR hSR hb huid
  let T := Metric.closedBall (0 : E n) r
  let q := fun x : E n => ‖x‖^2/2-r^2/2
  have hT : IsCompact T := isCompact_closedBall _ _
  have huT : ∀ A, IsCompact A → A ⊆ interior T → volume (subgradientImageOn T u A) = volume A := by
    intro A hA hAT
    rw [subgradientImageOn_restrict_compact_interior (T:=T) hS hn hu.continuousOn hc hT hrS hAT]
    exact huid A hA (hAT.trans (interior_subset.trans hrS))
  have hqT : ∀ A, IsCompact A → A ⊆ interior T → volume (subgradientImageOn T q A) = volume A := by
    intro A _ hAT
    exact congrArg (fun B : Set (E n) => volume B)
      (subgradientImageOn_unit_paraboloid hAT (-(r^2/2)))
  have hqb : ∀ x ∈ frontier T, u x ≤ q x := by
    intro x hx
    have hxT := hT.isClosed.frontier_subset hx
    have hnorm : ‖x‖ = r := by
      have hle : ‖x‖ ≤ r := by simpa [T] using hxT
      apply le_antisymm hle
      by_contra hnot
      have hlt : ‖x‖ < r := lt_of_not_ge hnot
      have hib : Metric.ball (0 : E n) r ⊆ interior T :=
        interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
      exact hx.2 (hib (by simpa using hlt))
    have hh := (hnonpos x (interior_subset (hrS hxT))).2
    simpa [q,hnorm] using hh
  exact unit_density_alexandrovOn_comparison (by fun_prop : Continuous q) hu hT hqb hqT huT

lemma unit_density_reference_depth_on_half_ball [NeZero n]
    {u : E n → ℝ} (hu : Continuous u) {S : Set (E n)} (hS : IsCompact S)
    (hc : ConvexOn ℝ S u) (hb : ∀ y ∈ frontier S, u y = 0)
    (huid : ∀ A, IsCompact A → A ⊆ interior S → volume (subgradientImageOn S u A) = volume A)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hSR : S ⊆ Metric.closedBall 0 R)
    (hrS : Metric.closedBall (0 : E n) r ⊆ interior S) {x : E n}
    (hx : x ∈ Metric.closedBall (0 : E n) (r/2)) : 4*(r^2/16) ≤ -u x := by
  have hxnorm : ‖x‖ ≤ r/2 := by simpa using hx
  have hxfull : x ∈ Metric.closedBall (0 : E n) r :=
    Metric.closedBall_subset_closedBall (half_le_self hr.le) hx
  have hh := unit_density_reference_inscribed_ball_bound hu hS hc hb huid hr hR hSR hrS x hxfull
  have hsq : ‖x‖^2 ≤ (r/2)^2 := (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ r/2 from by positivity)).mpr hxnorm
  nlinarith

def referenceVolumeBound (n : ℕ) (R : ℝ) : ℝ := volume.real (Metric.closedBall (0 : E n) R)
def referenceHessianBound (n : ℕ) (r R : ℝ) : ℝ :=
  sectionInteriorHessianBound n (2*R) (referenceVolumeBound n R) (r^2/16)
def referenceThirdBound (n : ℕ) (r R : ℝ) : ℝ :=
  calabiThirdDerivativeBound n (referenceHessianBound n r R)
    (sectionThirdDerivativeRadius n (2*R) (referenceVolumeBound n R) (r^2/16))

/-- A uniform physical-scale Hessian and third-derivative bound follows
from actual unit density and actual inner/outer ball containment. -/
theorem smooth_reference_derivative_bounds_on_half_ball [NeZero n]
    {u : E n → ℝ} (huc : Continuous u) {S : Set (E n)} (hS : IsCompact S)
    (hu : ContDiffOn ℝ ∞ u (interior S)) (hc : ConvexOn ℝ S u)
    (hb : ∀ y ∈ frontier S, u y = 0)
    (huid : ∀ A, IsCompact A → A ⊆ interior S → volume (subgradientImageOn S u A) = volume A)
    (hH : ∀ y ∈ interior S, (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).PosDef)
    (hMA : ∀ y ∈ interior S, (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).det = 1)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hSR : S ⊆ Metric.closedBall 0 R)
    (hrS : Metric.closedBall (0 : E n) r ⊆ interior S) :
    (∀ x ∈ Metric.closedBall (0 : E n) (r/2), ∀ i j,
      |coordinateHessian (coordinatePullback u) (coordinateEquiv n x) i j| ≤ referenceHessianBound n r R) ∧
    (∀ x ∈ Metric.closedBall (0 : E n) (r/2), ∀ i j k,
      |coordinateThirdDerivative (coordinatePullback u) (coordinateEquiv n x) i j k| ≤ referenceThirdBound n r R) := by
  have hM : 0 ≤ referenceVolumeBound n R := ENNReal.toReal_nonneg
  have hδ : 0 < r^2/16 := div_pos (sq_pos_of_pos hr) (by norm_num)
  have hdiam : Metric.diam S ≤ 2*R := Metric.diam_le_of_subset_closedBall hR hSR
  have hmass : volume (subgradientImageOn S u (interior S)) ≤ ENNReal.ofReal (referenceVolumeBound n R) := by
    rw [alexandrovOn_identity_on_open_of_on_compact hS huid isOpen_interior Subset.rfl]
    change volume (interior S) ≤ ENNReal.ofReal (volume (Metric.closedBall (0 : E n) R)).toReal
    rw [ENNReal.ofReal_toReal (measure_closedBall_lt_top.ne)]
    exact measure_mono (interior_subset.trans hSR)
  have hinside {x : E n} (hx : x ∈ Metric.closedBall (0 : E n) (r/2)) : x ∈ S :=
    interior_subset (hrS (Metric.closedBall_subset_closedBall (half_le_self hr.le) hx))
  have hdepth {x : E n} (hx : x ∈ Metric.closedBall (0 : E n) (r/2)) : 4*(r^2/16) ≤ -u x :=
    unit_density_reference_depth_on_half_ball huc hS hc hb huid hr hR hSR hrS hx
  constructor
  · intro x hx i j
    exact interior_smooth_constant_density_hessian_bound_at_depth huc hS hu hc hb hH hMA
      (by positivity) hdiam hM hδ hmass (hinside hx) (by linarith [hdepth hx]) i j
  · intro x hx i j k
    exact interior_smooth_constant_density_thirdDerivative_bound_at_depth huc hS hu hc hb hH hMA
      (by positivity) hdiam hM hδ hmass (hinside hx) (hdepth hx) i j k

end GaussianTilt.MomentMapRegularity
