import GaussianTilt.MomentMapRegularityConstantDensityMass

/-!
# Quantitative normalized Pogorelov and Calabi a priori estimates

Both estimates follow from the actual smooth determinant equation on a
compact zero-boundary convex section. The literal Alexandrov mass bound,
positive-depth separation, gradient bound, Hessian bound, inverse-metric
bound and cubic energy bound are all derived. The constants depend only on
the dimension, enclosing radius and interior depth.
-/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators Topology ContDiff Gradient ENNReal NNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def normalizedHessianConstant (n : ℕ) (R δ : ℝ) : ℝ :=
  sectionInteriorHessianBound n (2*R) (volume.real (Metric.closedBall (0 : E n) R)) δ

def normalizedThirdDerivativeConstant (n : ℕ) (R δ : ℝ) : ℝ :=
  calabiThirdDerivativeBound n (normalizedHessianConstant n R δ)
    (sectionThirdDerivativeRadius n (2*R) (volume.real (Metric.closedBall (0 : E n) R)) δ)

/-- The normalized constant-density interior Hessian estimate, with no
mass, gradient or Hessian bound among its premises. -/
theorem normalized_constant_density_hessian_estimate [NeZero n]
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u) {S : Set (E n)} (hS : IsCompact S)
    (hc : ConvexOn ℝ S u) (hb : ∀ y ∈ frontier S, u y = 0)
    (hH : ∀ y ∈ interior S,
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).PosDef)
    (hMA : ∀ y ∈ interior S,
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).det = 1)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (houter : S ⊆ Metric.closedBall 0 R)
    {x : E n} (hx : x ∈ S) (hdepth : 2*δ ≤ -u x) (i j : Fin n) :
    |coordinateHessian (coordinatePullback u) (coordinateEquiv n x) i j| ≤
      normalizedHessianConstant n R δ := by
  have hm : volume (subgradientImageOn S u (interior S)) ≤
      ENNReal.ofReal (volume.real (Metric.closedBall (0 : E n) R)) := by
    change volume (subgradientImageOn S u (interior S)) ≤ ENNReal.ofReal (volume (Metric.closedBall (0 : E n) R)).toReal
    rw [ENNReal.ofReal_toReal (show volume (Metric.closedBall (0 : E n) R) ≠ ⊤ from
      (isCompact_closedBall (0 : E n) R).measure_lt_top.ne)]
    exact (subgradientImageOn_interior_volume_le_of_smooth_unit_det hu hMA).trans (measure_mono houter)
  exact smooth_constant_density_hessian_bound_at_depth hu hS hc hb hH hMA
    (by positivity) (Metric.diam_le_of_subset_closedBall hR.le houter) ENNReal.toReal_nonneg hδ hm hx hdepth i j

/-- The normalized constant-density interior third-derivative estimate.
All ellipticity and lower-order derivative bounds are consequences of the
same actual equation and normalized geometry. -/
theorem normalized_constant_density_thirdDerivative_estimate [NeZero n]
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u) {S : Set (E n)} (hS : IsCompact S)
    (hc : ConvexOn ℝ S u) (hb : ∀ y ∈ frontier S, u y = 0)
    (hH : ∀ y ∈ interior S,
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).PosDef)
    (hMA : ∀ y ∈ interior S,
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).det = 1)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (houter : S ⊆ Metric.closedBall 0 R)
    {x : E n} (hx : x ∈ S) (hdepth : 3*δ ≤ -u x) (i j k : Fin n) :
    |coordinateThirdDerivative (coordinatePullback u) (coordinateEquiv n x) i j k| ≤
      normalizedThirdDerivativeConstant n R δ := by
  have hm : volume (subgradientImageOn S u (interior S)) ≤
      ENNReal.ofReal (volume.real (Metric.closedBall (0 : E n) R)) := by
    change volume (subgradientImageOn S u (interior S)) ≤ ENNReal.ofReal (volume (Metric.closedBall (0 : E n) R)).toReal
    rw [ENNReal.ofReal_toReal (show volume (Metric.closedBall (0 : E n) R) ≠ ⊤ from
      (isCompact_closedBall (0 : E n) R).measure_lt_top.ne)]
    exact (subgradientImageOn_interior_volume_le_of_smooth_unit_det hu hMA).trans (measure_mono houter)
  exact smooth_constant_density_thirdDerivative_bound_at_depth hu hS hc hb hH hMA
    (by positivity) (Metric.diam_le_of_subset_closedBall hR.le houter) ENNReal.toReal_nonneg hδ hm hx hdepth i j k

end GaussianTilt.MomentMapRegularity
