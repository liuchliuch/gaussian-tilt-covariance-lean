import GaussianTilt.MomentMapSchauderLocalSpatialBootstrap
import GaussianTilt.MomentMapSchauderLocalMongeAmpere

/-! # Genuine interior smoothness for variable smooth positive densities -/
noncomputable section
set_option maxSynthPendingDepth 1000
open Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

/-- Local C²,α plus a true positive Hessian and logdet H u = F(x), with
F smooth on the same open set, imply actual interior smoothness. -/
theorem local_spatial_contDiffOn_infty [NeZero n]
    {u F : KernelSpace n → ℝ} {U : Set (KernelSpace n)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hF : ContDiffOn ℝ ∞ F U)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ U, (euclideanHessianMatrix u x).PosDef)
    (hMA : ∀ x ∈ U, Real.log (euclideanHessianMatrix u x).det=F x)
    (hloc : ∀ a ∈ U, ∃ R H : ℝ, 0 < R ∧ 0 ≤ H ∧ Metric.closedBall a R ⊆ U ∧
      ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R,
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ H*‖x-y‖^α) :
    ContDiffOn ℝ ∞ u U :=
  local_spatial_contDiffOn_infty_of_holderJets hU hu hF hα hα1 hpos hMA
    (locallyHolderJetOn_two_of_hessian_holder hU hu hα.le hα1.le hloc)

/-- Coordinate form matching the intrinsic classical-continuation jets.
No global regularity, ellipticity, or spatial density extension is assumed. -/
theorem local_coordinate_logdet_contDiffOn_infty [NeZero n]
    {u F : KernelSpace n → ℝ} {U : Set (KernelSpace n)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hF : ContDiffOn ℝ ∞ F U)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ U, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef)
    (hMA : ∀ x ∈ U, Real.log (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det=F x)
    (hloc : ∀ a ∈ U, ∃ R H : ℝ, 0 < R ∧ 0 ≤ H ∧ Metric.closedBall a R ⊆ U ∧
      ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R,
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ H*‖x-y‖^α) :
    ContDiffOn ℝ ∞ u U := by
  have he (x : KernelSpace n) (hx : x ∈ U) :=
    coordinateHessian_pullback_eq_euclidean_at (hu.contDiffAt (hU.mem_nhds hx))
  exact local_spatial_contDiffOn_infty hU hu hF hα hα1
    (fun x hx => by simpa only [he x hx] using hpos x hx)
    (fun x hx => by simpa only [he x hx] using hMA x hx) hloc

/-- A true smooth positive, spatially varying determinant density gives
interior C∞ regularity from local C²,α and positive Hessian data. This
covers the nonconstant densities occurring at intermediate homotopy times. -/
theorem local_positive_density_contDiffOn_infty [NeZero n]
    {u ρ : KernelSpace n → ℝ} {U : Set (KernelSpace n)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hρ : ContDiffOn ℝ ∞ ρ U) (hρpos : ∀ x ∈ U, 0 < ρ x)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ U, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef)
    (hMA : ∀ x ∈ U, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det=ρ x)
    (hloc : ∀ a ∈ U, ∃ R H : ℝ, 0 < R ∧ 0 ≤ H ∧ Metric.closedBall a R ⊆ U ∧
      ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R,
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ H*‖x-y‖^α) :
    ContDiffOn ℝ ∞ u U := by
  have hlog : ContDiffOn ℝ ∞ (fun x => Real.log (ρ x)) U := hρ.log (fun x hx => (hρpos x hx).ne')
  exact local_coordinate_logdet_contDiffOn_infty hU hu hlog hα hα1 hpos
    (fun x hx => congrArg Real.log (hMA x hx)) hloc

end GaussianTilt.MomentMapSchauder
