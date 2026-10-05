import GaussianTilt.MomentMapRegularityImprovementInitialNormalization
import GaussianTilt.MomentMapRegularityImprovementReference
import GaussianTilt.MomentMapRegularitySecondOrderLocalPerturbation

/-! # Constructing the first near-quadratic source from a normalized section -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff Gradient
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 1000000

def initialNormalizationBound (n : ℕ) (r R : ℝ) : ℝ :=
  max (initialInverseNormalizationBound n (referenceHessianBound n r R)) 1

def initialForwardNormalizationBound (n : ℕ) (r R : ℝ) : ℝ :=
  max (Real.sqrt ((n:ℝ)^2*max (referenceHessianBound n r R) 0)) 1

/-- The first near-quadratic normalization is derived from constant-density
comparison on a genuinely normalized section. No near-quadraticity, source
Hessian or source differentiability is among the assumptions. -/
theorem initial_reference_normalization [NeZero n] {u w f : E n → ℝ}
    (huc : Continuous u) (huconv : ConvexOn ℝ univ u) (hfc : Continuous f)
    (hwc : Continuous w) {S : Set (E n)} (hS : IsCompact S)
    (hw : ContDiffOn ℝ ∞ w (interior S)) (hwconv : ConvexOn ℝ S w)
    (hub : ∀ y∈frontier S, u y=0) (hwb : ∀ y∈frontier S, w y=0)
    (huMA : ∀ A, IsCompact A → A⊆interior S →
      volume (subgradientImageOn S u A)=(volume.withDensity (fun x=>ENNReal.ofReal (f x))) A)
    (hwMA : ∀ A, IsCompact A → A⊆interior S → volume (subgradientImageOn S w A)=volume A)
    {r R δ ρ : ℝ} (hr : 0 < r) (hR : 0≤R) (hSR : S⊆Metric.closedBall 0 R)
    (hrS : Metric.closedBall (0:E n) r⊆interior S) (hδ : 0 < δ) (hδ1 : δ<1)
    (hfd : ∀ x∈interior S, |f x-1|≤δ) (hρ : 0 < ρ)
    (hregion : ρ*initialNormalizationBound n r R≤r/2) :
    ∃ p : E n, ∃ L : E n ≃L[ℝ] E n,
      (L : E n →L[ℝ] E n).det=1 ∧ ‖(L : E n →L[ℝ] E n)‖≤ initialNormalizationBound n r R ∧
      ‖(L.symm : E n →L[ℝ] E n)‖≤ initialForwardNormalizationBound n r R ∧
      Continuous (improvementRescale u p L ρ) ∧ ConvexOn ℝ univ (improvementRescale u p L ρ) ∧
      improvementRescale u p L ρ 0=0 ∧
      ∀ x, ‖x‖≤1 → |improvementRescale u p L ρ x-‖x‖^2/2|≤
        δ*R^2/ρ^2+referenceTaylorConstant n r R*ρ*(initialNormalizationBound n r R)^3 := by
  obtain ⟨v,hv,he,hPD,hdet,hTaylor⟩ := exists_reference_improvement_representative
    hwc hS hw hwconv hwb hwMA hr hR hSR hrS 0
  have hclassical := positive_hessian_and_unit_det_of_C2_alexandrov hwconv isOpen_interior
    (Subset.refl (interior S)) (contDiffOn_infty.mp hw 2) hwMA
  have hhessian := (smooth_reference_derivative_bounds_on_half_ball hwc hS hw hwconv hwb hwMA
    (fun y hy=>(hclassical y hy).1) (fun y hy=>(hclassical y hy).2) hr hR hSR hrS).1
  have he0 : v =ᶠ[𝓝 (0:E n)] w := by
    filter_upwards [Metric.ball_mem_nhds (0:E n) (half_pos hr)] with y hy
    have hyn : ‖y‖<r/2 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    simpa using he y hyn.le
  have hHz : coordinateHessian (coordinatePullback v) 0=coordinateHessian (coordinatePullback w) 0 := by
    simpa only [map_zero] using coordinateHessian_congr_nhds (coordinatePullback_congr_nhds he0)
  have hentries : ∀ i j, |coordinateHessian (coordinatePullback v) 0 i j|≤referenceHessianBound n r R := by
    rw [hHz]
    simpa only [map_zero] using hhessian 0 (by simp only [Metric.mem_closedBall,dist_self]; positivity)
  let L := referenceNormalization hPD
  have hLbound : ‖(L : E n →L[ℝ] E n)‖≤ initialNormalizationBound n r R :=
    (referenceNormalization_norm_bound hPD hdet hentries).trans (le_max_left _ _)
  have hIbound : ‖(L.symm : E n →L[ℝ] E n)‖≤ initialForwardNormalizationBound n r R := by
    apply (referenceNormalization_inverse_norm_bound hPD (le_max_right _ _)
      (fun i j=>(hentries i j).trans (le_max_left _ _))).trans
    exact le_max_left _ _
  have hN : 0≤ initialNormalizationBound n r R := (by norm_num : (0:ℝ)≤1).trans (le_max_right _ _)
  have hH : Matrix.toEuclideanCLM (𝕜:=ℝ) (coordinateHessian (coordinatePullback v) 0)=frechetHessian v 0 := by
    simpa only [map_zero] using coordinateHessian_toEuclideanCLM_eq_frechetHessian (contDiff_infty.mp hv 2) 0
  have hcomparison := alexandrovOn_normalized_constant_density_perturbation huc hwc hfc hS hR hSR
    hub hwb hδ hδ1 hfd huMA hwMA
  have hcompare : ∀ y:E n, ‖y‖≤r/2 → |u y-v y|≤δ*R^2/2 := by
    intro y hy
    rw [he y hy,add_zero]
    apply hcomparison y
    apply interior_subset (hrS _)
    simpa only [Metric.mem_closedBall,dist_zero_right] using hy.trans (half_le_self hr.le)
  have herror := improvementRescale_error hρ (half_pos hr).le (by norm_num : (0:ℝ)≤1) hN
    (by positivity : 0≤δ*R^2/2) (referenceTaylorConstant_nonneg n r R) hLbound
    (by simpa using hregion) (H:=frechetHessian v 0) (a:=v 0) (p:=gradient v 0)
    (by intro x; rw [← hH]; exact referenceNormalization_quadratic hPD x) hcompare hTaylor
  refine ⟨gradient v 0,L,referenceNormalization_det_one hPD hdet,hLbound,hIbound,
    improvementRescale_continuous huc _ _ _,improvementRescale_convex huconv _ _ _,
    improvementRescale_zero _ _ _ _,?_⟩
  intro x hx
  convert herror x hx using 1 <;> ring

end GaussianTilt.MomentMapRegularity
