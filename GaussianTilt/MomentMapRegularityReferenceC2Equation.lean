import GaussianTilt.MomentMapRegularityReferenceDensityPointwise
import GaussianTilt.LetwinMomentJacobianInjective

/-! # Recovering positive Hessian and the classical equation after C²

The compact-set Alexandrov identity first forces a nonzero Jacobian by the
area inequality. Convexity gives positivity, hence true gradient injectivity;
the exact area formula then forces the Jacobian density to equal one.
-/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff Gradient ENNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma positive_hessian_and_unit_det_of_gradient_image_volume
    {u : E n → ℝ} (hu : ContDiff ℝ 2 u) {U : Set (E n)} (hU : IsOpen U)
    (hc : ConvexOn ℝ U u)
    (hid : ∀ A : Set (E n), IsCompact A → A ⊆ U → volume (gradient u '' A) = volume A) :
    ∀ x ∈ U, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef ∧
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det = 1 := by
  let f := fun x : E n => |(coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det|
  have hraw := contDiff_coordinatePullback hu
  have hfc : Continuous f := ((continuous_coordinateHessian hraw).matrix_det.abs).comp (coordinateEquiv n).continuous
  have hgrad := (contDiff_one_gradient_of_two hu).differentiable le_rfl
  have hlower : ∀ A : Set (E n), IsCompact A → A ⊆ U →
      volume A ≤ ∫⁻ y in A, ENNReal.ofReal (f y) := by
    intro A hA hAU
    rw [← hid A hA hAU]
    have hh := addHaar_image_le_lintegral_abs_det_fderiv volume hA.measurableSet
      (fun x _ => (hgrad x).hasFDerivAt.hasFDerivWithinAt)
    simpa only [determinant_fderiv_gradient_eq_coordinateHessian_two hu] using hh
  have hge (x : E n) (hx : x ∈ U) : 1 ≤ f x :=
    continuous_ge_one_of_compact_integral_lower hU hfc.continuousOn (fun _ _ => abs_nonneg _) hlower hx
  have hpos (x : E n) (hx : x ∈ U) :
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef := by
    have hrawcv : ConvexOn ℝ ((coordinateEquiv n).symm ⁻¹' U) (coordinatePullback u) :=
      hc.comp_linearMap (coordinateEquiv n).symm.toLinearMap
    have hpsd := coordinateHessian_posSemidef_of_convex
      (hU.preimage (coordinateEquiv n).symm.continuous) hrawcv hraw.contDiffOn
      (show coordinateEquiv n x ∈ (coordinateEquiv n).symm ⁻¹' U from by simpa using hx)
    apply posDef_of_posSemidef_det_ne_zero hpsd
    intro hz
    have hh := hge x hx
    change 1 ≤ |(coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det| at hh
    rw [hz,abs_zero] at hh
    norm_num at hh
  have hinj := gradient_injOn_of_hessian_posDef hu hc.1 hpos
  have hupper : ∀ A : Set (E n), IsCompact A → A ⊆ U →
      (∫⁻ y in A, ENNReal.ofReal (f y)) ≤ volume A := by
    intro A hA hAU
    have heq := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA.measurableSet
      (fun x _ => (hgrad x).hasFDerivAt.hasFDerivWithinAt) (hinj.mono hAU) (fun _ => (1 : ℝ≥0∞))
    have hh : volume A = ∫⁻ y in A, ENNReal.ofReal (f y) := by
      simpa only [determinant_fderiv_gradient_eq_coordinateHessian_two hu,mul_one,
        lintegral_const,Measure.restrict_apply_univ,one_mul,hid A hA hAU] using heq
    exact hh.ge
  intro x hx
  refine ⟨hpos x hx,?_⟩
  have hle := continuous_le_one_of_compact_integral_upper hU hfc.continuousOn hupper hx
  have heq := le_antisymm hle (hge x hx)
  simpa only [f,abs_of_pos (hpos x hx).det_pos] using heq

/-- Once the weak Alexandrov reference is C² locally, its positive Hessian
and literal unit Monge--Ampère equation follow from its actual image law.
Neither strict convexity, injectivity nor the PDE is assumed. -/
theorem positive_hessian_and_unit_det_of_C2_alexandrov
    {u : E n → ℝ} {S U : Set (E n)} (hc : ConvexOn ℝ S u)
    (hU : IsOpen U) (hUS : U ⊆ interior S) (hu : ContDiffOn ℝ 2 u U)
    (hid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S u A) = volume A) :
    ∀ x ∈ U, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef ∧
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det = 1 := by
  intro x hx
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let K := Metric.closedBall x (r/2)
  let V := Metric.ball x (r/2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKU : K ⊆ U := fun y hy => hball (lt_of_le_of_lt hy (half_lt_self hr))
  obtain ⟨v,hv,he⟩ := exists_global_contDiff_eq_near_compact 2 hU hu hK hKU
  have hepoint (y : E n) (hy : y ∈ K) : v y = u y := (he y hy).self_of_nhds
  have hvc : ConvexOn ℝ K v := by
    refine ⟨convex_closedBall _ _,?_⟩
    intro y hy z hz a b ha hb hab
    have hyS := interior_subset (hUS (hKU hy))
    have hzS := interior_subset (hUS (hKU hz))
    rw [hepoint y hy,hepoint z hz,hepoint _ ((convex_closedBall x (r/2)) hy hz ha hb hab)]
    exact hc.2 hyS hzS ha hb hab
  have hVid : ∀ A : Set (E n), IsCompact A → A ⊆ V → volume (gradient v '' A) = volume A := by
    intro A hA hAV
    have hAS : A ⊆ interior S := hAV.trans (Metric.ball_subset_closedBall.trans (hKU.trans hUS))
    have hAeq : subgradientImageOn S u A = gradient v '' A := by
      ext p
      constructor
      · rintro ⟨y,hy,hp⟩
        have hyK : y ∈ K := Metric.ball_subset_closedBall (hAV hy)
        have hyU := hKU hyK
        have hd := (hu.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
        have hgrad := (gradient_congr_nhds (he y hyK)).self_of_nhds
        exact ⟨y,hy,hgrad.trans (supportsOn_eq_gradient (hAS hy) hd hp).symm⟩
      · rintro ⟨y,hy,rfl⟩
        have hyK : y ∈ K := Metric.ball_subset_closedBall (hAV hy)
        have hyU := hKU hyK
        have hd := (hu.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
        have hgrad := (gradient_congr_nhds (he y hyK)).self_of_nhds
        refine ⟨y,hy,?_⟩
        rw [hgrad]
        exact supportsOn_gradient_of_convexOn hc (interior_subset (hAS hy)) hd
    rw [← hAeq]
    exact hid A hA hAS
  have hpair := positive_hessian_and_unit_det_of_gradient_image_volume hv Metric.isOpen_ball
    (hvc.subset Metric.ball_subset_closedBall (convex_ball _ _)) hVid x
    (Metric.mem_ball_self (half_pos hr))
  have hxK : x ∈ K := Metric.mem_closedBall_self (half_pos hr).le
  rw [coordinateHessian_congr_nhds (coordinatePullback_congr_nhds (he x hxK))] at hpair
  exact hpair

end GaussianTilt.MomentMapRegularity
