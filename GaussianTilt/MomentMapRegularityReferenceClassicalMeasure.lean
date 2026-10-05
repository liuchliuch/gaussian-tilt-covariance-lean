import GaussianTilt.MomentMapRegularityReferenceClassicalGradient

/-! # Exact classical-to-Alexandrov identification on the real domain

Only C² regularity in the domain interior is required. Positive Hessians
supply genuine gradient injectivity, and the exact area formula identifies
the literal supporting-plane image measure.
-/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff Gradient ENNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma gradient_injOn_of_interior_hessian_posDef {u : E n → ℝ} {S : Set (E n)}
    (hu : ContDiffOn ℝ 2 u (interior S)) (hSc : Convex ℝ S)
    (hH : ∀ x ∈ interior S, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef) :
    InjOn (gradient u) (interior S) := by
  intro x hx y hy hxy
  have hseg : segment ℝ x y ⊆ interior S := hSc.interior.segment_subset hx hy
  have hsegcompact : IsCompact (segment ℝ x y) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨v,hv,he⟩ := exists_global_contDiff_eq_near_compact 2 isOpen_interior hu hsegcompact hseg
  have hHv : ∀ z ∈ segment ℝ x y,
      (coordinateHessian (coordinatePullback v) (coordinateEquiv n z)).PosDef := by
    intro z hz
    rw [coordinateHessian_congr_nhds (coordinatePullback_congr_nhds (he z hz))]
    exact hH z (hseg hz)
  have hveqx := (gradient_congr_nhds (he x (left_mem_segment ℝ x y))).self_of_nhds
  have hveqy := (gradient_congr_nhds (he y (right_mem_segment ℝ x y))).self_of_nhds
  exact gradient_injOn_of_hessian_posDef hv (convex_segment x y) hHv
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y) (by rw [hveqx,hveqy,hxy])

lemma determinant_fderiv_gradient_eq_coordinateHessian_interior {u : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) {x : E n} (hx : x ∈ U) :
    (fderiv ℝ (gradient u) x).det =
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det := by
  obtain ⟨v,hv,he⟩ := exists_global_contDiff_eq_near_compact 2 hU hu (isCompact_singleton (x:=x))
    (singleton_subset_iff.mpr hx)
  have hnear := he x (mem_singleton x)
  have hgrad := gradient_congr_nhds hnear
  rw [← hgrad.fderiv_eq,determinant_fderiv_gradient_eq_coordinateHessian_two hv,
    coordinateHessian_congr_nhds (coordinatePullback_congr_nhds hnear)]

/-- The literal Alexandrov image equals the classical unit Jacobian measure
on every measurable interior source set, including noncompact test sets. -/
theorem subgradientImageOn_volume_eq_of_interior_classical_unit_det
    {u : E n → ℝ} {S A : Set (E n)} (hu : ContDiffOn ℝ 2 u (interior S))
    (hc : ConvexOn ℝ S u) (hA : MeasurableSet A) (hAS : A ⊆ interior S)
    (hH : ∀ x ∈ interior S, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef)
    (hMA : ∀ x ∈ A, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det = 1) :
    volume (subgradientImageOn S u A) = volume A := by
  have hud (x : E n) (hx : x ∈ interior S) : DifferentiableAt ℝ u x :=
    (hu.contDiffAt (isOpen_interior.mem_nhds hx)).differentiableAt (by norm_num)
  have hgd (x : E n) (hx : x ∈ interior S) : DifferentiableAt ℝ (gradient u) x := by
    have hD := ((hu.contDiffAt (isOpen_interior.mem_nhds hx)).fderiv_right
      (m:=1) (by norm_num)).differentiableAt le_rfl
    exact (InnerProductSpace.toDual ℝ (E n)).symm.differentiableAt.comp x hD
  have hinj := gradient_injOn_of_interior_hessian_posDef hu hc.1 hH
  have himage : subgradientImageOn S u A = gradient u '' A := by
    ext p
    constructor
    · rintro ⟨x,hx,hp⟩
      exact ⟨x,hx,(supportsOn_eq_gradient (hAS hx) (hud x (hAS hx)) hp).symm⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x,hx,supportsOn_gradient_of_convexOn hc (interior_subset (hAS hx)) (hud x (hAS hx))⟩
  rw [himage]
  calc
    volume (gradient u '' A) = ∫⁻ _y in gradient u '' A, (1 : ℝ≥0∞) := by simp
    _ = ∫⁻ x in A, ENNReal.ofReal |(fderiv ℝ (gradient u) x).det| * 1 :=
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA
        (fun x hx => (hgd x (hAS hx)).hasFDerivAt.hasFDerivWithinAt) (hinj.mono hAS) (fun _ => 1)
    _ = ∫⁻ _x in A, (1 : ℝ≥0∞) := by
      apply setLIntegral_congr_fun hA
      intro x hx
      change ENNReal.ofReal |(fderiv ℝ (gradient u) x).det| * 1 = 1
      rw [determinant_fderiv_gradient_eq_coordinateHessian_interior isOpen_interior hu (hAS hx),hMA x hx]
      simp
    _ = volume A := by simp

end GaussianTilt.MomentMapRegularity
