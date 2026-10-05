import GaussianTilt.MomentMapLinearDirichletSecondFieldChartPullback
import GaussianTilt.MomentMapLinearDirichletSmoothDomainStartInterior
import GaussianTilt.MomentMapLinearDirichletVariableWeakClosedGeometry

/-! # Actual physical boundary patches from the constructed inverse flattening chart -/
noncomputable section
set_option maxHeartbeats 2500000
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.HolderSpace GaussianTilt.MomentMapRegularity GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- The physical neighborhood, closed-half-ball containment, strict
interior containment and value recovery are derived from the actual IFT
chart. The only unknown-function input is its genuine flattened closed jet. -/
theorem boundary_secondFieldPatch_of_actual_flattened_jet
    {S A : Set (E n)} (d : SmoothInnerDomain S A)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f : Space {y | d.coordinateDefining y ≤ 0} ℝ α}
    (data : SmoothDomainLaplaceStartData d α f)
    (a : E n) (ha : a ∈ frontier d.body) (q : Fin n)
    (hq : fderiv ℝ d.defining a (EuclideanSpace.basisFun (Fin n) ℝ q)≠0)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (ψ : CoordinateSpace n → CoordinateSpace n)
    (hψ : ∀ y ∈ coordinateClosedHalfBall q r,
      ψ y=scaledRawInverseChart d.smooth a q hq s y)
    (J : Jet (CoordinateSpace n) ℝ (convex_coordinateClosedHalfBall q r) α)
    (hJ : ∀ y : coordinateClosedHalfBall q r,
      value (coordinateClosedHalfBall q r) ℝ α
        (jetValue (CoordinateSpace n) ℝ (convex_coordinateClosedHalfBall q r) α J) y=
          data.representative (ψ y)) :
    Nonempty (SecondFieldPatch d.body α data.euclideanRepresentative a) := by
  let F := scaledRawForwardChart d.defining a q s ∘ coordinateEquiv n
  let chart := regularLevelFlatteningChart d.smooth a q hq
  let U := chart.source ∩ F ⁻¹' rawChartBall r
  have hF : ContDiff ℝ ∞ F := (contDiff_scaledRawForwardChart d.smooth a q s).comp (coordinateEquiv n).contDiff
  have hU : IsOpen U := chart.open_source.inter ((isOpen_rawChartBall r).preimage hF.continuous)
  have ha0 : d.defining a=0 := by
    have hle : d.defining a≤0 := d.compact_sublevel.isClosed.frontier_subset ha
    have hn : ¬d.defining a<0 := by
      intro hh
      apply ha.2
      rw [d.interior_body]
      exact hh
    exact le_antisymm hle (le_of_not_gt hn)
  have haU : a ∈ U := by
    refine ⟨regularLevelFlatteningChart_source d.smooth a q hq,?_⟩
    change scaledRawForwardChart d.defining a q s (coordinateEquiv n a) ∈ rawChartBall r
    rw [scaledRawForward_self]
    simpa only [rawChartBall,mem_setOf_eq,map_zero,norm_zero] using hr
  have hFa (x : E n) : F x q=s⁻¹*(-d.defining x) := by
    change scaledRawForwardChart d.defining a q s (coordinateEquiv n x) q = _
    rw [scaledRawForward_normal,ContinuousLinearEquiv.symm_apply_apply,ha0,zero_sub]
  have hmap : MapsTo F (d.body ∩ U) (coordinateClosedHalfBall q r) := by
    intro x hx
    have hn : ‖(coordinateEquiv n).symm (F x)‖<r := hx.2.2
    refine ⟨hn.le,?_⟩
    change 0 ≤ F x q
    rw [hFa]
    exact mul_nonneg (inv_pos.mpr hs).le (neg_nonneg.mpr hx.1)
  have hmapi : MapsTo F (interior d.body ∩ U) (interior (coordinateClosedHalfBall q r)) := by
    intro x hx
    rw [interior_coordinateClosedHalfBall q hr]
    refine ⟨hx.2.2,?_⟩
    change 0 < F x q
    rw [hFa]
    have hxd : d.defining x<0 := by simpa only [d.interior_body] using hx.1
    exact mul_pos (inv_pos.mpr hs) (neg_pos.mpr hxd)
  have hv : ∀ x ∈ d.body ∩ U, data.euclideanRepresentative x=
      extendValue α (jetValue (CoordinateSpace n) ℝ (convex_coordinateClosedHalfBall q r) α J) (F x) := by
    intro x hx
    rw [extendValue_mem α _ (hmap hx),hJ ⟨F x,hmap hx⟩,hψ (F x) (hmap hx)]
    have hright : scaledRawInverseChart d.smooth a q hq s (F x)=coordinateEquiv n x := by
      apply scaledRawInverse_forward d.smooth a q hq hs.ne'
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx.2.1
    rw [hright]
    rfl
  have haBody : a ∈ d.body := by
    change d.defining a≤0
    exact ha0.le
  have hint : (interior d.body).Nonempty := by rw [d.interior_body]; exact d.negative_nonempty
  exact secondFieldPatch_of_smooth_chart_jet d.convex_body d.compact_sublevel hint
    (convex_coordinateClosedHalfBall q r) hα hα1 J F hF haBody hU haU hmap hmapi hv

/-- Direct interface for the globally smooth inverse model used by the
actual weak chart pullback. Its proved germ agreement, rather than an
assumed inverse, supplies the physical value recovery. -/
theorem boundary_secondFieldPatch_of_inverse_model_jet
    {S A : Set (E n)} (d : SmoothInnerDomain S A)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f : Space {y | d.coordinateDefining y ≤ 0} ℝ α}
    (data : SmoothDomainLaplaceStartData d α f)
    (a : E n) (ha : a ∈ frontier d.body) (q : Fin n)
    (hq : fderiv ℝ d.defining a (EuclideanSpace.basisFun (Fin n) ℝ q)≠0)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (hr1 : r ≤ 1)
    (ψ : CoordinateSpace n → CoordinateSpace n)
    (hψ : ∀ y ∈ rawChartClosedBall (n := n) 1,
      ψ =ᶠ[𝓝 y] scaledRawInverseChart d.smooth a q hq s)
    (J : Jet (CoordinateSpace n) ℝ (convex_coordinateClosedHalfBall q r) α)
    (hJ : ∀ y : coordinateClosedHalfBall q r,
      value (coordinateClosedHalfBall q r) ℝ α
        (jetValue (CoordinateSpace n) ℝ (convex_coordinateClosedHalfBall q r) α J) y=
          data.representative (ψ y)) :
    Nonempty (SecondFieldPatch d.body α data.euclideanRepresentative a) := by
  apply boundary_secondFieldPatch_of_actual_flattened_jet d hα hα1 data a ha q hq hs hr ψ _ J hJ
  intro y hy
  have hball : y ∈ rawChartClosedBall (n := n) 1 := hy.1.trans hr1
  exact (hψ y hball).self_of_nhds

end GaussianTilt.MomentMapLinearDirichlet
