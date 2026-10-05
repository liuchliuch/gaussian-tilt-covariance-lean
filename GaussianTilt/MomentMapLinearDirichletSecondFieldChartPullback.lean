import GaussianTilt.MomentMapLinearDirichletSecondFieldPatch
import GaussianTilt.MomentMapHolderChartComposition

/-! # Physical boundary fields from a genuine closed flattened jet

Only the fixed chart is smooth. Its full curvature term is included by the
proved closed-jet composition theorem. A compact convex physical patch and
its nonempty interior are constructed from the actual body geometry.
-/
noncomputable section
set_option maxHeartbeats 2500000
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pull back an actual flat closed-domain jet to a genuine physical
boundary field patch. No smooth extension of the unknown is required. -/
theorem secondFieldPatch_of_smooth_chart_jet
    {T : Set E} {S : Set F} (hT : Convex ℝ T) (hTc : IsCompact T)
    (hTi : (interior T).Nonempty) (hS : Convex ℝ S)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (J : Jet F ℝ hS α) (ψ : E → F) (hψ : ContDiff ℝ ∞ ψ)
    {u : E → ℝ} {x : E} (hx : x ∈ T) {U : Set E} (hU : IsOpen U) (hxU : x ∈ U)
    (hmap : MapsTo ψ (T ∩ U) S)
    (hmapi : MapsTo ψ (interior T ∩ U) (interior S))
    (hvalue : ∀ y ∈ T ∩ U, u y=extendValue α (jetValue F ℝ hS α J) (ψ y)) :
    Nonempty (SecondFieldPatch T α u x) := by
  obtain ⟨R,hR,hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hballU : Metric.closedBall x r ⊆ U :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hRU
  let K := T ∩ Metric.closedBall x r
  have hK : Convex ℝ K := hT.inter (convex_closedBall x r)
  have hKc : IsCompact K := hTc.inter_right Metric.isClosed_closedBall
  have hKi : (interior K).Nonempty := by
    have hxcl : x ∈ closure (interior T) := by
      rw [hT.closure_interior_eq_closure_of_nonempty_interior hTi,hTc.isClosed.closure_eq]
      exact hx
    obtain ⟨y,hy,hyx⟩ := Metric.mem_closure_iff.mp hxcl r hr
    refine ⟨y,?_⟩
    rw [show K=T ∩ Metric.closedBall x r from rfl,interior_inter,interior_closedBall x hr.ne']
    exact ⟨hy,by simpa only [Metric.mem_ball,dist_comm] using hyx⟩
  have hKsub : K ⊆ T ∩ U := fun y hy => ⟨hy.1,hballU hy.2⟩
  have hKisub : interior K ⊆ interior T ∩ U := by
    intro y hy
    exact ⟨interior_mono inter_subset_left hy,hballU (interior_subset hy).2⟩
  obtain ⟨C,hC,hcomp⟩ := exists_jet_smooth_chart_composition hS hK hKc hKi hα hα1 ψ hψ
    (hmap.mono_left hKsub) (hmapi.mono_left hKisub)
  obtain ⟨j,hj,hjv,hjD,hjH⟩ := hcomp J
  let V := Metric.ball x r
  have hV : IsOpen V := Metric.isOpen_ball
  have hTV : T ∩ V ⊆ K := fun y hy => ⟨hy.1,Metric.ball_subset_closedBall hy.2⟩
  have hiV : interior T ∩ V ⊆ interior K := by
    intro y hy
    rw [show K=T ∩ Metric.closedBall x r from rfl,interior_inter,interior_closedBall x hr.ne']
    exact hy
  have hju : EqOn (extendValue α (jetValue E ℝ hK α j)) u K := by
    intro y hy
    rw [extendValue_mem α _ hy,hjv ⟨y,hy⟩]
    exact (hvalue y (hKsub hy)).symm
  refine ⟨{
    patch := V
    isOpen_patch := hV
    mem_patch := Metric.mem_ball_self hr
    first := extendValue α (jetFirst E ℝ hK α j)
    second := extendValue α (jetSecond E ℝ hK α j)
    first_continuous := (continuousOn_extendValue α _).mono hTV
    second_continuous := (continuousOn_extendValue α _).mono hTV
    first_derivative := ?_
    second_derivative := ?_
    second_holder := ?_ }⟩
  · intro y hy
    have hyi := hiV hy
    have he : u =ᶠ[𝓝 y] extendValue α (jetValue E ℝ hK α j) := by
      filter_upwards [isOpen_interior.mem_nhds hyi] with z hz
      exact (hju (interior_subset hz)).symm
    exact (jet_hasFDerivAt hK hα j hyi).congr_of_eventuallyEq he
  · intro y hy
    exact jet_first_hasFDerivAt hK hα j (hiV hy)
  · refine ⟨‖jetSecond E ℝ hK α j‖,norm_nonneg _,?_⟩
    intro y hy z hz
    rw [extendValue_mem α _ (hTV hy),extendValue_mem α _ (hTV hz)]
    exact norm_value_sub_le K (E →L[ℝ] E →L[ℝ] ℝ) α (jetSecond E ℝ hK α j)
      ⟨y,hTV hy⟩ ⟨z,hTV hz⟩

end GaussianTilt.MomentMapLinearDirichlet
