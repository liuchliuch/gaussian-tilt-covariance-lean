import GaussianTilt.MomentMapSchauderGlobalPatchGeometry
import GaussianTilt.MomentMapHolderChartRecoveryBounds
import GaussianTilt.MomentMapSchauderBoundaryVariableJetEstimate

/-! # Quantitative recovery of the true physical closed Hessian fields -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2200000
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.HolderSpace
variable {n : ℕ}

/-- The closed physical Hessian is recovered by genuine interior chain
rules and density, with one fixed chart constant before every test jet. -/
theorem exists_physical_hessian_recovery_bound
    {S : Set (KernelSpace n)} (hS : Convex ℝ S) (hSc : IsCompact S) (hint : (interior S).Nonempty)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (q : Fin n) (a : KernelSpace n)
    {r ρ : ℝ} (hr : 0 < r) (hρ1 : ρ ≤ 1)
    (φ : KernelSpace n → KernelSpace n) (hφ : ContDiff ℝ ∞ φ)
    (hmap : MapsTo φ (S ∩ Metric.closedBall a (2*r)) (flatClosedPatch q ρ))
    (hmapi : MapsTo φ (interior S ∩ Metric.ball a r) (interior (flatClosedPatch q 1))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : Jet (KernelSpace n) ℝ hS α)
      (V : Jet (KernelSpace n) ℝ (convex_flatClosedPatch q 1) α),
      (∀ x ∈ S ∩ Metric.ball a r,
        extendValue α (jetValue (KernelSpace n) ℝ hS α J) x=flatJetValue q 1 α V (φ x)) →
      ∀ Z : ℝ, 0 ≤ Z →
      (∀ z ∈ flatClosedPatch q ρ, ‖flatJetFirst q 1 α V z‖ ≤ Z ∧ ‖flatJetSecond q 1 α V z‖ ≤ Z) →
      (∀ z ∈ flatClosedPatch q ρ, ∀ y ∈ flatClosedPatch q ρ,
        ‖flatJetFirst q 1 α V z-flatJetFirst q 1 α V y‖ ≤ Z*‖z-y‖^α) →
      (∀ z ∈ flatClosedPatch q ρ, ∀ y ∈ flatClosedPatch q ρ,
        ‖flatJetSecond q 1 α V z-flatJetSecond q 1 α V y‖ ≤ Z*‖z-y‖^α) →
      (∀ x ∈ S ∩ Metric.ball a r, ‖extendValue α (jetSecond (KernelSpace n) ℝ hS α J) x‖ ≤ C*Z) ∧
      (∀ x ∈ S ∩ Metric.ball a r, ∀ y ∈ S ∩ Metric.ball a r,
        ‖extendValue α (jetSecond (KernelSpace n) ℝ hS α J) x-extendValue α (jetSecond (KernelSpace n) ℝ hS α J) y‖ ≤ C*Z*‖x-y‖^α) := by
  let K := S ∩ Metric.closedBall a (2*r)
  have hKc : IsCompact K := hSc.inter_right Metric.isClosed_closedBall
  have hK : Convex ℝ K := hS.inter (convex_closedBall a (2*r))
  obtain ⟨C,hC,hbound⟩ := exists_chart_second_uniform_bounds hKc hK hα.le hα1 φ hφ hmap
  refine ⟨C,hC,?_⟩
  intro J V he Z hZ hb hD hH
  let D := flatJetFirst q 1 α V
  let B := flatJetSecond q 1 α V
  have hsub : S ∩ Metric.ball a r ⊆ K := inter_subset_inter_right S
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith : r ≤ 2*r)))
  have hsubT : flatClosedPatch q ρ ⊆ flatClosedPatch q 1 := fun z hz =>
    ⟨Metric.closedBall_subset_closedBall hρ1 hz.1,hz.2⟩
  have hmap1 : MapsTo φ (S ∩ Metric.ball a r) (flatClosedPatch q 1) := fun x hx => hsubT (hmap (hsub hx))
  obtain ⟨hBs,hBH⟩ := hbound D B Z hZ (fun z hz => (hb z hz).1) (fun z hz => (hb z hz).2) hD hH
  have hfirstc : ContinuousOn (chartFirst D φ) (S ∩ Metric.ball a r) := by
    exact ((continuousOn_extendValue α _).comp hφ.continuous.continuousOn hmap1).clm_comp
      (hφ.fderiv_right (m := ∞) (by simp)).continuous.continuousOn
  have hsecondc : ContinuousOn (chartSecond D B φ) (S ∩ Metric.ball a r) := by
    apply (continuousOn_of_holder_bound_general hα hBH).mono hsub
  have hrec := (jet_fields_recover_through_smooth_chart hS (convex_flatClosedPatch q 1)
    hSc.isClosed hint Metric.isOpen_ball hα J V φ hφ hmapi he hfirstc hsecondc).2
  constructor
  · intro x hx
    rw [hrec hx]
    exact hBs x (hsub hx)
  · intro x hx y hy
    rw [hrec hx,hrec hy]
    exact hBH x (hsub hx) y (hsub hy)

end GaussianTilt.MomentMapSchauder
