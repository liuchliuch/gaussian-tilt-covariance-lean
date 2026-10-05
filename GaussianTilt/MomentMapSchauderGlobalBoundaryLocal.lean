import GaussianTilt.MomentMapSchauderGlobalBoundaryTarget
import GaussianTilt.MomentMapSchauderGlobalPhysicalRecovery
import GaussianTilt.MomentMapClassicalDirichletGeometryDomains

/-! # Physical boundary Schauder estimates on actual smooth convex domains -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 3000000
open Set Filter Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.HolderSpace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- The local physical boundary estimate for arbitrary zero-boundary
jets. The genuine inverse chart, transferred PDE, one-sided absorption,
and physical closed Hessian recovery are all constructed in the proof. -/
theorem exists_smooth_domain_boundary_local_estimate [NeZero n]
    {I : Type*} [TopologicalSpace I] {P : Set I} (hP : IsCompact P)
    {S₀ A₀ : Set (KernelSpace n)} (d : SmoothInnerDomain S₀ A₀)
    {α M K : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (a : KernelSpace n) (ha : d.defining a=0) (q : Fin n)
    (hq : fderiv ℝ d.defining a (EuclideanSpace.basisFun (Fin n) ℝ q)≠0)
    (A : I → KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAt : ContinuousOn (fun t => A t a) P) (hA0 : ∀ t ∈ P, (A t a).PosDef)
    (hAs : ∀ t ∈ P, ∀ x ∈ d.body, (A t x).IsSymm)
    (hAb : ∀ t ∈ P, ∀ x ∈ d.body, ∀ i k, |A t x i k| ≤ M)
    (hAH : ∀ t ∈ P, ∀ x ∈ d.body, ∀ y ∈ d.body, ∀ i k, |A t x i k-A t y i k| ≤ K*‖x-y‖^α) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ t ∈ P, ∀ J : zeroBoundary (KernelSpace n) ℝ d.convex_body α,
      ∀ (f : KernelSpace n → ℝ) (U F H : ℝ), 0 ≤ U → 0 ≤ F → 0 ≤ H →
      (∀ x : d.body, |value d.body ℝ α (jetValue (KernelSpace n) ℝ d.convex_body α J.1) x| ≤ U) →
      (∀ x ∈ d.body, |f x| ≤ F) →
      (∀ x ∈ d.body, ∀ y ∈ d.body, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ interior d.body, euclideanEllipticOperator (A t x)
        (extendValue α (jetValue (KernelSpace n) ℝ d.convex_body α J.1)) x=f x) →
      (∀ x ∈ d.body ∩ Metric.ball a r,
        ‖extendValue α (jetSecond (KernelSpace n) ℝ d.convex_body α J.1) x‖ ≤ C*(U+F+H)+ε*‖J‖) ∧
      (∀ x ∈ d.body ∩ Metric.ball a r, ∀ y ∈ d.body ∩ Metric.ball a r,
        ‖extendValue α (jetSecond (KernelSpace n) ℝ d.convex_body α J.1) x-
          extendValue α (jetSecond (KernelSpace n) ℝ d.convex_body α J.1) y‖ ≤
            (C*(U+F+H)+ε*‖J‖)*‖x-y‖^α) := by
  obtain ⟨s,ψ,hs,hs1,hψ,hψ0,hgerm,hlevel,hright,hsource,hleft⟩ :=
    exists_global_euclidean_boundary_chart d.smooth a q hq
  have hint : (interior d.body).Nonempty := by
    rw [d.interior_body]
    exact d.negative_nonempty
  have hInt : interior {x | d.defining x ≤ 0}={x | d.defining x < 0} := d.interior_body
  have hmap : MapsTo ψ (flatClosedPatch q 1) d.body := boundary_inverse_maps_halfball hs ha hlevel
  have hmapi : MapsTo ψ (interior (flatClosedPatch q 1)) (interior d.body) :=
    boundary_inverse_maps_interior hs ha hlevel hInt
  have hplane : ∀ z ∈ flatClosedPatch q 1, z q=0 → ψ z ∈ frontier d.body :=
    fun z hz hzq => boundary_inverse_plane_mem_frontier d.smooth.continuous ha hlevel hInt hz hzq
  obtain ⟨ρ,hρ,hρ1,htarget⟩ := exists_boundary_target_fields_small_highest hP d.convex_body d.compact_sublevel.isClosed
    (regularLevelFlatteningChart d.smooth a q hq).open_source hα hα1 hM hK
    d.smooth a q hq hs ψ hψ hψ0 hmap hmapi hplane hsource hright hleft A hAt hA0 hAs hAb hAH
  obtain ⟨r,hr,hrsource,hrnorm,hrmap,hrmapi⟩ :=
    exists_physical_boundary_patch d.smooth a q hq hs hρ ha hInt
  have hρle : ρ ≤ 1 := by linarith
  have hsub : flatClosedPatch q ρ ⊆ flatClosedPatch q 1 := fun z hz =>
    ⟨Metric.closedBall_subset_closedBall hρle hz.1,hz.2⟩
  have hball : Metric.ball a r ⊆ Metric.closedBall a (2*r) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hmapI : MapsTo (scaledFlatteningMap d.defining a q s) (interior d.body ∩ Metric.ball a r)
      (interior (flatClosedPatch q 1)) := fun x hx => interior_mono hsub (hrmapi ⟨hx.1,hball hx.2⟩)
  obtain ⟨Cr,hCr,hrecover⟩ := exists_physical_hessian_recovery_bound d.convex_body d.compact_sublevel hint hα hα1.le q a hr hρle
    (scaledFlatteningMap d.defining a q s) (contDiff_scaledFlatteningMap d.smooth a q s) hrmap hmapI
  refine ⟨r,hr,?_⟩
  intro ε hε
  let η := ε/(Cr+1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨Ct,hCt,ht⟩ := htarget η hη
  let C := Cr*Ct+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro t htP J f U F H hU hF hH hu hf hfH heq
  obtain ⟨V,hVu,hVb,hVD,hVH⟩ := ht t htP J f U F H hU hF hH hu hf hfH heq
  have heValue : ∀ x ∈ d.body ∩ Metric.ball a r,
      extendValue α (jetValue (KernelSpace n) ℝ d.convex_body α J.1) x=
        flatJetValue q 1 α V (scaledFlatteningMap d.defining a q s x) := by
    intro x hx
    have hxp : scaledFlatteningMap d.defining a q s x ∈ flatClosedPatch q 1 := hsub (hrmap ⟨hx.1,hball hx.2⟩)
    rw [show flatJetValue q 1 α V (scaledFlatteningMap d.defining a q s x)=
      value (flatClosedPatch q 1) ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch q 1) α V)
        ⟨scaledFlatteningMap d.defining a q s x,hxp⟩ from extendValue_mem α _ hxp,hVu]
    rw [hleft x (hrsource (hball hx.2)) ((hrnorm x (hball hx.2)).le.trans hρle)]
  let Z := Ct*(U+F+H)+η*‖J‖
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  obtain ⟨hb,hHh⟩ := hrecover J.1 V heValue Z hZ hVb hVD hVH
  have hηCr : Cr*η ≤ ε := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < Cr+1)).mpr
    nlinarith
  have htotal : Cr*Z ≤ C*(U+F+H)+ε*‖J‖ := by
    have hsmall := mul_le_mul_of_nonneg_right hηCr (norm_nonneg J)
    have hdata : Cr*Ct*(U+F+H) ≤ C*(U+F+H) :=
      mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
    dsimp only [Z]
    nlinarith only [hsmall,hdata]
  exact ⟨fun x hx => (hb x hx).trans htotal,
    fun x hx y hy => (hHh x hx y hy).trans (mul_le_mul_of_nonneg_right htotal (Real.rpow_nonneg (norm_nonneg _) α))⟩

end GaussianTilt.MomentMapSchauder
