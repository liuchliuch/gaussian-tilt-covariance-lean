import GaussianTilt.MomentMapRegularityReferenceTranslation
import GaussianTilt.MomentMapRegularitySecondOrderDirichletExistence

/-! # Building smooth unit-density references from actual classical inner solvers -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 1000

/-- A classical solver on the genuinely constructed smooth strongly convex
inner domains supplies smoothness of the already constructed weak Dirichlet
solution on every compact convex full-dimensional body. The limit passage,
true Hessian equation and local smooth bootstrap are all discharged here. -/
theorem smooth_reference_of_classical_inner_solver [NeZero n]
    (hsolve : ∀ (S:Set (E n)) (d:SmoothInnerDomain S ∅),
      ∃ v : E n → ℝ, Continuous v ∧ ContDiffOn ℝ ∞ v (interior d.body) ∧ ConvexOn ℝ d.body v ∧
        (∀ x∈frontier d.body, v x=0) ∧
        (∀ x∈interior d.body, (coordinateHessian (coordinatePullback v) (coordinateEquiv n x)).PosDef) ∧
        ∀ x∈interior d.body, (coordinateHessian (coordinatePullback v) (coordinateEquiv n x)).det=1)
    {S:Set (E n)} (hS : IsCompact S) (hSc : Convex ℝ S) (hi : (interior S).Nonempty)
    {u:E n → ℝ} (huc : Continuous u) (huconv : ConvexOn ℝ S u)
    (hub : ∀ x∈frontier S, u x=0)
    (huMA : ∀ A, IsCompact A → A⊆interior S → volume (subgradientImageOn S u A)=volume A) :
    ContDiffOn ℝ ∞ u (interior S) := by
  intro x hx
  let D : Set (E n) := (fun y=>y+x) ⁻¹' S
  let w : E n → ℝ := fun y=>u (y+x)
  have hD : IsCompact D := (Homeomorph.addRight x).isCompact_preimage.mpr hS
  have hwconv : ConvexOn ℝ D w := convexOn_translation_preimage huconv x
  have hwc : Continuous w := huc.comp (continuous_id.add continuous_const)
  have hDi : (0:E n)∈interior D := by
    have he := (Homeomorph.addRight x).preimage_interior S
    change (fun y:E n=>y+x) ⁻¹' interior S=interior D at he
    rw [← he]
    simpa using hx
  have hwb : ∀ y∈frontier D, w y=0 := by
    intro y hy
    have he := (Homeomorph.addRight x).preimage_frontier S
    change (fun y:E n=>y+x) ⁻¹' frontier S=frontier D at he
    rw [← he] at hy
    exact hub (y+x) hy
  have hwMA : ∀ A, IsCompact A → A⊆interior D → volume (subgradientImageOn D w A)=volume A :=
    unit_alexandrov_translation huMA x
  obtain ⟨d,_,_,hdex⟩ := exists_smoothInnerDomain_exhaustion hD hwconv.1 ⟨0,hDi⟩
  have hsolutions (k:ℕ) := hsolve D (d k)
  choose v hvc hvs hvv hvb hvH hvMA using hsolutions
  obtain ⟨r,hr,hrD⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hDi)
  have hrclosed : Metric.closedBall (0:E n) (r/2)⊆interior D :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrD
  obtain ⟨B,hB⟩ := hD.exists_bound_of_continuousOn (continuous_id.continuousOn)
  have hDbound : D⊆Metric.closedBall (0:E n) (max B 0) := by
    intro y hy
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (hB y hy).trans (le_max_left _ _)
  have hsmooth := reference_contDiffOn_infty_of_classical_inner_references hD
    ⟨0,interior_subset hDi⟩ hwc hwconv hwb hwMA d hdex v hvc hvs hvv hvb hvH hvMA
    (half_pos hr) (le_max_right B 0) hDbound hrclosed
  have hw0 : ContDiffAt ℝ ∞ w (0:E n) := hsmooth.contDiffAt (Metric.ball_mem_nhds _ (by positivity))
  have hwx : ContDiffAt ℝ ∞ w (x-x) := by simpa only [sub_self] using hw0
  have htrans : ContDiffAt ℝ ∞ (fun y:E n=>y-x) x := contDiffAt_id.sub contDiffAt_const
  have hcomp := hwx.comp (f:=fun y:E n=>y-x) x htrans
  have huAt : ContDiffAt ℝ ∞ u x := by simpa only [Function.comp_def,w,sub_add_cancel] using hcomp
  exact huAt.contDiffWithinAt

/-- The actual weak Dirichlet solution is constructed variationally first;
classical inner-domain solvability then makes it a smooth reference. -/
theorem exists_smooth_unit_reference_of_classical_inner_solver [NeZero n]
    (hsolve : ∀ (S:Set (E n)) (d:SmoothInnerDomain S ∅),
      ∃ v : E n → ℝ, Continuous v ∧ ContDiffOn ℝ ∞ v (interior d.body) ∧ ConvexOn ℝ d.body v ∧
        (∀ x∈frontier d.body, v x=0) ∧
        (∀ x∈interior d.body, (coordinateHessian (coordinatePullback v) (coordinateEquiv n x)).PosDef) ∧
        ∀ x∈interior d.body, (coordinateHessian (coordinatePullback v) (coordinateEquiv n x)).det=1)
    (S:Set (E n)) (hS : IsCompact S) (hSc : Convex ℝ S) (hi : (interior S).Nonempty) :
    ∃ u:E n → ℝ, Continuous u ∧ ContDiffOn ℝ ∞ u (interior S) ∧ ConvexOn ℝ S u ∧
      (∀ x∈frontier S, u x=0) ∧
      ∀ A, IsCompact A → A⊆interior S → volume (subgradientImageOn S u A)=volume A := by
  obtain ⟨u,huc,hconv,hb,hMA⟩ := exists_unit_density_alexandrov_dirichlet hS hSc hi
  exact ⟨u,huc,smooth_reference_of_classical_inner_solver hsolve hS hSc hi huc hconv hb hMA,hconv,hb,hMA⟩

end GaussianTilt.MomentMapRegularity
