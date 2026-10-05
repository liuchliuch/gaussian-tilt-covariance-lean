import GaussianTilt.MomentMapLinearDirichletHolderHessian

/-! # Actual interior C²,α jet patches of the continuous weak representative

The Newtonian-plus-harmonic regularity endpoints are applied to the true
continuous representative, whose equality with the canonical mollified
representative is proved. The forcing exponent is retained exactly.
-/
noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Every interior point has a genuine same-exponent C²,α patch of the
actual continuous Poisson solution. The fields are literal Fréchet
derivatives, not assumed jets or an unrelated representative. -/
theorem exists_interior_jet_patch_of_continuous_weak_poisson [NeZero n]
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {u f : KernelSpace n→ℝ} (hu : Continuous u) (hf : Continuous f) (hfc : HasCompactSupport f)
    {α H : ℝ} (hα : 0<α) (hα1 : α<1) (hH : 0≤H)
    (hholder : ∀ x y,|f x-f y|≤H*‖x-y‖^α)
    (heq : ∀ ψ : KernelSpace n→ℝ,ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ⊆Ω →
      (∫ y,u y*kernelLaplacian ψ y)=∫ y,f y*ψ y) :
    ∀ x∈Ω,∃ r C : ℝ,0<r ∧ 0≤C ∧ Metric.closedBall x r⊆Ω ∧
      ContinuousOn (fderiv ℝ u) (Metric.closedBall x r) ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ u)) (Metric.closedBall x r) ∧
      (∀ y∈Metric.closedBall x r,HasFDerivAt u (fderiv ℝ u y) y) ∧
      (∀ y∈Metric.closedBall x r,HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) y) y) ∧
      (∀ y∈Metric.closedBall x r,∀ z∈Metric.closedBall x r,
        ‖fderiv ℝ (fderiv ℝ u) y-fderiv ℝ (fderiv ℝ u) z‖≤C*dist y z^α) := by
  obtain ⟨B,hB⟩ := hΩb.isCompact_closure.exists_bound_of_continuousOn hu.continuousOn
  have huB (x : KernelSpace n) (hx : x∈Ω) : |u x|≤B := hB x (subset_closure hx)
  have hc := harmonicRepresentative_classical_of_holder_distribution_poisson hΩ hΩb
    hu.locallyIntegrable huB hf hfc hα hα1 hH hholder heq
  have hHess := harmonicRepresentative_hessian_locally_holder hΩ hΩb
    hu.locallyIntegrable huB hf hfc hα hα1 hH hholder heq
  have hrep : EqOn (harmonicRepresentative u) u Ω :=
    harmonicRepresentative_eqOn_of_local_ae_eq hΩ hu (ae_of_all _ (fun _ _=>rfl))
  have he (y : KernelSpace n) (hy : y∈Ω) : harmonicRepresentative u=ᶠ[𝓝 y] u :=
    eventually_of_mem (hΩ.mem_nhds hy) hrep
  have huc (y : KernelSpace n) (hy : y∈Ω) : ContDiffAt ℝ 2 u y :=
    (hc.1 y hy).congr_of_eventuallyEq (he y hy).symm
  intro x hx
  obtain ⟨r₁,C,hr₁,hC,hholderH⟩ := hHess x hx
  obtain ⟨r₂,hr₂,hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx)
  let r := min r₁ r₂/2
  have hr : 0<r := by dsimp [r]; positivity
  have hr₁' : r<r₁ := by dsimp [r]; linarith [min_le_left r₁ r₂,lt_min hr₁ hr₂]
  have hr₂' : r<r₂ := by dsimp [r]; linarith [min_le_right r₁ r₂,lt_min hr₁ hr₂]
  have hsub : Metric.closedBall x r⊆Ω := (Metric.closedBall_subset_ball hr₂').trans hball
  have hsubH : Metric.closedBall x r⊆Metric.ball x r₁ := Metric.closedBall_subset_ball hr₁'
  refine ⟨r,C,hr,hC.le,hsub,?_,?_,?_,?_,?_⟩
  · intro y hy
    exact ((huc y (hsub hy)).fderiv_right (m:=1) (by norm_num)).continuousAt.continuousWithinAt
  · intro y hy
    exact (((huc y (hsub hy)).fderiv_right (m:=1) (by norm_num)).fderiv_right (m:=0) (by norm_num)).continuousAt.continuousWithinAt
  · intro y hy
    exact ((huc y (hsub hy)).differentiableAt (by norm_num)).hasFDerivAt
  · intro y hy
    exact (((huc y (hsub hy)).fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  · intro y hy z hz
    rw [← (he y (hsub hy)).fderiv.fderiv_eq,← (he z (hsub hz)).fderiv.fderiv_eq]
    simpa only [dist_eq_norm] using hholderH y (hsubH hy) z (hsubH hz)

/-- An open-ball version directly matches the local-field assumptions of
`JetPatchEmbedding`; the compact patch estimates above remain stronger. -/
theorem exists_open_interior_jet_patch_of_continuous_weak_poisson [NeZero n]
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {u f : KernelSpace n→ℝ} (hu : Continuous u) (hf : Continuous f) (hfc : HasCompactSupport f)
    {α H : ℝ} (hα : 0<α) (hα1 : α<1) (hH : 0≤H)
    (hholder : ∀ x y,|f x-f y|≤H*‖x-y‖^α)
    (heq : ∀ ψ : KernelSpace n→ℝ,ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ⊆Ω →
      (∫ y,u y*kernelLaplacian ψ y)=∫ y,f y*ψ y) :
    ∀ x∈Ω,∃ U : Set (KernelSpace n),IsOpen U ∧ x∈U ∧ U⊆Ω ∧
      ContinuousOn (fderiv ℝ u) U ∧ ContinuousOn (fderiv ℝ (fderiv ℝ u)) U ∧
      (∀ y∈U,HasFDerivAt u (fderiv ℝ u y) y) ∧
      (∀ y∈U,HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) y) y) ∧
      ∃ C : ℝ,0≤C ∧ ∀ y∈U,∀ z∈U,
        ‖fderiv ℝ (fderiv ℝ u) y-fderiv ℝ (fderiv ℝ u) z‖≤C*dist y z^α := by
  intro x hx
  obtain ⟨r,C,hr,hC,hs,hD,hH',hd,hdD,hh⟩ :=
    exists_interior_jet_patch_of_continuous_weak_poisson hΩ hΩb hu hf hfc hα hα1 hH hholder heq x hx
  exact ⟨Metric.ball x r,Metric.isOpen_ball,Metric.mem_ball_self hr,Metric.ball_subset_closedBall.trans hs,
    hD.mono Metric.ball_subset_closedBall,hH'.mono Metric.ball_subset_closedBall,
    fun y hy=>hd y (Metric.ball_subset_closedBall hy),fun y hy=>hdD y (Metric.ball_subset_closedBall hy),
    C,hC,fun y hy z hz=>hh y (Metric.ball_subset_closedBall hy) z (Metric.ball_subset_closedBall hz)⟩

end GaussianTilt.MomentMapLinearDirichlet
