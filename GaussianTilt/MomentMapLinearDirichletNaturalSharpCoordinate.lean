import GaussianTilt.MomentMapLinearDirichletNaturalSharpGradient
import GaussianTilt.MomentMapLinearDirichletVariableWeakFinitePatches

/-! # The actual PDE Campanato field in boundary-recovery coordinates -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000

/-- The natural weak equation constructs a continuous raw-coordinate
Hölder gradient representative on a genuine closed boundary patch. -/
theorem exists_natural_coordinate_gradient_sharp_holder [NeZero n]
    (j:Fin n) {R lam Λ D β:ℝ} (hR:0<R) (hlam:0<lam) (hΛ:0≤Λ) (hD:0≤D)
    (hβ:0<β) (hβ1:β<1) {A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {KA:ℝ}
    (hA:WeakBallCoefficientBounds A KA R lam Λ D β)
    {Ω:Set (CoordinateSpace n)} (hΩ:Ω⊆{x|0<x j}) (u:dirichletSobolev Ω)
    (hDomain:coordinateHalfBall j R⊆Ω)
    {F H:ℝ} {f:Lp ℝ 2 (volume:Measure (CoordinateSpace n))}
    {G:Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n))} {g:KernelSpace n → Fin n → ℝ}
    (hLoad:WeakHalfBallLoadBounds j R β F H f G g)
    (heq:∀v:dirichletSobolev (coordinateHalfBall j R),
      variableJetEnergy A hA.measurable hA.nonneg hA.bound u.1 v.1=variableScalarVectorLoad (coordinateHalfBall j R) f G v) :
    ∃s:ℝ,0<s ∧ s≤R/4 ∧ ∃Q:CoordinateSpace n → CoordinateSpace n,
      BoundedHolderOn β Q (coordinateClosedHalfBall j s) ∧
      ContinuousOn Q (coordinateClosedHalfBall j s) ∧
      ∀i,∀ᵐx∂volume,x∈coordinateHalfBall j s → Q x i=u.1 i.succ x := by
  obtain ⟨s,C,hs,hsR,hC,L,hLc,hLAE,hLH⟩ :=
    exists_natural_weak_gradient_sharp_holder j hR hlam hΛ hD hβ hβ1 hA hΩ u hDomain hLoad heq
  have hSc:IsCompact (Metric.closedBall (0:KernelSpace n) s ∩ {x|0≤x j}) :=
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const (PiLp.proj 2 (𝕜:=ℝ) (fun _:Fin n=>ℝ) j).continuous)
  have hHolder:∀x∈Metric.closedBall (0:KernelSpace n) s ∩ {x|0≤x j},
      ∀y∈Metric.closedBall (0:KernelSpace n) s ∩ {x|0≤x j},‖L x-L y‖≤C*‖x-y‖^β := by
    intro x hx y hy
    exact hLH x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx.1) hx.2
      y (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy.1) hy.2
  have hAE:∀ᵐx∂(volume:Measure (KernelSpace n)),x∈upperCampanatoBall j 0 s → L x=euclideanWeakGradient u.1 x := by
    filter_upwards [hLAE] with x hx hxU
    exact hx (show ‖x‖≤s from (show ‖x‖<s by simpa only [Metric.mem_ball,dist_zero_right] using hxU.1).le) hxU.2
  obtain ⟨Q,hQH,hQc,hQAE,hQval⟩ := exists_coordinate_holder_weak_gradient u.1 hSc hLc
    hβ.le hC hHolder hAE
  refine ⟨s,hs,hsR,Q,?_,?_,?_⟩
  · simpa only [← coordinateClosedHalfBall_eq_preimage] using hQH
  · simpa only [← coordinateClosedHalfBall_eq_preimage] using hQc
  · intro i
    filter_upwards [hQAE i] with x hx hxU
    exact hx (by simpa only [coordinateHalfBall_eq_preimage_upper,mem_preimage] using hxU)

end GaussianTilt.MomentMapLinearDirichlet
