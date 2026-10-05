import GaussianTilt.MomentMapLinearDirichletNaturalGradientHolder
import GaussianTilt.MomentMapLinearDirichletWeakGradientClassicalVector
import GaussianTilt.MomentMapLinearDirichletH1ReflectedGradient

/-! # Actual classical derivatives of continuous representatives of the weak solution -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- The actual Sobolev integration-by-parts identity transfers to a local
continuous value representative. No weak-derivative identity is supplied. -/
lemma continuous_representative_weak_gradient_identity
    {Ω : Set (CoordinateSpace n)} (u : dirichletSobolev Ω)
    {V : Set (KernelSpace n)} {v : KernelSpace n → ℝ}
    (hAE : ∀ᵐx∂volume,x∈V → v x=dirichletValue Ω u (dirichletCoordinateEquiv n x))
    (i : Fin n) {ψ : KernelSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψV : tsupport ψ⊆V) :
    (∫x,v x*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x)=
      -(∫x,euclideanWeakGradient u.1 x i*ψ x) := by
  have hh:=dirichletSobolev_physical_integration_by_parts u i hψ hψc
  have he : (∫x,v x*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x)=
      ∫x,dirichletValue Ω u (dirichletCoordinateEquiv n x)*
        kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x := by
    apply integral_congr_ae
    filter_upwards [hAE] with x hx
    by_cases hxs:x∈tsupport ψ
    · rw [hx (hψV hxs)]
    · rw [kernelDerivative_zero_off_tsupport ψ _ hxs,mul_zero,mul_zero]
  rw [he]
  change (∫x,dirichletValue Ω u (dirichletCoordinateEquiv n x)*
    kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x)=
      -(∫x,u.1 i.succ (dirichletCoordinateEquiv n x)*ψ x)
  linarith

/-- Continuous representatives of the actual value and weak gradient have
true first derivatives. -/
theorem classical_gradient_of_h1_continuous_representatives
    {Ω : Set (CoordinateSpace n)} (u : dirichletSobolev Ω)
    {V : Set (KernelSpace n)} (hV : IsOpen V) {v : KernelSpace n → ℝ}
    {L : KernelSpace n → KernelSpace n} (hv : ContinuousOn v V) (hL : ContinuousOn L V)
    (hvAE : ∀ᵐx∂volume,x∈V → v x=dirichletValue Ω u (dirichletCoordinateEquiv n x))
    (hLAE : ∀ᵐx∂volume,x∈V → L x=euclideanWeakGradient u.1 x) :
    ContDiffOn ℝ 1 v V ∧ ∀x∈V,HasFDerivAt v (innerSL ℝ (L x)) x := by
  apply classical_gradient_of_continuous_ae_weak_gradient hV hv hL hLAE
  intro i ψ hψ hψc hψV
  exact continuous_representative_weak_gradient_identity u hvAE i hψ hψc hψV

/-- Continuous representatives of a Sobolev value and gradient on a
closed convex body give the true within-boundary derivative as well. -/
theorem within_gradient_of_h1_continuous_representatives
    {Ω : Set (CoordinateSpace n)} (u : dirichletSobolev Ω)
    {S : Set (KernelSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S)
    (hint : (interior S).Nonempty) {v : KernelSpace n → ℝ}
    {L : KernelSpace n → KernelSpace n} (hv : ContinuousOn v S) (hL : ContinuousOn L S)
    (hvAE : ∀ᵐx∂volume,x∈interior S → v x=dirichletValue Ω u (dirichletCoordinateEquiv n x))
    (hLAE : ∀ᵐx∂volume,x∈interior S → L x=euclideanWeakGradient u.1 x)
    {x : KernelSpace n} (hx : x∈S) : HasFDerivWithinAt v (innerSL ℝ (L x)) S x := by
  apply hasFDerivWithinAt_of_continuous_weak_gradient_vector hS hSc hint hv hL _ hx
  intro i ψ hψ hψc hψS
  rw [continuous_representative_weak_gradient_identity u hvAE i hψ hψc hψS]
  congr 1
  apply integral_congr_ae
  filter_upwards [hLAE] with y hy
  by_cases hys:y∈tsupport ψ
  · rw [hy (hψS hys)]
  · rw [image_eq_zero_of_notMem_tsupport hys,mul_zero,mul_zero]

/-- The literal natural weak PDE gives a true C¹ representative and a
Hölder continuous gradient up to the flat boundary, whenever the already
constructed value representative is continuous. -/
theorem exists_natural_classical_gradient_holder [NeZero n]
    (j : Fin n) {R lam Λ D β : ℝ} (hR : 0<R) (hlam : 0<lam) (hΛ : 0≤Λ) (hD : 0≤D)
    (hβ : 0<β) (hβ1 : β≤1) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {KA : ℝ}
    (hA : WeakBallCoefficientBounds A KA R lam Λ D β)
    {Ω : Set (CoordinateSpace n)} (hΩ : Ω⊆{x|0<x j}) (u : dirichletSobolev Ω)
    (hDomain : coordinateHalfBall j R⊆Ω)
    {F H : ℝ} {f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))}
    {G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))} {g : KernelSpace n → Fin n → ℝ}
    (hLoad : WeakHalfBallLoadBounds j R β F H f G g)
    (heq : ∀v:dirichletSobolev (coordinateHalfBall j R),
      variableJetEnergy A hA.measurable hA.nonneg hA.bound u.1 v.1=variableScalarVectorLoad (coordinateHalfBall j R) f G v)
    {v : KernelSpace n → ℝ} (hv : ContinuousOn v (upperCampanatoBall j 0 R))
    (hvAE : ∀ᵐx∂volume,x∈upperCampanatoBall j 0 R →
      v x=dirichletValue Ω u (dirichletCoordinateEquiv n x)) :
    ∃s C:ℝ,0<s ∧ s≤R/4 ∧ 0≤C ∧ ∃L:KernelSpace n→KernelSpace n,
      ContinuousOn L (Metric.closedBall 0 s∩{x|0≤x j}) ∧
      (∀ᵐx∂volume,‖x‖≤s → 0<x j → L x=euclideanWeakGradient u.1 x) ∧
      (∀x:KernelSpace n,‖x‖≤s → 0≤x j → ∀y:KernelSpace n,‖y‖≤s → 0≤y j →
        ‖L x-L y‖≤C*‖x-y‖^(β/2)) ∧
      ContDiffOn ℝ 1 v (upperCampanatoBall j 0 s) ∧
      (∀x∈upperCampanatoBall j 0 s,HasFDerivAt v (innerSL ℝ (L x)) x) := by
  obtain ⟨s,C,hs,hsR,hC,L,hLc,hLAE,hLH⟩ :=
    exists_natural_weak_gradient_holder j hR hlam hΛ hD hβ hβ1 hA hΩ u hDomain hLoad heq
  have hsub : upperCampanatoBall j 0 s⊆upperCampanatoBall j 0 R := by
    apply upperCampanatoBall_mono
    simp only [dist_self,zero_add]
    linarith
  have hclosed : upperCampanatoBall j 0 s⊆Metric.closedBall 0 s∩{x|0≤x j} :=
    fun x hx=>⟨Metric.ball_subset_closedBall hx.1,show 0≤x j from hx.2.le⟩
  have hAEv : ∀ᵐx∂volume,x∈upperCampanatoBall j 0 s →
      v x=dirichletValue Ω u (dirichletCoordinateEquiv n x) := by
    filter_upwards [hvAE] with x hx hxs
    exact hx (hsub hxs)
  have hAEL : ∀ᵐx∂volume,x∈upperCampanatoBall j 0 s → L x=euclideanWeakGradient u.1 x := by
    filter_upwards [hLAE] with x hx hxs
    have hn : ‖x‖<s := by simpa only [Metric.mem_ball,dist_zero_right] using hxs.1
    exact hx hn.le hxs.2
  obtain ⟨hc,hd⟩ := classical_gradient_of_h1_continuous_representatives u
    (isOpen_upperCampanatoBall j 0 s) (hv.mono hsub) (hLc.mono hclosed) hAEv hAEL
  exact ⟨s,C,hs,hsR,hC,L,hLc,hLAE,hLH,hc,hd⟩

end GaussianTilt.MomentMapLinearDirichlet
