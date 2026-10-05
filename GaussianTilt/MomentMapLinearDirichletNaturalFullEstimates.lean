import GaussianTilt.MomentMapLinearDirichletNaturalData
import GaussianTilt.MomentMapLinearDirichletNaturalBoundedEnergy
import GaussianTilt.MomentMapLinearDirichletVariableBoundaryFullCenters
import GaussianTilt.MomentMapLinearDirichletVariableInteriorFullExponent
import GaussianTilt.MomentMapLinearDirichletBoundaryInteriorEnergyBridge

/-! # Natural coefficient/load data supply both genuine Campanato estimates -/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- All boundary-centered normal excess bounds follow from the literal
weak PDE and the natural coefficient/load records. -/
theorem natural_boundary_normal_full_excess [NeZero n]
    (j : Fin n) {R lam Λ D β : ℝ} (hR : 0<R) (hlam : 0<lam) (hΛ : 0≤Λ) (hD : 0≤D)
    (hβ : 0<β) (hβ1 : β<1) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {KA : ℝ}
    (hA : WeakBallCoefficientBounds A KA R lam Λ D β)
    {Ω : Set (CoordinateSpace n)} (hΩ : Ω⊆{x|0<x j}) (u : dirichletSobolev Ω)
    (hDomain : coordinateHalfBall j R⊆Ω)
    {F H : ℝ} {f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))}
    {G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))} {g : KernelSpace n → Fin n → ℝ}
    (hLoad : WeakHalfBallLoadBounds j R β F H f G g)
    {Bnd : ℝ} (hBnd : 0≤Bnd)
    (hBounded : ∀ᵐx∂volume,‖x‖<R → 0<x j → ‖euclideanWeakGradient u.1 x‖≤Bnd)
    (heq : ∀v:dirichletSobolev (coordinateHalfBall j R),
      variableJetEnergy A hA.measurable hA.nonneg hA.bound u.1 v.1=variableScalarVectorLoad (coordinateHalfBall j R) f G v) :
    ∃ r₀ C : ℝ,0<r₀ ∧ r₀≤R/2 ∧ 0≤C ∧ ∀z:KernelSpace n,‖z‖≤R/4 → z j=0 →
      ∀r:ℝ,0<r → r≤r₀ →
      (∫x in upperCampanatoBall j z r,‖euclideanWeakGradient u.1 x-
        normalMean (volume.restrict (upperCampanatoBall j z r)) j (euclideanWeakGradient u.1) •
          EuclideanSpace.basisFun (Fin n) ℝ j‖^2)≤C*r^((n:ℝ)+2*β) := by
  obtain ⟨r₀,C,N,hr₀,hr₀R,hC,hN,hBound⟩ :=
    exists_variable_boundary_center_full_exponent (n := n) hlam hΛ hD hβ hβ1 hR
  let M := Bnd^2*volume.real (Metric.ball (0:KernelSpace n) 1)
  have hM : 0≤M := by dsimp [M]; positivity
  let Q := M+N*(2*F+(n:ℝ)*H)^2
  have hQ : 0≤Q := by dsimp [Q]; positivity
  refine ⟨r₀,C*Q,hr₀,hr₀R,mul_nonneg hC.le hQ,?_⟩
  intro z hz hzj r hr hrr
  have hzR : ‖z‖≤R := by linarith
  exact hBound j Ω hΩ u hDomain z hz hzj M hM
    (fun r hr hrr=>bounded_weakGradient_upperBall_energy u.1 j hBnd hBounded z hr.le (by linarith)) A (A (dirichletCoordinateEquiv n z))
    (hA.positive z hzR) (hA.lower z hzR) (hA.upper z hzR) hA.measurable KA hA.nonneg hA.bound
    (hA.centered j z hzR) F H hLoad.scalar_nonneg hLoad.vector_nonneg f G (g z)
    hLoad.scalar_bound (hLoad.centered z hzR (by rw [hzj])) heq r hr hrr


/-- The full-exponent interior estimate retains the genuine normalized
initial excess, with no inverse-height loss. -/
theorem natural_interior_full_excess [NeZero n]
    (j : Fin n) {R lam Λ D β : ℝ} (hlam : 0<lam) (hΛ : 0≤Λ) (hD : 0≤D)
    (hβ : 0<β) (hβ1 : β<1) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {KA : ℝ}
    (hA : WeakBallCoefficientBounds A KA R lam Λ D β)
    {Ω : Set (CoordinateSpace n)} (u : dirichletSobolev Ω) (hDomain : coordinateHalfBall j R⊆Ω)
    {F H : ℝ} {f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))}
    {G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))} {g : KernelSpace n → Fin n → ℝ}
    (hLoad : WeakHalfBallLoadBounds j R β F H f G g)
    {Bnd : ℝ} (hBnd : 0≤Bnd)
    (hBounded : ∀ᵐx∂volume,‖x‖<R → 0<x j → ‖euclideanWeakGradient u.1 x‖≤Bnd)
    (heq : ∀v:dirichletSobolev (coordinateHalfBall j R),
      variableJetEnergy A hA.measurable hA.nonneg hA.bound u.1 v.1=variableScalarVectorLoad (coordinateHalfBall j R) f G v) :
    ∃C N:ℝ,0<C ∧ 0<N ∧ ∀(a:KernelSpace n)(r:ℝ),‖a‖≤R → 0≤a j → 0<r → r≤1 →
      coordinateFullBall a r⊆coordinateHalfBall j R →
      ∀s:ℝ,0<s → s≤r → ballGradientExcess u.1 a s≤
        C*(ballGradientExcess u.1 a r/r^((n:ℝ)+2*β)+
          Bnd^2*volume.real (Metric.ball (0:KernelSpace n) 1)+N*(2*F+(n:ℝ)*H)^2)*s^((n:ℝ)+2*β) := by
  obtain ⟨C,N,hC,hN,hInterior⟩ := exists_variable_ball_full_exponent_all_radii (n:=n) hlam hΛ hD hβ hβ1
  refine ⟨C,N,hC,hN,?_⟩
  intro a r ha haj hr hr1 hsub s hs hsr
  have hDb := hA.centered j a ha
  have hGb := hLoad.centered a ha haj
  have hDb' : ∀i k,∀ᵐx∂volume,x∈coordinateFullBall a r →
      |A (dirichletCoordinateEquiv n a) i k-A x i k|≤D*‖(dirichletCoordinateEquiv n).symm x-a‖^β := by
    intro i k
    filter_upwards [hDb i k] with x hx hxr
    exact hx (hsub hxr)
  have hG' : ∀i,∀ᵐx∂volume,x∈coordinateFullBall a r →
      |G i x-g a i|≤H*‖(dirichletCoordinateEquiv n).symm x-a‖^β := by
    intro i
    filter_upwards [hGb i] with x hx hxr
    exact hx (hsub hxr)
  have hf' : ∀ᵐx∂volume,x∈coordinateFullBall a r → |f x|≤F := by
    filter_upwards [hLoad.scalar_bound] with x hx hxr
    exact hx (hsub hxr)
  have heq' : ∀v:dirichletSobolev (coordinateFullBall a r),
      variableJetEnergy A hA.measurable hA.nonneg hA.bound u.1 v.1=variableScalarVectorLoad (coordinateFullBall a r) f G v := by
    intro v
    have hh:=heq (dirichletInclusion hsub v)
    rw [variableScalarVectorLoad_apply,dirichletInclusion_value] at hh
    rw [variableScalarVectorLoad_apply]
    exact hh
  have hEnergy : ∀t:ℝ,0<t → t≤r → ballGradientEnergy u.1 a t≤
      (Bnd^2*volume.real (Metric.ball (0:KernelSpace n) 1))*t^n := by
    intro t ht htr
    apply bounded_weakGradient_ball_energy u.1 j hBnd hBounded a ht.le
    intro x hx
    have hh:=hsub (show dirichletCoordinateEquiv n x∈coordinateFullBall a r from by
      change (dirichletCoordinateEquiv n).symm (dirichletCoordinateEquiv n x)∈Metric.ball a r
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact Metric.ball_subset_ball htr hx)
    exact ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hh.1,hh.2⟩
  exact hInterior a r hr hr1 Ω u (hsub.trans hDomain)
    (Bnd^2*volume.real (Metric.ball (0:KernelSpace n) 1)) (by positivity) hEnergy
    A (A (dirichletCoordinateEquiv n a)) (hA.positive a ha) (hA.lower a ha) (hA.upper a ha)
    hA.measurable KA hA.nonneg hA.bound hDb' F H hLoad.scalar_nonneg hLoad.vector_nonneg f G (g a)
    hf' hG' heq' s hs hsr

end GaussianTilt.MomentMapLinearDirichlet
