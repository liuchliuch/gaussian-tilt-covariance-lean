import GaussianTilt.MomentMapLinearDirichletNaturalFullAllCenter
import GaussianTilt.MomentMapLinearDirichletCampanatoL2Local

/-! # Actual Hölder weak gradients from the natural variable-coefficient PDE -/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- The genuine first boundary regularity pass. The vector field is
constructed from literal mean-square estimates and is identified with the
actual weak gradient almost everywhere. -/
theorem exists_natural_weak_gradient_full_holder [NeZero n]
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
    ∃ s C : ℝ,0<s ∧ s≤R/4 ∧ 0≤C ∧ ∃ L : KernelSpace n → KernelSpace n,
      ContinuousOn L (Metric.closedBall 0 s ∩ {x|0≤x j}) ∧
      (∀ᵐx∂volume,‖x‖≤s → 0<x j → L x=euclideanWeakGradient u.1 x) ∧
      (∀x:KernelSpace n,‖x‖≤s → 0≤x j → ∀y:KernelSpace n,‖y‖≤s → 0≤y j →
        ‖L x-L y‖≤C*‖x-y‖^β) := by
  obtain ⟨s,C,hs,hsR,hC,hApp⟩ :=
    natural_all_center_full_campanato j hR hlam hΛ hD hβ hβ1 hA hΩ u hDomain hLoad hBnd hBounded heq
  have hApp' : ∀x:KernelSpace n,‖x‖≤s/4 → 0≤x j → ∀k:ℕ,∃q:KernelSpace n,
      (∫y in upperCampanatoBall j x (s*(1/2:ℝ)^k),‖euclideanWeakGradient u.1 y-q‖^2)≤
        C*(s*(1/2:ℝ)^k)^((n:ℝ)+2*β) := by
    intro x hx hxj k
    have hp : 0<s*(1/2:ℝ)^k := by positivity
    have hps : s*(1/2:ℝ)^k≤s := by
      exact mul_le_of_le_one_right hs.le (pow_le_one₀ (by norm_num) (by norm_num))
    exact hApp x hx hxj _ hp hps
  obtain ⟨L,hLc,hLAE,hLH⟩ := exists_holder_representative_of_local_l2_campanato j
    (euclideanWeakGradient u.1) ((euclideanWeakGradient_memLp u.1).restrict _) hs hC
    hβ hApp'
  refine ⟨s/4,max (campanatoL2HolderConstant n C β) 0,by positivity,
    by linarith,le_max_right _ _,L,hLc,hLAE,?_⟩
  intro x hx hxj y hy hyj
  exact (hLH x hx hxj y hy hyj).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))

end GaussianTilt.MomentMapLinearDirichlet
