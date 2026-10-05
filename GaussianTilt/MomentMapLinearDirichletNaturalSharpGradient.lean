import GaussianTilt.MomentMapLinearDirichletNaturalFullGradientHolder
import GaussianTilt.MomentMapLinearDirichletNaturalGradientHolder
import GaussianTilt.MomentMapLinearDirichletNaturalDataRestriction
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

/-- The sharp boundary Schauder first-derivative theorem follows from the
actual PDE alone: the initial continuous representative supplies bounded
energy, then a second genuine excess iteration recovers the full exponent. -/
theorem exists_natural_weak_gradient_sharp_holder [NeZero n]
    (j : Fin n) {R lam Λ D β : ℝ} (hR : 0<R) (hlam : 0<lam) (hΛ : 0≤Λ) (hD : 0≤D)
    (hβ : 0<β) (hβ1 : β<1) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {KA : ℝ}
    (hA : WeakBallCoefficientBounds A KA R lam Λ D β)
    {Ω : Set (CoordinateSpace n)} (hΩ : Ω⊆{x|0<x j}) (u : dirichletSobolev Ω)
    (hDomain : coordinateHalfBall j R⊆Ω)
    {F H : ℝ} {f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))}
    {G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))} {g : KernelSpace n → Fin n → ℝ}
    (hLoad : WeakHalfBallLoadBounds j R β F H f G g)
    (heq : ∀v:dirichletSobolev (coordinateHalfBall j R),
      variableJetEnergy A hA.measurable hA.nonneg hA.bound u.1 v.1=variableScalarVectorLoad (coordinateHalfBall j R) f G v) :
    ∃ s C : ℝ,0<s ∧ s≤R/4 ∧ 0≤C ∧ ∃ L : KernelSpace n → KernelSpace n,
      ContinuousOn L (Metric.closedBall 0 s ∩ {x|0≤x j}) ∧
      (∀ᵐx∂volume,‖x‖≤s → 0<x j → L x=euclideanWeakGradient u.1 x) ∧
      (∀x:KernelSpace n,‖x‖≤s → 0≤x j → ∀y:KernelSpace n,‖y‖≤s → 0≤y j →
        ‖L x-L y‖≤C*‖x-y‖^β) := by
  obtain ⟨s,C,hs,hsR,hC,L,hLc,hLAE,hLH⟩ :=
    exists_natural_weak_gradient_holder j hR hlam hΛ hD hβ hβ1.le hA hΩ u hDomain hLoad heq
  obtain ⟨B,hB,hBound⟩ := exists_weakGradient_bound_of_continuous_representative j u.1 hLc hLAE
  have hsR' : s≤R := by linarith
  have hA' := hA.mono_radius hsR'
  have hLoad' := hLoad.mono_radius hsR'
  have hDomain' : coordinateHalfBall j s⊆Ω := by
    intro x hx
    exact hDomain ⟨hx.1.trans_le hsR',hx.2⟩
  have heq' := weak_halfBall_equation_mono_radius hA u j hsR' f G heq
  obtain ⟨t,K,ht,hts,hK,W,hWc,hWAE,hWH⟩ := exists_natural_weak_gradient_full_holder
    j hs hlam hΛ hD hβ hβ1 hA' hΩ u hDomain' hLoad' hB hBound heq'
  exact ⟨t,K,ht,by linarith,hK,W,hWc,hWAE,hWH⟩

end GaussianTilt.MomentMapLinearDirichlet
