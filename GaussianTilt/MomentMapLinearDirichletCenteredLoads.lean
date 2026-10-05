import GaussianTilt.MomentMapLinearDirichletRestrictedReplacement
import GaussianTilt.MomentMapLinearDirichletVariableLoads

/-! # Actual cancellation and centering of constant divergence loads -/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Every actual H₀¹ derivative has zero integral on its bounded domain.
The proof uses a constructed compact test equal to one on the domain,
actual weak integration by parts, and the proved zero extension. -/
theorem dirichletGradient_integral_eq_zero {Ω : Set (CoordinateSpace n)}
    (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω)
    (u : dirichletSobolev Ω) (i : Fin n) : (∫ x in Ω, u.1 i.succ x) = 0 := by
  obtain ⟨R,hR,hΩR⟩ := hΩb.subset_ball_lt 0 (0 : CoordinateSpace n)
  let η : ContDiffBump (0 : CoordinateSpace n) := ⟨R,R+1,hR,by linarith⟩
  let ψ : smoothCompactCore n := ⟨η,η.contDiff,η.hasCompactSupport⟩
  have hη : ∀ x ∈ Ω, η x=1 := fun x hx => η.one_of_mem_closedBall (Metric.ball_subset_closedBall (hΩR hx))
  have hDη : ∀ x ∈ Ω, coordinateDerivative i ψ.1 x=0 := by
    intro x hx
    have he : (η : CoordinateSpace n → ℝ) =ᶠ[𝓝 x] (fun _ => 1) := η.eventuallyEq_one_of_mem_ball (hΩR hx)
    change fderiv ℝ (η : CoordinateSpace n → ℝ) x (Pi.single i 1) = 0
    rw [he.fderiv_eq]
    simp
  have hpair := dirichletSobolev_integration_by_parts u i ψ
  rw [inner_Lp_smoothCompactToL2,inner_Lp_smoothCompactToL2] at hpair
  have hz0 : ∀ᵐ x ∂volume, x ∉ Ω → u.1 0 x=0 := dirichletValue_ae_zero_outside hΩm u
  have hzD := dirichletGradient_ae_zero_outside hΩm u i
  have hright : (∫ x, u.1 0 x*(smoothCompactDerivative i ψ).1 x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hz0] with x hx
    change u.1 0 x*coordinateDerivative i ψ.1 x=0
    by_cases hxΩ : x ∈ Ω
    · rw [hDη x hxΩ,mul_zero]
    · rw [hx hxΩ,zero_mul]
  rw [hright,neg_zero] at hpair
  have hleft : (∫ x, u.1 i.succ x*ψ.1 x) = ∫ x in Ω,u.1 i.succ x := by
    rw [← integral_indicator hΩm]
    apply integral_congr_ae
    filter_upwards [hzD] with x hx
    by_cases hxΩ : x ∈ Ω
    · rw [indicator_of_mem hxΩ]
      change u.1 i.succ x*η x=u.1 i.succ x
      rw [hη x hxΩ,mul_one]
    · rw [indicator_of_notMem hxΩ,hx hxΩ,zero_mul]
  exact hleft.symm.trans hpair

def constantDomainL2 (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (hfin : (volume : Measure (CoordinateSpace n)) Ω ≠ (∞ : ℝ≥0∞)) (c : ℝ) : Lp ℝ 2 (volume : Measure (CoordinateSpace n)) :=
  (memLp_indicator_const 2 hΩ c (Or.inr hfin)).toLp (Ω.indicator (fun _ => c))

lemma constantDomainL2_ae (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (hfin : (volume : Measure (CoordinateSpace n)) Ω ≠ (∞ : ℝ≥0∞)) (c : ℝ) : constantDomainL2 Ω hΩ hfin c =ᵐ[volume] Ω.indicator (fun _ => c) :=
  (memLp_indicator_const 2 hΩ c (Or.inr hfin)).coeFn_toLp

/-- Actual constant divergence loads vanish on the genuine H₀¹ space. -/
theorem inner_constantDomainL2_gradient_eq_zero {Ω : Set (CoordinateSpace n)}
    (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) (hfin : (volume : Measure (CoordinateSpace n)) Ω ≠ (∞ : ℝ≥0∞))
    (u : dirichletSobolev Ω) (i : Fin n) (c : ℝ) :
    inner ℝ (constantDomainL2 Ω hΩm hfin c) (u.1 i.succ) = 0 := by
  have he : inner ℝ (constantDomainL2 Ω hΩm hfin c) (u.1 i.succ) =
      c*(∫ x in Ω,u.1 i.succ x) := by
    rw [L2.inner_def,← integral_const_mul,← integral_indicator hΩm]
    apply integral_congr_ae
    filter_upwards [constantDomainL2_ae Ω hΩm hfin c] with x hx
    rw [hx]
    by_cases hxΩ : x ∈ Ω
    · simp only [indicator_of_mem hxΩ,RCLike.inner_apply,conj_trivial]
      ring
    · simp only [indicator_of_notMem hxΩ,inner_zero_left]
  rw [he,dirichletGradient_integral_eq_zero hΩm hΩb,mul_zero]

/-- The literal scalar/vector load is unchanged by subtracting any
constant vector on Ω. The cancellation is proved on every H₀¹ test. -/
theorem variableScalarVectorLoad_sub_const {Ω : Set (CoordinateSpace n)}
    (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) (hfin : (volume : Measure (CoordinateSpace n)) Ω ≠ (∞ : ℝ≥0∞))
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (c : Fin n → ℝ) :
    variableScalarVectorLoad Ω f (fun i => G i-constantDomainL2 Ω hΩm hfin (c i)) =
      variableScalarVectorLoad Ω f G := by
  apply ContinuousLinearMap.ext
  intro u
  rw [variableScalarVectorLoad_apply,variableScalarVectorLoad_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sub_left,inner_constantDomainL2_gradient_eq_zero hΩm hΩb,sub_zero]

end GaussianTilt.MomentMapLinearDirichlet
