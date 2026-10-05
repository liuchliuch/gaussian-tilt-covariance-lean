import GaussianTilt.MomentMapLinearDirichletVariableReplacement
import GaussianTilt.MomentMapLinearDirichletRestrictedEnergy

/-! # Frozen replacement with the genuine local gradient energy

The correction/test zero extension localizes the original gradient norm.
Thus this estimate supplies the actual local E(r) for decay iteration.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
attribute [local irreducible] variableWeakSolution
variable {n : ℕ}

theorem exists_frozen_harmonic_replacement_local
    {Ω : Set (CoordinateSpace n)} (i : Fin n) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : ∀ x ∈ Ω, |x i| ≤ R) (hΩm : MeasurableSet Ω)
    (A B : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    (hBm : ∀ i k, AEStronglyMeasurable (fun x => B x i k) volume)
    {KA KB δ lam F : ℝ} (hKA : 0 ≤ KA) (hKB : 0 ≤ KB) (hδ : 0 ≤ δ) (hlam : 0 < lam) (hF : 0 ≤ F)
    (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ KA)
    (hBb : ∀ i k, ∀ᵐ x ∂volume, |B x i k| ≤ KB)
    (hDb : ∀ i k, ∀ᵐ x ∂volume, |B x i k-A x i k| ≤ δ)
    (hellB : ∀ᵐ x ∂volume, ∀ z : Fin n → ℝ, lam * (∑ i, (z i)^2) ≤ z ⬝ᵥ (B x *ᵥ z))
    (u : VolumeJet n) (hu : u ∈ weightedSobolev (volume : Measure (CoordinateSpace n)))
    (Φ : dirichletSobolev Ω →L[ℝ] ℝ)
    (hΦ : ∀ v : dirichletSobolev Ω, |Φ v| ≤ F*jetGradientNorm v.1)
    (heq : ∀ v : dirichletSobolev Ω, variableJetEnergy A hAm hKA hAb u v.1 = Φ v) :
    ∃ w : dirichletSobolev Ω,
      (u-w.1) ∈ weightedSobolev (volume : Measure (CoordinateSpace n)) ∧
      (∀ v : dirichletSobolev Ω, variableJetEnergy B hBm hKB hBb (u-w.1) v.1 = 0) ∧
      jetGradientNorm w.1 ≤ (F+(n:ℝ)^2*δ*restrictedJetGradientNorm Ω hΩm u)/lam ∧
      dirichletEnergy Ω w w ≤ ((F+(n:ℝ)^2*δ*restrictedJetGradientNorm Ω hΩm u)/lam)^2 := by
  let D := variableJetEnergy (fun x => B x-A x) (fun i k => (hBm i k).sub (hAm i k)) hδ hDb
  let Φ₀ : dirichletSobolev Ω →L[ℝ] ℝ := Φ + (D u).comp (dirichletSobolev Ω).subtypeL
  let w := variableWeakSolution i hR hΩ B hBm hKB hBb hlam hellB Φ₀
  have hw (v : dirichletSobolev Ω) : variableJetEnergy B hBm hKB hBb w.1 v.1 = Φ v + D u v.1 := by
    have he := variableWeakSolution_equation i hR hΩ B hBm hKB hBb hlam hellB Φ₀ v
    exact he
  have hdiff (v : VolumeJet n) : D u v =
      variableJetEnergy B hBm hKB hBb u v - variableJetEnergy A hAm hKA hAb u v :=
    variableJetEnergy_sub B A hBm hAm hKB hKA hδ hBb hAb hDb u v
  have hharm (v : dirichletSobolev Ω) : variableJetEnergy B hBm hKB hBb (u-w.1) v.1 = 0 := by
    rw [map_sub, ContinuousLinearMap.sub_apply, hw, hdiff, heq]
    ring
  have henergy : lam * (jetGradientNorm w.1)^2 ≤
      (F+(n:ℝ)^2*δ*restrictedJetGradientNorm Ω hΩm u)*jetGradientNorm w.1 := by
    have hl := variableDirichletEnergy_lower Ω B hBm hKB hBb hellB w
    rw [dirichletEnergy_eq_gradientNorm_sq] at hl
    change lam*(jetGradientNorm w.1)^2 ≤ variableJetEnergy B hBm hKB hBb w.1 w.1 at hl
    rw [hw] at hl
    have h1 := (le_abs_self (Φ w)).trans (hΦ w)
    have h2 := (le_abs_self (D u w.1)).trans
      (variableJetEnergy_abs_le_restricted_gradient Ω hΩm (fun x => B x-A x) (fun i k => (hBm i k).sub (hAm i k)) hδ hDb u w)
    nlinarith only [hl, h1, h2]
  have hnum : 0 ≤ F+(n:ℝ)^2*δ*restrictedJetGradientNorm Ω hΩm u :=
    add_nonneg hF (mul_nonneg (mul_nonneg (sq_nonneg _) hδ) (restrictedJetGradientNorm_nonneg Ω hΩm u))
  have hbound : jetGradientNorm w.1 ≤ (F+(n:ℝ)^2*δ*restrictedJetGradientNorm Ω hΩm u)/lam := by
    apply (le_div_iff₀ hlam).mpr
    by_cases hz : jetGradientNorm w.1 = 0
    · rw [hz, zero_mul]
      exact hnum
    · have hp : 0 < jetGradientNorm w.1 := lt_of_le_of_ne (jetGradientNorm_nonneg _) (Ne.symm hz)
      nlinarith only [henergy, hp]
  refine ⟨w, (weightedSobolev (volume : Measure (CoordinateSpace n))).sub_mem hu (dirichletSobolev_mem_weightedSobolev (n := n) (Ω := Ω) w), hharm, hbound, ?_⟩
  rw [dirichletEnergy_eq_gradientNorm_sq]
  exact (sq_le_sq₀ (jetGradientNorm_nonneg _) (div_nonneg hnum hlam.le)).mpr hbound

end GaussianTilt.MomentMapLinearDirichlet
