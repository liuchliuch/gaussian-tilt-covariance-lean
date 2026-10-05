import GaussianTilt.MomentMapLinearDirichletVariableInteriorIteration
import GaussianTilt.MomentMapLinearDirichletRadialBoundedEnergySharp

/-! # Full forcing-exponent interior excess from the actual weak PDE

The exact normalized initial excess is retained. In particular no inverse
height power is introduced by replacing that excess with the initial energy.
-/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

theorem exists_variable_ball_full_exponent_bound [NeZero n]
    {lam Λ D β : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ θ C N : ℝ, 0 < θ ∧ θ ≤ 1/2 ∧ 0 < C ∧ 0 < N ∧
      ∀ (a : KernelSpace n) (R₀ : ℝ), 0 < R₀ → R₀ ≤ 1 →
      ∀ (Ω : Set (CoordinateSpace n)) (u : dirichletSobolev Ω), coordinateFullBall a R₀ ⊆ Ω →
      ∀ M : ℝ, 0 ≤ M →
      (∀ r, 0 < r → r ≤ R₀ → ballGradientEnergy u.1 a r ≤ M*r^n) →
      ∀ (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (B : Matrix (Fin n) (Fin n) ℝ), B.PosDef →
      (∀ v : KernelSpace n, lam*‖v‖^2 ≤ euclideanQuadratic B v) →
      (∀ v : KernelSpace n, euclideanQuadratic B v ≤ Λ*‖v‖^2) →
      ∀ hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume,
      ∀ KA : ℝ, ∀ hKA : 0 ≤ KA,
      ∀ hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ KA,
      (∀ i k, ∀ᵐ x ∂volume, x ∈ coordinateFullBall a R₀ →
        |B i k-A x i k| ≤ D*‖(dirichletCoordinateEquiv n).symm x-a‖^β) →
      ∀ F H : ℝ, 0 ≤ F → 0 ≤ H →
      ∀ (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
        (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (c : Fin n → ℝ),
      (∀ᵐ x ∂volume, x ∈ coordinateFullBall a R₀ → |f x| ≤ F) →
      (∀ k, ∀ᵐ x ∂volume, x ∈ coordinateFullBall a R₀ →
        |G k x-c k| ≤ H*‖(dirichletCoordinateEquiv n).symm x-a‖^β) →
      (∀ v : dirichletSobolev (coordinateFullBall a R₀),
        variableJetEnergy A hAm hKA hAb u.1 v.1=variableScalarVectorLoad (coordinateFullBall a R₀) f G v) →
      ∀ k : ℕ, ballGradientExcess u.1 a (R₀*θ^k) ≤
        (ballGradientExcess u.1 a R₀/R₀^((n:ℝ)+2*β)+
          C*(M+N*(2*F+(n:ℝ)*H)^2))*(R₀*θ^k)^((n:ℝ)+2*β) := by
  obtain ⟨τ,K,N,hτ,hτ2,hK,hN,hStep⟩ := exists_variable_fullBall_energy_excess_step (n := n) hlam hΛ
  obtain ⟨θ,C,hθ,hθ2,hθτ,hC,hIter⟩ :=
    exists_radial_bounded_energy_full_exponent_sharp n hK hD hβ hβ1 hτ
  refine ⟨θ,C,N,hθ,hθ2,hC,hN,?_⟩
  intro a R₀ hR₀ hR₀1 Ω u hDomain M hM hEnergy A B hB hlo hhi hAm KA hKA hAb hDb F H hF hH f G c hf hG heq
  let E := ballGradientEnergy u.1 a
  let X := ballGradientExcess u.1 a
  let P := N*(2*F+(n:ℝ)*H)^2
  have hP : 0 ≤ P := mul_nonneg hN.le (sq_nonneg _)
  apply hIter R₀ hR₀ E X M P hM hP
    (fun r _ _ => ballGradientExcess_nonneg u.1 a r) hEnergy
  intro t ht htτ r hr hrR
  have hsub := coordinateFullBall_mono (a := a) hrR
  have hdist (x : CoordinateSpace n) (hx : x ∈ coordinateFullBall a r) :
      ‖(dirichletCoordinateEquiv n).symm x-a‖ ≤ r := by
    exact (show ‖(dirichletCoordinateEquiv n).symm x-a‖<r from hx).le
  have hDr : ∀ i k, ∀ᵐ x ∂volume, x ∈ coordinateFullBall a r → |B i k-A x i k| ≤ D*r^β := by
    intro i k
    filter_upwards [hDb i k] with x hx hxr
    exact (hx (hsub hxr)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (hdist x hxr) hβ.le) hD)
  have hfr : ∀ᵐ x ∂volume, x ∈ coordinateFullBall a r → |f x| ≤ F := by
    filter_upwards [hf] with x hx hxr
    exact hx (hsub hxr)
  have hGr : ∀ k, ∀ᵐ x ∂volume, x ∈ coordinateFullBall a r → |G k x-c k| ≤ H*r^β := by
    intro k
    filter_upwards [hG k] with x hx hxr
    exact (hx (hsub hxr)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (hdist x hxr) hβ.le) hH)
  have heqr : ∀ v : dirichletSobolev (coordinateFullBall a r),
      variableJetEnergy A hAm hKA hAb u.1 v.1=variableScalarVectorLoad (coordinateFullBall a r) f G v := by
    intro v
    have hh := heq (dirichletInclusion hsub v)
    rw [variableScalarVectorLoad_apply,dirichletInclusion_value] at hh
    rw [variableScalarVectorLoad_apply]
    exact hh
  have hh := (hStep a Ω u r β F H (D*r^β) hr (hrR.trans hR₀1) hβ hβ1.le hF hH (by positivity)
    (hsub.trans hDomain) A B hB hlo hhi hAm KA hKA hAb hDr f G c hfr hGr heqr t ht htτ).2
  have hp : (r^β)^2=r^(2*β) := by
    rw [← Real.rpow_two,← Real.rpow_mul hr.le]
    congr 1
    ring
  rw [mul_pow,hp] at hh
  convert hh using 1 <;> ring

end GaussianTilt.MomentMapLinearDirichlet
