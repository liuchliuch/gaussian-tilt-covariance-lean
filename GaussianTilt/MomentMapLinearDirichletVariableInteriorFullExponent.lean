import GaussianTilt.MomentMapLinearDirichletVariableInteriorBoundedEnergy
import GaussianTilt.MomentMapLinearDirichletInteriorRadiusInterpolation

/-! # All-radius full-exponent interior estimate with the genuine initial excess -/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

theorem exists_variable_ball_full_exponent_all_radii [NeZero n]
    {lam Λ D β : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
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
      ∀ r : ℝ, 0 < r → r ≤ R₀ → ballGradientExcess u.1 a r ≤
        C*(ballGradientExcess u.1 a R₀/R₀^((n:ℝ)+2*β)+
          M+N*(2*F+(n:ℝ)*H)^2)*r^((n:ℝ)+2*β) := by
  obtain ⟨θ,C,N,hθ,hθ2,hC,hN,hGeometric⟩ :=
    exists_variable_ball_full_exponent_bound (n := n) hlam hΛ hD hβ hβ1
  let p := (n:ℝ)+2*β
  let C' := max 1 C*θ^(-p)
  have hC' : 0 < C' := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Real.rpow_pos_of_pos hθ _)
  refine ⟨C',N,hC',hN,?_⟩
  intro a R₀ hR₀ hR₀1 Ω u hDomain M hM hEnergy A B hB hlo hhi hAm KA hKA hAb hDb F H hF hH f G c hf hG heq
  have hGeom := hGeometric a R₀ hR₀ hR₀1 Ω u hDomain M hM hEnergy A B hB hlo hhi hAm KA hKA hAb hDb F H hF hH f G c hf hG heq
  let T := ballGradientExcess u.1 a R₀/R₀^p
  let Q := M+N*(2*F+(n:ℝ)*H)^2
  have hT : 0 ≤ T := div_nonneg (ballGradientExcess_nonneg u.1 a R₀) (Real.rpow_nonneg hR₀.le _)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hAll := geometric_power_bound_to_all_radii (s := p) (ballGradientExcess u.1 a) hR₀ hθ
    (hθ2.trans_lt (by norm_num)) (add_nonneg hT (mul_nonneg hC.le hQ))
    (by dsimp only [p]; positivity)
    (fun r hr s hs hrs => ballGradientExcess_mono u.1 a hrs) hGeom
  have hcoef : T+C*Q ≤ max 1 C*(T+Q) := by
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left 1 C) hT,
      mul_le_mul_of_nonneg_right (le_max_right 1 C) hQ]
  intro r hr hrR
  apply (hAll r hr hrR).trans
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hθ.le (-p)))
    (Real.rpow_nonneg hr.le p)
  convert hh using 1 <;> dsimp only [C',T,Q,p] <;> ring

end GaussianTilt.MomentMapLinearDirichlet
