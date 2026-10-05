import GaussianTilt.MomentMapLinearDirichletExcessRadiusInterpolation

/-! # Genuine all-radius boundary Campanato estimates from the weak PDE -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

theorem exists_variable_halfBall_campanato_all_radii [NeZero n]
    {lam Λ D β R₀ : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hR₀ : 0 < R₀) :
    ∃ r₀ θ C N : ℝ, 0 < r₀ ∧ r₀ ≤ R₀ ∧ 0 < θ ∧ θ ≤ 1/2 ∧ 0 < C ∧ 0 < N ∧
      ∀ (j : Fin n) (Ω : Set (CoordinateSpace n)), (Ω ⊆ {x | 0 < x j}) →
      ∀ u : dirichletSobolev Ω, coordinateHalfBall j R₀ ⊆ Ω →
      ∀ (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (B : Matrix (Fin n) (Fin n) ℝ), B.PosDef →
      (∀ v : KernelSpace n, lam*‖v‖^2 ≤ euclideanQuadratic B v) →
      (∀ v : KernelSpace n, euclideanQuadratic B v ≤ Λ*‖v‖^2) →
      ∀ hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume,
      ∀ KA : ℝ, ∀ hKA : 0 ≤ KA,
      ∀ hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ KA,
      (∀ i k, ∀ᵐ x ∂volume, x ∈ coordinateHalfBall j R₀ →
        |B i k-A x i k| ≤ D*‖(dirichletCoordinateEquiv n).symm x‖^β) →
      ∀ (F H : ℝ), 0 ≤ F → 0 ≤ H →
      ∀ (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
        (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (c : Fin n → ℝ),
      (∀ᵐ x ∂volume, x ∈ coordinateHalfBall j R₀ → |f x| ≤ F) →
      (∀ k, ∀ᵐ x ∂volume, x ∈ coordinateHalfBall j R₀ →
        |G k x-c k| ≤ H*‖(dirichletCoordinateEquiv n).symm x‖^β) →
      (∀ v : dirichletSobolev (coordinateHalfBall j R₀),
        variableJetEnergy A hAm hKA hAb u.1 v.1 = variableScalarVectorLoad (coordinateHalfBall j R₀) f G v) →
      ∀ r : ℝ, 0 < r → r ≤ r₀ → halfBallGradientExcess u.1 j r ≤
        C*(dirichletEnergy Ω u u+N*(2*F+(n:ℝ)*H)^2)*r^((n:ℝ)+β) := by
  obtain ⟨r₀,θ,C,N,hr₀,hr₀R,hθ,hθ2,hC,hN,hGeometric⟩ :=
    exists_variable_halfBall_campanato_bound (n := n) hlam hΛ hD hβ hβ1 hR₀
  let C' := C*θ^(-((n:ℝ)+β))
  have hC' : 0 < C' := mul_pos hC (Real.rpow_pos_of_pos hθ _)
  refine ⟨r₀,θ,C',N,hr₀,hr₀R,hθ,hθ2,hC',hN,?_⟩
  intro j Ω hΩ u hDomain A B hB hlo hhi hAm KA hKA hAb hDb F H hF hH f G c hf hG heq
  have hbound := hGeometric j Ω hΩ u hDomain A B hB hlo hhi hAm KA hKA hAb hDb F H hF hH f G c hf hG heq
  have hQ : 0 ≤ dirichletEnergy Ω u u+N*(2*F+(n:ℝ)*H)^2 := by
    rw [dirichletEnergy_eq_gradientNorm_sq]
    positivity
  have hall := halfBallGradientExcess_bound_all_radii u.1 j hr₀ hθ
    (hθ2.trans_lt (by norm_num)) (mul_nonneg hC.le hQ) hβ.le hbound
  intro r hr hrr₀
  convert hall r hr hrr₀ using 1 <;> dsimp [C'] <;> ring

end GaussianTilt.MomentMapLinearDirichlet
