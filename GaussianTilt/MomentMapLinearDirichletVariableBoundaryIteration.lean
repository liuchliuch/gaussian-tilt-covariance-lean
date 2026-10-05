import GaussianTilt.MomentMapLinearDirichletVariableBoundaryStep
import GaussianTilt.MomentMapLinearDirichletRadialEnergyIteration

/-!
# Genuine boundary Campanato decay from the variable weak equation

The natural coefficient oscillation and centered forcing bounds are
inserted into the constructed replacement theorem at every radius.
The true two-stage iteration then proves the mean-square normal-gradient
approximation, uniformly before the weak solution and forcing are chosen.
-/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma coordinateHalfBall_mono {j : Fin n} {r R : ℝ} (hrR : r ≤ R) :
    coordinateHalfBall j r ⊆ coordinateHalfBall j R := fun _ hx => ⟨hx.1.trans_le hrR,hx.2⟩

theorem exists_variable_halfBall_campanato_bound [NeZero n]
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
      ∀ k : ℕ, halfBallGradientExcess u.1 j (r₀*θ^k) ≤
        C*(dirichletEnergy Ω u u+N*(2*F+(n:ℝ)*H)^2)*(r₀*θ^k)^((n:ℝ)+β) := by
  obtain ⟨τ,K,N,hτ,hτ2,hK,hN,hStep⟩ := exists_variable_halfBall_energy_excess_step (n := n) hlam hΛ
  let Rw := min R₀ 1
  have hRw : 0 < Rw := lt_min hR₀ zero_lt_one
  have hRwR : Rw ≤ R₀ := min_le_left _ _
  have hRw1 : Rw ≤ 1 := min_le_right _ _
  obtain ⟨r₀,θ,C,hr₀,hr₀Rw,hr₀1,hθ,hθ2,hθτ,hC,hIter⟩ :=
    exists_radial_energy_campanato_constants n (NeZero.pos n) hK hD hβ hβ1 hτ hRw
  refine ⟨r₀,θ,C,N,hr₀,hr₀Rw.trans hRwR,hθ,hθ2,hC,hN,?_⟩
  intro j Ω hΩ u hDomain A B hB hlo hhi hAm KA hKA hAb hDb F H hF hH f G c hf hG heq
  let E := halfBallGradientEnergy u.1 j
  let X := halfBallGradientExcess u.1 j
  let P := N*(2*F+(n:ℝ)*H)^2
  have hP : 0 ≤ P := mul_nonneg hN.le (sq_nonneg _)
  have hM : 0 ≤ dirichletEnergy Ω u u := by rw [dirichletEnergy_eq_gradientNorm_sq]; positivity
  apply hIter E X (dirichletEnergy Ω u u) P hM hP
    (fun r _ _ => halfBallGradientEnergy_nonneg u.1 j r)
    (fun r _ _ => halfBallGradientExcess_nonneg u.1 j r)
    (fun r _ _ => halfBallGradientEnergy_le_dirichletEnergy u j r)
    (fun r hr _ => halfBallGradientExcess_le_energy u.1 j hr)
  intro t ht htτ r hr hrRw
  have hrR : r ≤ R₀ := hrRw.trans hRwR
  have hsub := coordinateHalfBall_mono (j := j) hrR
  have hDr : ∀ i k, ∀ᵐ x ∂volume, x ∈ coordinateHalfBall j r → |B i k-A x i k| ≤ D*r^β := by
    intro i k
    filter_upwards [hDb i k] with x hx hxr
    apply (hx (hsub hxr)).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hxr.1.le hβ.le) hD
  have hfr : ∀ᵐ x ∂volume, x ∈ coordinateHalfBall j r → |f x| ≤ F := by
    filter_upwards [hf] with x hx hxr
    exact hx (hsub hxr)
  have hGr : ∀ k, ∀ᵐ x ∂volume, x ∈ coordinateHalfBall j r → |G k x-c k| ≤ H*r^β := by
    intro k
    filter_upwards [hG k] with x hx hxr
    apply (hx (hsub hxr)).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hxr.1.le hβ.le) hH
  have heqr : ∀ v : dirichletSobolev (coordinateHalfBall j r),
      variableJetEnergy A hAm hKA hAb u.1 v.1=variableScalarVectorLoad (coordinateHalfBall j r) f G v := by
    intro v
    have hh := heq (dirichletInclusion hsub v)
    rw [variableScalarVectorLoad_apply,dirichletInclusion_value] at hh
    rw [variableScalarVectorLoad_apply]
    exact hh
  exact hStep j Ω hΩ u r β F H (D*r^β) hr (hrRw.trans hRw1) hβ hβ1 hF hH (by positivity)
    (hsub.trans hDomain) A B hB hlo hhi hAm KA hKA hAb hDr f G c hfr hGr heqr t ht htτ

end GaussianTilt.MomentMapLinearDirichlet
