import GaussianTilt.MomentMapLinearDirichletVariableInteriorStep
import GaussianTilt.MomentMapLinearDirichletRadialEnergyRescaling

/-! # Genuine scale-correct interior Campanato iteration of the weak PDE -/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma coordinateFullBall_mono {a : KernelSpace n} {r R : ℝ} (hrR : r ≤ R) :
    coordinateFullBall a r ⊆ coordinateFullBall a R := fun _ hx => Metric.ball_subset_ball hrR hx

/-- Interior recurrence constants are fixed before the center and its
initial radius. The latter retains its forcing power, making this usable
uniformly for balls approaching the flat boundary. -/
theorem exists_variable_ball_campanato_bound [NeZero n]
    {lam Λ D β : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ ρ θ C N : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < θ ∧ θ ≤ 1/2 ∧ 0 < C ∧ 0 < N ∧
      ∀ (a : KernelSpace n) (R₀ : ℝ), 0 < R₀ → R₀ ≤ 1 →
      ∀ (Ω : Set (CoordinateSpace n)) (u : dirichletSobolev Ω), coordinateFullBall a R₀ ⊆ Ω →
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
      ∀ k : ℕ, ballGradientExcess u.1 a ((R₀*ρ)*θ^k) ≤
        C*(ballGradientEnergy u.1 a R₀+N*(2*F+(n:ℝ)*H)^2*R₀^((n:ℝ)+2*β))*(ρ*θ^k)^((n:ℝ)+β) := by
  obtain ⟨τ,K,N,hτ,hτ2,hK,hN,hStep⟩ := exists_variable_fullBall_energy_excess_step (n := n) hlam hΛ
  obtain ⟨ρ,θ,C,hρ,hρ1,hθ,hθ2,hθτ,hC,hIter⟩ :=
    exists_scale_correct_radial_campanato_constants n (NeZero.pos n) hK hD hβ hβ1 hτ
  refine ⟨ρ,θ,C,N,hρ,hρ1,hθ,hθ2,hC,hN,?_⟩
  intro a R₀ hR₀ hR₀1 Ω u hDomain A B hB hlo hhi hAm KA hKA hAb hDb F H hF hH f G c hf hG heq
  let E := ballGradientEnergy u.1 a
  let X := ballGradientExcess u.1 a
  let P := N*(2*F+(n:ℝ)*H)^2
  have hP : 0 ≤ P := mul_nonneg hN.le (sq_nonneg _)
  apply hIter R₀ hR₀ hR₀1 E X (E R₀) P (ballGradientEnergy_nonneg u.1 a R₀) hP
    (fun r _ _ => ballGradientEnergy_nonneg u.1 a r)
    (fun r _ _ => ballGradientExcess_nonneg u.1 a r)
    (fun r _ hrR => ballGradientEnergy_mono u.1 a hrR)
    (fun r _ _ => ballGradientExcess_le_energy u.1 a r)
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
  exact hStep a Ω u r β F H (D*r^β) hr (hrR.trans hR₀1) hβ hβ1 hF hH (by positivity)
    (hsub.trans hDomain) A B hB hlo hhi hAm KA hKA hAb hDr f G c hfr hGr heqr t ht htτ

end GaussianTilt.MomentMapLinearDirichlet
