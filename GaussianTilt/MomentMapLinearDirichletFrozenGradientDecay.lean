import GaussianTilt.MomentMapLinearDirichletFrozenBallExcess
import GaussianTilt.MomentMapLinearDirichletEnergyDecayGeometry

/-! # Common-threshold genuine frozen energy and excess estimates -/
noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

theorem exists_frozen_halfBall_gradient_decay [NeZero n]
    {lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) :
    ∃ θ K : ℝ, 0 < θ ∧ θ ≤ 1/2 ∧ 0 < K ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosDef →
      (∀ v : KernelSpace n, lam*‖v‖^2 ≤ euclideanQuadratic B v) →
      (∀ v : KernelSpace n, euclideanQuadratic B v ≤ Λ*‖v‖^2) →
      ∀ (j : Fin n) (Ω : Set (CoordinateSpace n)), (Ω ⊆ {x | 0 < x j}) →
      ∀ u : dirichletSobolev Ω, ∀ R : ℝ, 0 < R →
      (∀ ξ : smoothCompactCore n, tsupport ξ.1 ⊆ coordinateHalfBall j R →
        (∫ x, (fun i : Fin n => u.1 i.succ x) ⬝ᵥ (B*ᵥcoordinateGradient ξ.1 x))=0) →
      ∃ p : KernelSpace n, (∀ i, i ≠ j → p i=0) ∧
        (∀ q : KernelSpace n, (∀ i, i ≠ j → q i=0) → ∀ r : ℝ, 0 < r → r ≤ θ*R →
          (∫ x in upperCampanatoBall j 0 r, ‖euclideanWeakGradient u.1 x-p‖^2) ≤
            K*(r/R)^(n+2)*(∫ x in upperCampanatoBall j 0 R, ‖euclideanWeakGradient u.1 x-q‖^2)) ∧
        (∀ r : ℝ, 0 < r → r ≤ θ*R →
          (∫ x in upperCampanatoBall j 0 r, ‖euclideanWeakGradient u.1 x‖^2) ≤
            K*(r/R)^n*(∫ x in upperCampanatoBall j 0 R, ‖euclideanWeakGradient u.1 x‖^2)) := by
  obtain ⟨θ,K,hθ,hθhalf,hK,hEx⟩ := exists_frozen_halfBall_gradient_excess_decay (n := n) hlam hΛ
  let E := halfBallEnergyDecayConstant n K θ
  have hE : 0 < E := halfBallEnergyDecayConstant_pos hK hθ
  refine ⟨θ,max K E,hθ,hθhalf,hK.trans_le (le_max_left _ _),?_⟩
  intro B hB hlo hhi j Ω hΩ u R hR heq
  obtain ⟨p,hp,hdec⟩ := hEx B hB hlo hhi j Ω hΩ u R hR heq
  have hEnergy := halfBall_energy_decay_of_common_excess j (euclideanWeakGradient u.1) p hR hθ
    (hθhalf.trans (by norm_num)) hK ((euclideanWeakGradient_memLp u.1).mono_measure Measure.restrict_le_self)
    (fun r hr hrt => by simpa only [sub_zero] using hdec 0 (fun i _ => rfl) r hr hrt)
  refine ⟨p,hp,?_,?_⟩
  · intro q hq r hr hrt
    exact (hdec q hq r hr hrt).trans (by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      · exact integral_nonneg (fun _ => sq_nonneg _))
  · intro r hr hrt
    exact (hEnergy r hr hrt).trans (by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      · exact integral_nonneg (fun _ => sq_nonneg _))

theorem exists_frozen_ball_gradient_decay [NeZero n]
    {lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) :
    ∃ θ K : ℝ, 0 < θ ∧ θ ≤ 1/2 ∧ 0 < K ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosDef →
      (∀ v : KernelSpace n, lam*‖v‖^2 ≤ euclideanQuadratic B v) →
      (∀ v : KernelSpace n, euclideanQuadratic B v ≤ Λ*‖v‖^2) →
      ∀ (Ω : Set (CoordinateSpace n)) (u : dirichletSobolev Ω),
      ∀ a : KernelSpace n, ∀ R : ℝ, 0 < R →
      (∀ ξ : smoothCompactCore n, tsupport ξ.1 ⊆ (dirichletCoordinateEquiv n).symm ⁻¹' Metric.ball a R →
        (∫ x, (fun i : Fin n => u.1 i.succ x) ⬝ᵥ (B*ᵥcoordinateGradient ξ.1 x))=0) →
      ∃ p : KernelSpace n,
        (∀ q : KernelSpace n, ∀ r : ℝ, 0 < r → r ≤ θ*R →
          (∫ x in Metric.ball a r, ‖euclideanWeakGradient u.1 x-p‖^2) ≤
            K*(r/R)^(n+2)*(∫ x in Metric.ball a R, ‖euclideanWeakGradient u.1 x-q‖^2)) ∧
        (∀ r : ℝ, 0 < r → r ≤ θ*R →
          (∫ x in Metric.ball a r, ‖euclideanWeakGradient u.1 x‖^2) ≤
            K*(r/R)^n*(∫ x in Metric.ball a R, ‖euclideanWeakGradient u.1 x‖^2)) := by
  obtain ⟨θ,K,hθ,hθhalf,hK,hEx⟩ := exists_frozen_ball_gradient_excess_decay (n := n) hlam hΛ
  let E := 2*K+4*(K+1)/θ^n
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨θ,max K E,hθ,hθhalf,hK.trans_le (le_max_left _ _),?_⟩
  intro B hB hlo hhi Ω u a R hR heq
  obtain ⟨p,hdec⟩ := hEx B hB hlo hhi Ω u a R hR heq
  have hEnergy := fullBall_energy_decay_of_common_excess a (euclideanWeakGradient u.1) p hR hθ
    (hθhalf.trans (by norm_num)) hK ((euclideanWeakGradient_memLp u.1).mono_measure Measure.restrict_le_self)
    (fun r hr hrt => by simpa only [sub_zero] using hdec 0 r hr hrt)
  refine ⟨p,?_,?_⟩
  · intro q r hr hrt
    exact (hdec q r hr hrt).trans (by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      · exact integral_nonneg (fun _ => sq_nonneg _))
  · intro r hr hrt
    exact (hEnergy r hr hrt).trans (by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      · exact integral_nonneg (fun _ => sq_nonneg _))

end GaussianTilt.MomentMapLinearDirichlet
