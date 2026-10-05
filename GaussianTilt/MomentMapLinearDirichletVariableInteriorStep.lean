import GaussianTilt.MomentMapLinearDirichletFrozenBallExcess
import GaussianTilt.MomentMapLinearDirichletEnergyDecayGeometry
import GaussianTilt.MomentMapLinearDirichletInteriorEnergyFields
import GaussianTilt.MomentMapLinearDirichletVariableWeakFullBallReplacement
import GaussianTilt.MomentMapLinearDirichletLocalCoefficients
import GaussianTilt.MomentMapLinearDirichletFrozenWeakTestBridge

/-!
# The genuine variable-coefficient full-ball energy/excess step

The corrector, its centered forcing bound, constant-SPD normalization,
weak harmonic reflection, and both decay estimates are all constructed.
The final one-step inequalities have only the literal weak PDE and natural
coefficient/forcing bounds as inputs.
-/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- The actual variable-coefficient interior energy/excess improvement,
with uniform constants chosen before all coefficients, loads and solutions. -/
theorem exists_variable_fullBall_energy_excess_step [NeZero n]
    {lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) :
    ∃ τ K N : ℝ, 0 < τ ∧ τ ≤ 1/2 ∧ 0 < K ∧ 0 < N ∧
      ∀ (a : KernelSpace n) (Ω : Set (CoordinateSpace n)),
      ∀ (u : dirichletSobolev Ω) (R β F H δ : ℝ),
      0 < R → R ≤ 1 → 0 < β → β ≤ 1 → 0 ≤ F → 0 ≤ H → 0 ≤ δ →
      coordinateFullBall a R ⊆ Ω →
      ∀ (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (B : Matrix (Fin n) (Fin n) ℝ), B.PosDef →
      (∀ v : KernelSpace n, lam*‖v‖^2 ≤ euclideanQuadratic B v) →
      (∀ v : KernelSpace n, euclideanQuadratic B v ≤ Λ*‖v‖^2) →
      ∀ hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume,
      ∀ KA : ℝ, ∀ hKA : 0 ≤ KA,
      ∀ hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ KA,
      (∀ i k, ∀ᵐ x ∂volume, x ∈ coordinateFullBall a R → |B i k-A x i k| ≤ δ) →
      ∀ (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
        (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (c : Fin n → ℝ),
      (∀ᵐ x ∂volume, x ∈ coordinateFullBall a R → |f x| ≤ F) →
      (∀ k, ∀ᵐ x ∂volume, x ∈ coordinateFullBall a R → |G k x-c k| ≤ H*R^β) →
      (∀ v : dirichletSobolev (coordinateFullBall a R),
        variableJetEnergy A hAm hKA hAb u.1 v.1 = variableScalarVectorLoad (coordinateFullBall a R) f G v) →
      ∀ θ : ℝ, 0 < θ → θ ≤ τ →
      ballGradientEnergy u.1 a (θ*R) ≤ (K*θ^n+K*δ^2)*ballGradientEnergy u.1 a R+
        N*(2*F+(n:ℝ)*H)^2*R^((n:ℝ)+2*β) ∧
      ballGradientExcess u.1 a (θ*R) ≤ K*θ^(n+2)*ballGradientExcess u.1 a R+
        K*δ^2*ballGradientEnergy u.1 a R+N*(2*F+(n:ℝ)*H)^2*R^((n:ℝ)+2*β) := by
  obtain ⟨τ,C,hτ,hτ2,hC,hFrozen⟩ := exists_frozen_ball_gradient_excess_decay (n := n) hlam hΛ
  let Ce := 2*C+4*(C+1)/τ^n
  have hCe : 0 < Ce := by dsimp [Ce]; positivity
  let Kh := max C Ce
  have hKh : 0 < Kh := hC.trans_le (le_max_left _ _)
  let J := 2*(n:ℝ)^4/lam^2
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  let K := replacementIterationConstant Kh J
  let V := volume.real (Metric.ball (0 : KernelSpace n) 1)
  have hV : 0 < V := ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne
  let N := (4*Kh+2)*(2/lam^2)*V
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨τ,K,N,hτ,hτ2,replacementIterationConstant_pos hKh hJ,hN,?_⟩
  intro a Ω u R β F H δ hR hR1 hβ hβ1 hF hH hδ hSub A B hB hlo hhi hAm KA hKA hAb hDb f G c hf hG heq
  let KB := ‖B‖
  have hKB : 0 ≤ KB := norm_nonneg B
  have hBm : ∀ i k, AEStronglyMeasurable (fun _ : CoordinateSpace n => B i k) volume := fun _ _ => aestronglyMeasurable_const
  have hBb : ∀ i k, ∀ᵐ x ∂(volume : Measure (CoordinateSpace n)), |B i k| ≤ KB := by
    intro i k
    exact ae_of_all _ (fun _ => by simpa only [Real.norm_eq_abs] using Matrix.norm_entry_le_entrywise_sup_norm B (i := i) (j := k))
  have hellB : ∀ᵐ x ∂(volume : Measure (CoordinateSpace n)), ∀ z : Fin n → ℝ,
      lam*(∑ i,(z i)^2) ≤ z ⬝ᵥ (B*ᵥz) := by
    apply ae_of_all
    intro x z
    have hh := hlo (WithLp.toLp 2 z)
    simpa only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,euclideanQuadratic,WithLp.ofLp_toLp] using hh
  obtain ⟨w,hw,hharm,hcorr⟩ := exists_local_centered_fullBall_harmonic_replacement a hR hR1 hβ hβ1 hF hH
    A (fun _ => B) hAm hBm hKA hKB hδ hlam hAb hBb hDb hellB u.1
    (dirichletSobolev_mem_weightedSobolev u) f G c hf hG heq
  let v : dirichletSobolev Ω := u-dirichletInclusion hSub w
  have hv : v.1=u.1-w.1 := rfl
  have hBs : ∀ i k, B i k=B k i := by intro i k; simpa only [star_trivial] using (hB.isHermitian.apply k i)
  have htest := constant_energy_zero_compact_tests B hBs hBm hKB hBb (u.1-w.1) hharm
  obtain ⟨p,hp⟩ := hFrozen B hB hlo hhi Ω v a R hR (by simpa only [hv] using htest)
  have hpzero : ∀ r : ℝ, 0 < r → r ≤ τ*R →
      (∫ x in Metric.ball a r, ‖euclideanWeakGradient (u.1-w.1) x-p‖^2) ≤
        C*(r/R)^(n+2)*ballGradientEnergy (u.1-w.1) a R := by
    intro r hr hrt
    simpa only [hv,sub_zero,ballGradientEnergy] using hp 0 r hr hrt
  have hEnergyAll := fullBall_energy_decay_of_common_excess a (euclideanWeakGradient (u.1-w.1)) p
    hR hτ (hτ2.trans (by norm_num)) hC ((euclideanWeakGradient_memLp _).restrict _) hpzero
  let Fc := ((2/lam^2)*(2*F+(n:ℝ)*H)^2*V)*R^((n:ℝ)+2*β)
  have hFc : 0 ≤ Fc := by dsimp [Fc]; positivity
  have hCorr : dirichletEnergy (coordinateFullBall a R) w w ≤ J*δ^2*ballGradientEnergy u.1 a R+Fc := by
    rw [ballGradientEnergy_eq_local]
    exact hcorr
  intro θ hθ hθτ
  have hθ1 : θ ≤ 1 := hθτ.trans (hτ2.trans (by norm_num))
  have hratio : θ*R/R=θ := mul_div_cancel_right₀ θ hR.ne'
  have hEH : ballGradientEnergy (u.1-w.1) a (θ*R) ≤ (Kh*θ^n)*ballGradientEnergy (u.1-w.1) a R := by
    have hh := hEnergyAll (θ*R) (mul_pos hθ hR) (mul_le_mul_of_nonneg_right hθτ hR.le)
    rw [hratio] at hh
    apply hh.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right C Ce) (pow_nonneg hθ.le _))
      (ballGradientEnergy_nonneg (u.1-w.1) a R)
  have hXH : ∃ p : KernelSpace n,
      (∫ x in Metric.ball a (θ*R), ‖euclideanWeakGradient (u.1-w.1) x-p‖^2) ≤
      (Kh*θ^(n+2))*(∫ x in Metric.ball a R,
        ‖euclideanWeakGradient (u.1-w.1) x-ballMeanGradient u.1 a R‖^2) := by
    have hh := hp (ballMeanGradient u.1 a R) (θ*R) (mul_pos hθ hR) (mul_le_mul_of_nonneg_right hθτ hR.le)
    rw [hv,hratio] at hh
    refine ⟨p,hh.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C Ce) (pow_nonneg hθ.le _))
      (integral_nonneg (fun _ => sq_nonneg _))
  have hstep := ball_weak_jet_energy_excess_step u.1 w a hR hθ hθ1 hKh hJ hFc hCorr hEH hXH
  dsimp only at hstep
  convert hstep using 1 <;> dsimp [K,N,Fc] <;> ring

end GaussianTilt.MomentMapLinearDirichlet
