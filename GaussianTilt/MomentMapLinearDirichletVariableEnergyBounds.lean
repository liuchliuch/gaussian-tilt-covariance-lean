import GaussianTilt.MomentMapLinearDirichletVariableEnergy

/-! # Actual gradient-energy bounds for measurable coefficient perturbations -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

def jetGradientNorm (u : VolumeJet n) : ℝ := Real.sqrt (∑ i : Fin n, ‖u i.succ‖^2)

lemma jetGradientNorm_nonneg (u : VolumeJet n) : 0 ≤ jetGradientNorm u := Real.sqrt_nonneg _

lemma jetGradientNorm_sq (u : VolumeJet n) : (jetGradientNorm u)^2 = ∑ i : Fin n, ‖u i.succ‖^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma norm_jetDerivative_le_gradient (u : VolumeJet n) (i : Fin n) : ‖u i.succ‖ ≤ jetGradientNorm u := by
  apply (sq_le_sq₀ (norm_nonneg _) (jetGradientNorm_nonneg u)).mp
  rw [jetGradientNorm_sq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖u j.succ‖) (Finset.mem_univ i)

lemma jetGradientNorm_le_norm (u : VolumeJet n) : jetGradientNorm u ≤ ‖u‖ := by
  apply (sq_le_sq₀ (jetGradientNorm_nonneg u) (norm_nonneg _)).mp
  rw [jetGradientNorm_sq, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (sq_nonneg _)

lemma dirichletEnergy_eq_gradientNorm_sq (Ω : Set (CoordinateSpace n)) (u : dirichletSobolev Ω) :
    dirichletEnergy Ω u u = (jetGradientNorm u.1)^2 := by rw [dirichletEnergy_self, jetGradientNorm_sq]

lemma norm_boundedL2Multiplier_le {a : CoordinateSpace n → ℝ}
    (ha : AEStronglyMeasurable a volume) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ x ∂volume, |a x| ≤ K) (u : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    ‖boundedL2Multiplier ha hK hb u‖ ≤ K*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedL2Multiplier_ae ha hK hb u, hb] with x hx hbx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hbx (norm_nonneg _)

/-- A genuine L² coefficient multiplier gives a quantitative bilinear
bound in gradient energy only, not in the value norm. -/
theorem variableJetEnergy_abs_le_gradient
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K)
    (u v : VolumeJet n) :
    |variableJetEnergy A hAm hK hAb u v| ≤ (n:ℝ)^2*K*jetGradientNorm u*jetGradientNorm v := by
  have hentry (i k : Fin n) :
      |inner ℝ (boundedL2Multiplier (hAm i k) hK (hAb i k) (u k.succ)) (v i.succ)| ≤
        K*jetGradientNorm u*jetGradientNorm v := by
    have h1 := abs_real_inner_le_norm (boundedL2Multiplier (hAm i k) hK (hAb i k) (u k.succ)) (v i.succ)
    have h2 := norm_boundedL2Multiplier_le (hAm i k) hK (hAb i k) (u k.succ)
    have h3 := norm_jetDerivative_le_gradient u k
    have h4 := norm_jetDerivative_le_gradient v i
    exact h1.trans (mul_le_mul (h2.trans (mul_le_mul_of_nonneg_left h3 hK)) h4
      (norm_nonneg _) (mul_nonneg hK (jetGradientNorm_nonneg u)))
  simp only [variableJetEnergy, ContinuousLinearMap.sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.comp_apply, volumeJetDerivative, PiLp.proj_apply, innerSL_apply]
  calc
    _ ≤ ∑ i : Fin n, ∑ k : Fin n,
        |inner ℝ (boundedL2Multiplier (hAm i k) hK (hAb i k) (u k.succ)) (v i.succ)| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : Fin n, ∑ _k : Fin n, K*jetGradientNorm u*jetGradientNorm v :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => hentry i k))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GaussianTilt.MomentMapLinearDirichlet
