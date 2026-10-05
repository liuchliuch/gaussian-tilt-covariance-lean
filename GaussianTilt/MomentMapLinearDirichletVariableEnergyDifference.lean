import GaussianTilt.MomentMapLinearDirichletVariableEnergyBounds

/-! # Literal difference of measurable divergence coefficient energies -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma integrable_variable_energy (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K) (u v : VolumeJet n) :
    Integrable (fun x => ∑ i : Fin n, ∑ k : Fin n, A x i k * u k.succ x * v i.succ x) volume :=
  integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun k _ =>
    integrable_variable_energy_entry A hAm hK hAb u v i k))

/-- The operator difference is the actual coefficient difference, even for
merely measurable coefficients and genuine L² derivative classes. -/
theorem variableJetEnergy_sub
    (A B : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    (hBm : ∀ i k, AEStronglyMeasurable (fun x => B x i k) volume)
    {KA KB δ : ℝ} (hKA : 0 ≤ KA) (hKB : 0 ≤ KB) (hδ : 0 ≤ δ)
    (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ KA)
    (hBb : ∀ i k, ∀ᵐ x ∂volume, |B x i k| ≤ KB)
    (hDb : ∀ i k, ∀ᵐ x ∂volume, |A x i k-B x i k| ≤ δ)
    (u v : VolumeJet n) :
    variableJetEnergy (fun x => A x-B x) (fun i k => (hAm i k).sub (hBm i k)) hδ hDb u v =
      variableJetEnergy A hAm hKA hAb u v - variableJetEnergy B hBm hKB hBb u v := by
  rw [variableJetEnergy_integral, variableJetEnergy_integral, variableJetEnergy_integral,
    ← integral_sub (integrable_variable_energy A hAm hKA hAb u v) (integrable_variable_energy B hBm hKB hBb u v)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib])

end GaussianTilt.MomentMapLinearDirichlet
