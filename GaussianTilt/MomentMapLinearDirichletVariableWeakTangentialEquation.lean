import GaussianTilt.MomentMapLinearDirichletTangentialDifferenceL2
import GaussianTilt.MomentMapLinearDirichletVariableWeakTestClosure

/-! # Exact weak divergence commutator for genuine L² translations -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 1000

lemma translated_coefficient_measurable
    {A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hAm:∀ i k,AEStronglyMeasurable (fun x=>A x i k) volume) (a:CoordinateSpace n) (i k:Fin n) :
    AEStronglyMeasurable (fun x=>A (x+a) i k) volume :=
  (hAm i k).comp_measurePreserving (measurePreserving_add_right volume a)

lemma translated_coefficient_bound
    {A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {K:ℝ}
    (hAb:∀ i k,∀ᵐ x∂volume,|A x i k|≤K) (a:CoordinateSpace n) (i k:Fin n) :
    ∀ᵐ x∂volume,|A (x+a) i k|≤K :=
  (measurePreserving_add_right (volume:Measure (CoordinateSpace n)) a).quasiMeasurePreserving.tendsto_ae.eventually (hAb i k)

lemma variableJetEnergy_translate_test
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm:∀ i k,AEStronglyMeasurable (fun x=>A x i k) volume)
    {K:ℝ} (hK:0≤K) (hAb:∀ i k,∀ᵐ x∂volume,|A x i k|≤K)
    (a:CoordinateSpace n) (u v:VolumeJet n) :
    variableJetEnergy A hAm hK hAb u (volumeTranslateJet (-a) v)=
      ∫ x,∑ i:Fin n,∑ k:Fin n,A (x+a) i k*(volumeTranslateJet a u k.succ x)*v i.succ x := by
  rw [variableJetEnergy_integral]
  have hv (i:Fin n) : ∀ᵐ x∂volume,volumeTranslateJet (-a) v i.succ x=v i.succ (x-a) := by
    simpa only [volumeTranslateJet_apply,sub_eq_add_neg] using volumeTranslate_ae (-a) (v i.succ)
  calc
    _ = ∫ x,∑ i:Fin n,∑ k:Fin n,A x i k*u k.succ x*v i.succ (x-a) := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hv] with x hx
      simp only [hx]
    _ = ∫ x,∑ i:Fin n,∑ k:Fin n,A (x+a) i k*u k.succ (x+a)*v i.succ x := by
      have hh := integral_add_right_eq_self (μ := (volume : Measure (CoordinateSpace n)))
        (fun x=>∑ i:Fin n,∑ k:Fin n,A x i k*u k.succ x*v i.succ (x-a)) a
      simpa only [add_sub_cancel_right] using hh.symm
    _ = _ := by
      have hu (k:Fin n) : ∀ᵐ x∂volume,volumeTranslateJet a u k.succ x=u k.succ (x+a) :=
        volumeTranslate_ae a (u k.succ)
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hu] with x hx
      simp only [hx]

/-- The coefficient commutator is a literal integrable weak-gradient
product. This exact identity precedes every tangential energy estimate. -/
theorem variableJetEnergy_translate_commutator
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm:∀ i k,AEStronglyMeasurable (fun x=>A x i k) volume)
    {K:ℝ} (hK:0≤K) (hAb:∀ i k,∀ᵐ x∂volume,|A x i k|≤K)
    (a:CoordinateSpace n) (u v:VolumeJet n) :
    variableJetEnergy A hAm hK hAb (volumeTranslateJet a u) v=
      variableJetEnergy A hAm hK hAb u (volumeTranslateJet (-a) v)-
        ∫ x,∑ i:Fin n,∑ k:Fin n,(A (x+a) i k-A x i k)*(volumeTranslateJet a u k.succ x)*v i.succ x := by
  have htrans := integrable_finset_sum Finset.univ (fun (i:Fin n) _=>integrable_finset_sum Finset.univ
    (fun (k:Fin n) _=>integrable_variable_energy_entry (fun x=>A (x+a))
      (translated_coefficient_measurable hAm a) hK (translated_coefficient_bound hAb a)
      (volumeTranslateJet a u) v i k))
  have horig := integrable_finset_sum Finset.univ (fun (i:Fin n) _=>integrable_finset_sum Finset.univ
    (fun (k:Fin n) _=>integrable_variable_energy_entry A hAm hK hAb (volumeTranslateJet a u) v i k))
  have hc : (∫ x,∑ i:Fin n,∑ k:Fin n,(A (x+a) i k-A x i k)*(volumeTranslateJet a u k.succ x)*v i.succ x)=
      (∫ x,∑ i:Fin n,∑ k:Fin n,A (x+a) i k*(volumeTranslateJet a u k.succ x)*v i.succ x)-
        ∫ x,∑ i:Fin n,∑ k:Fin n,A x i k*(volumeTranslateJet a u k.succ x)*v i.succ x := by
    rw [← integral_sub htrans horig]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    simp only [sub_mul,Finset.sum_sub_distrib]
  rw [hc,variableJetEnergy_translate_test,variableJetEnergy_integral]
  ring

end GaussianTilt.MomentMapLinearDirichlet
