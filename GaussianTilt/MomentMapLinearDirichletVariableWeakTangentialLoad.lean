import GaussianTilt.MomentMapLinearDirichletVariableWeakTangentialQuotient
import GaussianTilt.MomentMapLinearDirichletH1ZeroExtension

/-! # Uniform localized load bound for the actual tangential quotient equation -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 1000

@[simp] lemma jetGradientNorm_volumeTranslateJet (a:CoordinateSpace n) (u:VolumeJet n) :
    jetGradientNorm (volumeTranslateJet a u)=jetGradientNorm u := by
  simp only [jetGradientNorm,volumeTranslateJet_apply,norm_volumeTranslate]

/-- Only the actual coefficient quotient on the support of the H₀¹ test
is used. Its exterior is masked by the proved zero exterior weak gradient. -/
theorem coefficient_quotient_pairing_bound {U:Set (CoordinateSpace n)} (hU:MeasurableSet U)
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm:∀ p k,AEStronglyMeasurable (fun x=>A x p k) volume)
    (i:Fin n) (h:ℝ) {L:ℝ} (hL:0≤L)
    (hquot:∀ x∈U,∀ p k,|h⁻¹*(A (x+h • (Pi.single i 1:CoordinateSpace n)) p k-A x p k)|≤L)
    (u:VolumeJet n) (v:dirichletSobolev U) :
    |∫ x,∑ p:Fin n,∑ k:Fin n,(h⁻¹*(A (x+h • (Pi.single i 1:CoordinateSpace n)) p k-A x p k))*
      (volumeTranslateJet (h • (Pi.single i 1:CoordinateSpace n)) u k.succ x)*v.1 p.succ x| ≤
      (n:ℝ)^2*L*jetGradientNorm u*jetGradientNorm v.1 := by
  let a := h • (Pi.single i 1:CoordinateSpace n)
  let Q:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ := fun x p k=>
    U.indicator (fun y=>h⁻¹*(A (y+a) p k-A y p k)) x
  have hQm (p k:Fin n) : AEStronglyMeasurable (fun x=>Q x p k) volume :=
    (((translated_coefficient_measurable hAm a p k).sub (hAm p k)).const_mul h⁻¹).indicator hU
  have hQb (p k:Fin n) : ∀ᵐ x∂volume,|Q x p k|≤L := by
    apply ae_of_all
    intro x
    by_cases hx:x∈U
    · simpa only [Q,indicator_of_mem hx] using hquot x hx p k
    · simpa only [Q,indicator_of_notMem hx,abs_zero] using hL
  have hv := ae_all_iff.mpr (fun p:Fin n=>dirichletGradient_ae_zero_outside hU v p)
  have he : (∫ x,∑ p:Fin n,∑ k:Fin n,(h⁻¹*(A (x+a) p k-A x p k))*
      (volumeTranslateJet a u k.succ x)*v.1 p.succ x)=variableJetEnergy Q hQm hL hQb (volumeTranslateJet a u) v.1 := by
    rw [variableJetEnergy_integral]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    by_cases hxU:x∈U
    · simp only [Q,indicator_of_mem hxU]
    · have hz (p:Fin n) : v.1 p.succ x=0 := hx p hxU
      simp only [hz,mul_zero,Finset.sum_const_zero]
  change |∫ x,∑ p:Fin n,∑ k:Fin n,(h⁻¹*(A (x+a) p k-A x p k))*
      (volumeTranslateJet a u k.succ x)*v.1 p.succ x|≤_
  rw [he]
  simpa only [jetGradientNorm_volumeTranslateJet] using
    variableJetEnergy_abs_le_gradient Q hQm hL hQb (volumeTranslateJet a u) v.1

/-- A genuine uniform tangential Caccioppoli load estimate. The scalar
forcing is only L², and the coefficient modulus is required only locally. -/
theorem weak_divergence_difference_quotient_load_bound {Ω U:Set (CoordinateSpace n)}
    (hUm:MeasurableSet U) (hU:U⊆Ω) (i:Fin n) (h:ℝ)
    (hshift:(fun x:CoordinateSpace n=>x+((-h) • (Pi.single i 1:CoordinateSpace n))) ⁻¹' U⊆Ω)
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm:∀ p k,AEStronglyMeasurable (fun x=>A x p k) volume)
    {K L:ℝ} (hK:0≤K) (hL:0≤L) (hAb:∀ p k,∀ᵐ x∂volume,|A x p k|≤K)
    (hquot:∀ x∈U,∀ p k,|h⁻¹*(A (x+h • (Pi.single i 1:CoordinateSpace n)) p k-A x p k)|≤L)
    (u:VolumeJet n) (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (hu:∀v:dirichletSobolev Ω,variableJetEnergy A hAm hK hAb u v.1=inner ℝ f (dirichletValue Ω v))
    (v:dirichletSobolev U) :
    |variableJetEnergy A hAm hK hAb (h⁻¹ • (volumeTranslateJet (h • (Pi.single i 1:CoordinateSpace n)) u-u)) v.1| ≤
      (‖f‖+(n:ℝ)^2*L*jetGradientNorm u)*jetGradientNorm v.1 := by
  rw [weak_divergence_difference_quotient hU i h hshift A hAm hK hAb u f hu v]
  have hs : |inner ℝ f (dirichletDifferenceQuotient v i (-h))| ≤ ‖f‖*jetGradientNorm v.1 :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      ((norm_dirichletDifferenceQuotient_le v i (-h)).trans (norm_jetDerivative_le_gradient v.1 i)) (norm_nonneg f))
  have hc := coefficient_quotient_pairing_bound hUm A hAm i h hL hquot u v
  apply (abs_sub _ _).trans
  rw [abs_neg]
  exact (add_le_add hs hc).trans_eq (by ring)

end GaussianTilt.MomentMapLinearDirichlet
