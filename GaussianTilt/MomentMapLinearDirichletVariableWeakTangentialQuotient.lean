import GaussianTilt.MomentMapLinearDirichletVariableWeakTangentialEquation

/-! # The actual finite-difference weak divergence equation -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 1000

/-- Exact difference-quotient energy identity for the actual L² jets. -/
theorem variableJetEnergy_difference_quotient
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm:∀ i k,AEStronglyMeasurable (fun x=>A x i k) volume)
    {K:ℝ} (hK:0≤K) (hAb:∀ i k,∀ᵐ x∂volume,|A x i k|≤K)
    (i:Fin n) (h:ℝ) (u v:VolumeJet n) :
    variableJetEnergy A hAm hK hAb (h⁻¹ • (volumeTranslateJet (h • (Pi.single i 1:CoordinateSpace n)) u-u)) v=
      -variableJetEnergy A hAm hK hAb u
        ((-h)⁻¹ • (volumeTranslateJet ((-h) • (Pi.single i 1:CoordinateSpace n)) v-v))-
        ∫ x,∑ p:Fin n,∑ k:Fin n,(h⁻¹*(A (x+h • (Pi.single i 1:CoordinateSpace n)) p k-A x p k))*
          (volumeTranslateJet (h • (Pi.single i 1:CoordinateSpace n)) u k.succ x)*v p.succ x := by
  let a := h • (Pi.single i 1:CoordinateSpace n)
  let E := variableJetEnergy A hAm hK hAb
  let I := ∫ x,∑ p:Fin n,∑ k:Fin n,(A (x+a) p k-A x p k)*(volumeTranslateJet a u k.succ x)*v p.succ x
  have hleft : E (h⁻¹ • (volumeTranslateJet a u-u)) v=h⁻¹*(E (volumeTranslateJet a u) v-E u v) := by
    simp only [map_smul,map_sub,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,smul_eq_mul]
  have hright : E u ((-h)⁻¹ • (volumeTranslateJet (-a) v-v))= -h⁻¹*(E u (volumeTranslateJet (-a) v)-E u v) := by
    simp only [map_smul,map_sub,inv_neg,smul_eq_mul]
  have hcorr : (∫ x,∑ p:Fin n,∑ k:Fin n,(h⁻¹*(A (x+a) p k-A x p k))*
      (volumeTranslateJet a u k.succ x)*v p.succ x)=h⁻¹*I := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only [I]
    simp only [Finset.mul_sum,mul_assoc]
  have hcomm := variableJetEnergy_translate_commutator A hAm hK hAb a u v
  change E (volumeTranslateJet a u) v=E u (volumeTranslateJet (-a) v)-I at hcomm
  change E (h⁻¹ • (volumeTranslateJet a u-u)) v= -E u ((-h)⁻¹ • (volumeTranslateJet ((-h) • (Pi.single i 1:CoordinateSpace n)) v-v)) - _
  rw [neg_smul,hleft,hright,hcorr,hcomm]
  ring

/-- Applying the original weak equation to the actual backward difference
of an admissible H₀¹ test yields the differentiated equation. The scalar
forcing remains a true divergence load; no derivative of f is assumed. -/
theorem weak_divergence_difference_quotient {Ω U:Set (CoordinateSpace n)}
    (hU:U⊆Ω) (i:Fin n) (h:ℝ)
    (hshift:(fun x:CoordinateSpace n=>x+((-h) • (Pi.single i 1:CoordinateSpace n))) ⁻¹' U⊆Ω)
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm:∀ p k,AEStronglyMeasurable (fun x=>A x p k) volume)
    {K:ℝ} (hK:0≤K) (hAb:∀ p k,∀ᵐ x∂volume,|A x p k|≤K)
    (u:VolumeJet n) (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (hu:∀v:dirichletSobolev Ω,variableJetEnergy A hAm hK hAb u v.1=inner ℝ f (dirichletValue Ω v))
    (v:dirichletSobolev U) :
    variableJetEnergy A hAm hK hAb (h⁻¹ • (volumeTranslateJet (h • (Pi.single i 1:CoordinateSpace n)) u-u)) v.1=
      -inner ℝ f (dirichletDifferenceQuotient v i (-h))-
        ∫ x,∑ p:Fin n,∑ k:Fin n,(h⁻¹*(A (x+h • (Pi.single i 1:CoordinateSpace n)) p k-A x p k))*
          (volumeTranslateJet (h • (Pi.single i 1:CoordinateSpace n)) u k.succ x)*v.1 p.succ x := by
  let v₀:dirichletSobolev Ω := dirichletInclusion hU v
  let v₁:dirichletSobolev Ω := ⟨volumeTranslateJet ((-h) • (Pi.single i 1:CoordinateSpace n)) v.1,
    dirichletSobolev_mono hshift (volumeTranslateJet_mem_dirichlet _ v)⟩
  let q:dirichletSobolev Ω := (-h)⁻¹ • (v₁-v₀)
  have hq : q.1=(-h)⁻¹ • (volumeTranslateJet ((-h) • (Pi.single i 1:CoordinateSpace n)) v.1-v.1) := rfl
  have hqv : dirichletValue Ω q=dirichletDifferenceQuotient v i (-h) := by
    change ((-h)⁻¹ • (v₁.1-v₀.1)) 0=_
    simp only [PiLp.smul_apply,PiLp.sub_apply,volumeTranslateJet_apply]
    rfl
  rw [variableJetEnergy_difference_quotient,← hq,hu q,hqv]

end GaussianTilt.MomentMapLinearDirichlet
