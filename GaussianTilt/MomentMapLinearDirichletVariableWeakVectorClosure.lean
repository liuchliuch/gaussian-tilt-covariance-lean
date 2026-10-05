import GaussianTilt.MomentMapLinearDirichletVariableWeakTangentialLocalPDE

/-! # Genuine vector-load compact equations extend to all H₀¹ tests -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 1000

lemma vector_load_smooth_test (G:Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n))) (ψ:smoothCompactCore n) :
    (∑ i:Fin n,inner ℝ (G i) (smoothCompactToL2 volume (smoothCompactDerivative i ψ)))=
      ∫ x,∑ i:Fin n,G i x*coordinateDerivative i ψ.1 x := by
  simp_rw [inner_Lp_smoothCompactToL2]
  change (∑ i:Fin n,∫ x,G i x*coordinateDerivative i ψ.1 x)=_
  rw [← integral_finset_sum]
  intro i _
  exact (Lp.memLp (G i)).integrable_mul (smooth_compact_memLp
    (smooth_coordinateDerivative ψ.2.1 i) (ψ.2.2.fderiv_apply (𝕜:=ℝ) (Pi.single i 1)))

theorem weak_vector_equation_all_dirichlet_tests {U:Set (CoordinateSpace n)}
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm:∀ i k,AEStronglyMeasurable (fun x=>A x i k) volume)
    {K:ℝ} (hK:0≤K) (hAb:∀ i k,∀ᵐ x∂volume,|A x i k|≤K)
    (u:VolumeJet n) (G:Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (heq:∀ψ:smoothCompactCore n,tsupport ψ.1⊆U →
      (∫ x,∑ i:Fin n,∑ k:Fin n,A x i k*u k.succ x*coordinateDerivative i ψ.1 x)=
        ∫ x,∑ i:Fin n,G i x*coordinateDerivative i ψ.1 x)
    (v:dirichletSobolev U) :
    variableJetEnergy A hAm hK hAb u v.1=variableScalarVectorLoad U 0 G v := by
  let F:VolumeJet n→L[ℝ]ℝ := ∑ i:Fin n,(innerSL ℝ (G i)).comp (volumeJetDerivative i)
  have hF (z:VolumeJet n) : F z=∑ i:Fin n,inner ℝ (G i) (z i.succ) := by
    simp only [F,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,innerSL_apply,
      volumeJetDerivative,PiLp.proj_apply]
  have hc:(LinearMap.range (dirichletJet U):Set (VolumeJet n))⊆
      {z|variableJetEnergy A hAm hK hAb u z=F z} := by
    rintro z ⟨ψ,rfl⟩
    change variableJetEnergy A hAm hK hAb u (smoothCompactJet volume ψ.1)=F (smoothCompactJet volume ψ.1)
    rw [variableJetEnergy_smooth_test,hF]
    simp only [smoothCompactJet_succ]
    rw [vector_load_smooth_test]
    exact heq ψ.1 ψ.2
  have hh := closure_minimal hc
    (isClosed_eq (variableJetEnergy A hAm hK hAb u).continuous F.continuous) v.2
  change variableJetEnergy A hAm hK hAb u v.1=F v.1 at hh
  rw [variableScalarVectorLoad_apply,inner_zero_left,zero_add,← hF]
  exact hh

end GaussianTilt.MomentMapLinearDirichlet
