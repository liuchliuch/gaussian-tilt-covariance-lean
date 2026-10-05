import GaussianTilt.MomentMapLinearDirichletVariableWeakAffineEnergy

/-! # Genuine H¹ Laplace harmonicity after frozen-SPD normalization -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 1000

lemma gradient_pairing_smooth_test (u:VolumeJet n) (τ:smoothCompactCore n) :
    (∑ i:Fin n,inner ℝ (u i.succ) (smoothCompactToL2 volume (smoothCompactDerivative i τ)))=
      ∫ x,(fun i:Fin n=>u i.succ x) ⬝ᵥ coordinateGradient τ.1 x := by
  simp_rw [inner_Lp_smoothCompactToL2]
  change (∑ i:Fin n,∫ x,u i.succ x*coordinateDerivative i τ.1 x)=_
  rw [← integral_finset_sum]
  · rfl
  · intro i _
    exact (Lp.memLp (u i.succ)).integrable_mul (smooth_compact_memLp
      (smooth_coordinateDerivative τ.2.1 i) (τ.2.2.fderiv_apply (𝕜:=ℝ) (Pi.single i 1)))

lemma weak_harmonic_all_dirichlet_tests {D:Set (CoordinateSpace n)} (u:VolumeJet n)
    (heq:∀τ:smoothCompactCore n,tsupport τ.1⊆D →
      (∫ x,(fun i:Fin n=>u i.succ x) ⬝ᵥ coordinateGradient τ.1 x)=0)
    (v:dirichletSobolev D) : (∑ i:Fin n,inner ℝ (u i.succ) (v.1 i.succ))=0 := by
  let F:VolumeJet n→L[ℝ]ℝ := ∑ i:Fin n,(innerSL ℝ (u i.succ)).comp (volumeJetDerivative i)
  have hF (z:VolumeJet n) : F z=∑ i:Fin n,inner ℝ (u i.succ) (z i.succ) := by
    simp only [F,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,innerSL_apply,
      volumeJetDerivative,PiLp.proj_apply]
  have hc : (LinearMap.range (dirichletJet D):Set (VolumeJet n))⊆{z|F z=0} := by
    rintro z ⟨τ,rfl⟩
    change F (dirichletJet D τ)=0
    rw [hF]
    change (∑ i:Fin n,inner ℝ (u i.succ) (smoothCompactJet volume τ.1 i.succ))=0
    simp only [smoothCompactJet_succ]
    rw [gradient_pairing_smooth_test]
    exact heq τ.1 τ.2
  have hh := closure_minimal hc (isClosed_eq F.continuous continuous_const) v.2
  simpa only [mem_setOf_eq,hF] using hh

/-- The full H¹ frozen-SPD normalization: an actual upper-domain jet is
pulled back and proved Laplace-harmonic against every H₀¹ half-ball test.
This is exactly the nonclassical input to odd reflection and harmonic decay. -/
theorem exists_affine_normalized_harmonic_jet {Ω D:Set (CoordinateSpace n)}
    (j:Fin n) (hΩ:Ω⊆{x:CoordinateSpace n|0<x j})
    (P:CoordinateSpace n ≃L[ℝ] CoordinateSpace n) {c R:ℝ} (hc:0<c) (hR:0<R)
    (hplane:∀x,(P x) j=c*x j) (hPD:MapsTo P (coordinateHalfBall j R) D)
    {B:Matrix (Fin n) (Fin n) ℝ}
    (hB:LinearMap.toMatrix' P.toLinearMap*(LinearMap.toMatrix' P.toLinearMap)ᵀ=B)
    (u:dirichletSobolev Ω)
    (heq:∀ξ:smoothCompactCore n,tsupport ξ.1⊆D →
      (∫ x,(fun i:Fin n=>u.1 i.succ x) ⬝ᵥ (B *ᵥ coordinateGradient ξ.1 x))=0) :
    ∃ v:dirichletSobolev {x:CoordinateSpace n|0<x j},
      (∀ᵐ x∂volume,x∈rawChartBall (n:=n) R → v.1 0 x=u.1 0 (P x)) ∧
      (∀ i,∀ᵐ x∂volume,x∈rawChartBall (n:=n) R →
        v.1 i.succ x=∑ k,LinearMap.toMatrix' P.toLinearMap k i*u.1 k.succ (P x)) ∧
      ∀ τ:dirichletSobolev (coordinateHalfBall j R),
        (∑ i:Fin n,inner ℝ (v.1 i.succ) (τ.1 i.succ))=0 := by
  obtain ⟨v,hval,hgrad⟩ := exists_halfspace_affine_sobolev_pullback j hΩ P hc hR hplane u
  refine ⟨v,hval,hgrad,?_⟩
  apply weak_harmonic_all_dirichlet_tests
  intro τ hτ
  have hh := frozen_affine_weak_harmonic P hPD hB (fun x i=>u.1 i.succ x) heq τ hτ
  apply Eq.trans ?_ hh
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hgrad] with x hx
  by_cases hxR:x∈rawChartBall (n:=n) R
  · have hg : (fun i:Fin n=>v.1 i.succ x)=(LinearMap.toMatrix' P.toLinearMap)ᵀ *ᵥ (fun i:Fin n=>u.1 i.succ (P x)) := by
      funext i
      exact hx i hxR
    rw [hg]
  · rw [coordinateGradient_eq_zero_off_support τ.1 (fun ht=>hxR (hτ ht).1),dotProduct_zero,dotProduct_zero]

end GaussianTilt.MomentMapLinearDirichlet
