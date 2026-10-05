import GaussianTilt.MomentMapLinearDirichletVariableWeakExtension

/-! # Extending the actual transformed compact-test equation to H₀¹ tests -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 1000

lemma variableJetEnergy_smooth_test
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm: ∀ i k,AEStronglyMeasurable (fun x=>A x i k) volume)
    {K:ℝ} (hK:0 ≤ K) (hAb: ∀ i k, ∀ᵐx∂volume,|A x i k| ≤ K)
    (u:VolumeJet n) (τ:smoothCompactCore n) :
    variableJetEnergy A hAm hK hAb u (smoothCompactJet volume τ)=
       ∫ x, ∑ i:Fin n, ∑ k:Fin n,A x i k*u k.succ x*coordinateDerivative i τ.1 x  :=  by
  rw [variableJetEnergy_integral]
  apply integral_congr_ae
  have hτeach (i : Fin n) : ∀ᵐ x∂(volume : Measure (CoordinateSpace n)),
      smoothCompactJet volume τ i.succ x = coordinateDerivative i τ.1 x :=
    by simpa only [smoothCompactJet_succ] using smoothCompactToL2_ae (volume : Measure (CoordinateSpace n)) (smoothCompactDerivative i τ)
  have hτall := ae_all_iff.mpr hτeach
  filter_upwards [hτall] with x hx
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [show smoothCompactJet volume τ i.succ x=coordinateDerivative i τ.1 x from hx i]

/-- The weak compact-test equation determines the equation against every
actual H₀¹ test, by closure in the genuine value/gradient graph. -/
theorem weak_divergence_equation_all_dirichlet_tests {Ω:Set (CoordinateSpace n)}
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm: ∀ i k,AEStronglyMeasurable (fun x=>A x i k) volume)
    {K:ℝ} (hK:0 ≤ K) (hAb: ∀ i k, ∀ᵐx∂volume,|A x i k| ≤ K)
    (u:VolumeJet n) (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (hweak: ∀ τ:smoothCompactCore n,tsupport τ.1⊆Ω  → 
      ( ∫ x, ∑ i:Fin n, ∑ k:Fin n,A x i k*u k.succ x*coordinateDerivative i τ.1 x)= ∫ x,f x*τ.1 x)
    (v:dirichletSobolev Ω) :
    variableJetEnergy A hAm hK hAb u v.1=inner ℝ f (dirichletValue Ω v)  :=  by
  let Q:VolumeJet n →L[ℝ]Lp ℝ 2 (volume:Measure (CoordinateSpace n))  := 
    PiLp.proj 2 (fun _ : Fin (n+1)=>Lp ℝ 2 (volume:Measure (CoordinateSpace n))) 0
  let F:VolumeJet n →L[ℝ]ℝ  :=  (innerSL ℝ f).comp Q
  have hclosed:IsClosed {z:VolumeJet n|variableJetEnergy A hAm hK hAb u z=F z}  := 
    isClosed_eq (variableJetEnergy A hAm hK hAb u).continuous F.continuous
  have hc:(LinearMap.range (dirichletJet Ω):Set (VolumeJet n))⊆
      {z:VolumeJet n|variableJetEnergy A hAm hK hAb u z=F z}  :=  by
    rintro z ⟨τ,rfl⟩
    change variableJetEnergy A hAm hK hAb u (smoothCompactJet volume τ.1)=
      inner ℝ f (smoothCompactToL2 volume τ.1)
    rw [variableJetEnergy_smooth_test,inner_Lp_smoothCompactToL2]
    exact hweak τ.1 τ.2
  exact closure_minimal hc hclosed v.2

/-- Coefficients and forcing can be changed outside the compact test domain;
the literal equation only sees their actual values in that domain. -/
lemma weak_compact_equation_congr_on_domain {Ω : Set (CoordinateSpace n)}
    {A B : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {f g : CoordinateSpace n → ℝ} (hAB : ∀ x∈Ω, A x=B x)
    (hfg : ∀ᵐ x∂volume, x∈Ω → f x=g x) (u : VolumeJet n)
    (hw : ∀ τ:smoothCompactCore n, tsupport τ.1⊆Ω →
      (∫ x, ∑ i:Fin n, ∑ k:Fin n, A x i k*u k.succ x*coordinateDerivative i τ.1 x)=∫ x,f x*τ.1 x)
    (τ : smoothCompactCore n) (hτ : tsupport τ.1⊆Ω) :
      (∫ x, ∑ i:Fin n, ∑ k:Fin n, B x i k*u k.succ x*coordinateDerivative i τ.1 x)=∫ x,g x*τ.1 x := by
  calc
    _ = ∫ x, ∑ i:Fin n, ∑ k:Fin n, A x i k*u k.succ x*coordinateDerivative i τ.1 x := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      by_cases hx:x∈Ω
      · dsimp only
        rw [hAB x hx]
      · have hg := coordinateGradient_eq_zero_off_support τ.1 (fun hh=>hx (hτ hh))
        apply Finset.sum_congr rfl
        intro i _
        have hi := congrFun hg i
        change coordinateDerivative i τ.1 x=0 at hi
        simp only [hi,mul_zero,Finset.sum_const_zero]
    _ = ∫ x,f x*τ.1 x := hw τ hτ
    _ = ∫ x,g x*τ.1 x := by
      apply integral_congr_ae
      filter_upwards [hfg] with x hx
      by_cases hxΩ:x∈Ω
      · rw [hx hxΩ]
      · rw [image_eq_zero_of_notMem_tsupport (fun hh=>hxΩ (hτ hh)),mul_zero,mul_zero]

end GaussianTilt.MomentMapLinearDirichlet
