import GaussianTilt.MomentMapLinearDirichletVariableWeakVectorClosure

/-! # The actual L² divergence load of the tangential derivative -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 1000

/-- A locally bounded coefficient derivative times the true weak gradient
constructs an actual L² vector load, with the exact compact-test formula. -/
theorem exists_differentiated_vector_load {U:Set (CoordinateSpace n)} (hU:MeasurableSet U)
    (a:Fin n) (D:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hDm:∀ i k,AEStronglyMeasurable (fun x=>D x i k) (volume.restrict U))
    {L:ℝ} (hL:0≤L) (hDb:∀ x∈U,∀ i k,|D x i k|≤L)
    (u:VolumeJet n) (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n))) :
    ∃ G:Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n)),
      (∀ i,∀ᵐ x∂volume,x∈U → G i x= -(if i=a then f x else 0)-∑ k:Fin n,D x i k*u k.succ x) ∧
      ∀ ψ:smoothCompactCore n,tsupport ψ.1⊆U →
        (∫ x,∑ i:Fin n,G i x*coordinateDerivative i ψ.1 x)=
          -(∫ x,f x*coordinateDerivative a ψ.1 x)-
          ∫ x,∑ i:Fin n,∑ k:Fin n,D x i k*u k.succ x*coordinateDerivative i ψ.1 x := by
  let C:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ := fun x i k=>U.indicator (fun y=>D y i k) x
  have hCm (i k:Fin n) : AEStronglyMeasurable (fun x=>C x i k) volume :=
    (aestronglyMeasurable_indicator_iff hU).mpr (hDm i k)
  have hCb (i k:Fin n) : ∀ᵐ x∂volume,|C x i k|≤L := by
    apply ae_of_all
    intro x
    by_cases hx:x∈U
    · simpa only [C,indicator_of_mem hx] using hDb x hx i k
    · simpa only [C,indicator_of_notMem hx,abs_zero] using hL
  let γ:Fin n → CoordinateSpace n → ℝ := fun i x=> -(if i=a then f x else 0)-∑ k:Fin n,C x i k*u k.succ x
  have hγ (i:Fin n) : MemLp (γ i) 2 volume := by
    have hs : MemLp (fun x=>∑ k:Fin n,C x i k*u k.succ x) 2 volume :=
      memLp_finset_sum Finset.univ (fun k _=>boundedMultiplier_memLp (hCm i k) (hCb i k) (u k.succ))
    have hf : MemLp (fun x=>if i=a then f x else (0:ℝ)) 2 volume := by
      by_cases hi:i=a
      · simpa only [if_pos hi] using Lp.memLp f
      · simpa only [if_neg hi] using (MemLp.zero : MemLp (0:CoordinateSpace n → ℝ) 2 volume)
    exact hf.neg.sub hs
  let G:Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n)) := fun i=>(hγ i).toLp (γ i)
  have hGe (i:Fin n) : G i=ᵐ[volume] γ i := (hγ i).coeFn_toLp
  refine ⟨G,?_,?_⟩
  · intro i
    filter_upwards [hGe i] with x hx hxU
    simpa only [γ,C,indicator_of_mem hxU] using hx
  · intro ψ hψ
    have hIf : Integrable (fun x=>f x*coordinateDerivative a ψ.1 x) :=
      (Lp.memLp f).integrable_mul (smooth_compact_memLp (smooth_coordinateDerivative ψ.2.1 a)
        (ψ.2.2.fderiv_apply (𝕜:=ℝ) (Pi.single a 1)))
    have hIc (i k:Fin n) : Integrable (fun x=>C x i k*u k.succ x*coordinateDerivative i ψ.1 x) :=
      (boundedMultiplier_memLp (hCm i k) (hCb i k) (u k.succ)).integrable_mul
        (smooth_compact_memLp (smooth_coordinateDerivative ψ.2.1 i)
          (ψ.2.2.fderiv_apply (𝕜:=ℝ) (Pi.single i 1)))
    have hI : Integrable (fun x=>∑ i:Fin n,∑ k:Fin n,C x i k*u k.succ x*coordinateDerivative i ψ.1 x) :=
      integrable_finset_sum Finset.univ (fun i _=>integrable_finset_sum Finset.univ (fun k _=>hIc i k))
    have hpair : (∫ x,∑ i:Fin n,G i x*coordinateDerivative i ψ.1 x)=
        -(∫ x,f x*coordinateDerivative a ψ.1 x)-
        ∫ x,∑ i:Fin n,∑ k:Fin n,C x i k*u k.succ x*coordinateDerivative i ψ.1 x := by
      have hIfn : Integrable (fun x => -(f x*coordinateDerivative a ψ.1 x)) := hIf.neg
      rw [← integral_neg,← integral_sub hIfn hI]
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hGe] with x hx
      try dsimp only
      simp only [hx,γ,sub_mul,neg_mul,Finset.sum_sub_distrib,Finset.sum_neg_distrib,
        Finset.sum_mul,ite_mul,zero_mul]
      simp
    have hCD (x:CoordinateSpace n) (hx:x∈U) (i k:Fin n) : C x i k=D x i k := by simp only [C,indicator_of_mem hx]
    rw [weak_matrix_energy_congr_support hCD (fun k x=>u k.succ x)
      (fun i=>coordinateDerivative i ψ.1) (fun i=>(coordinateDerivative_tsupport_subset ψ.1 i).trans hψ)] at hpair
    exact hpair

/-- The constructed tangential H¹ derivative satisfies the exact genuine
all-H₀¹ divergence equation with zero scalar load and the actual L² vector
load Gᵢ=−δᵢₐf−Σₖ(∂ₐAᵢₖ)uₖ. -/
theorem exists_differentiated_vector_equation {Ω Ω' U:Set (CoordinateSpace n)}
    (hU:IsOpen U) (u:dirichletSobolev Ω) (w:dirichletSobolev Ω') (a:Fin n)
    (hval:∀ᵐ x∂volume,x∈U → w.1 0 x=u.1 a.succ x)
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hA:∀ i k,ContDiffOn ℝ ∞ (fun x=>A x i k) U)
    (hAm:∀ i k,AEStronglyMeasurable (fun x=>A x i k) volume)
    {K L:ℝ} (hK:0≤K) (hL:0≤L) (hAb:∀ i k,∀ᵐ x∂volume,|A x i k|≤K)
    (hD:∀ x∈U,∀ i k,|coordinateDerivative a (fun y=>A y i k) x|≤L)
    (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (heq:∀ψ:smoothCompactCore n,tsupport ψ.1⊆U →
      (∫ x,∑ i:Fin n,∑ k:Fin n,A x i k*u.1 k.succ x*coordinateDerivative i ψ.1 x)=∫ x,f x*ψ.1 x) :
    ∃ G:Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n)),
      (∀ i,∀ᵐ x∂volume,x∈U → G i x= -(if i=a then f x else 0)-
        ∑ k:Fin n,coordinateDerivative a (fun y=>A y i k) x*u.1 k.succ x) ∧
      ∀ v:dirichletSobolev U,variableJetEnergy A hAm hK hAb w.1 v.1=variableScalarVectorLoad U 0 G v := by
  have hDm (i k:Fin n) : AEStronglyMeasurable (coordinateDerivative a (fun y=>A y i k)) (volume.restrict U) := by
    have hc : ContDiffOn ℝ ∞ (coordinateDerivative a (fun y=>A y i k)) U :=
      ((hA i k).fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    exact hc.continuousOn.aestronglyMeasurable hU.measurableSet
  obtain ⟨G,hG,hpair⟩ := exists_differentiated_vector_load hU.measurableSet a
    (fun x i k=>coordinateDerivative a (fun y=>A y i k) x) hDm hL hD u.1 f
  refine ⟨G,hG,?_⟩
  apply weak_vector_equation_all_dirichlet_tests A hAm hK hAb w.1 G
  intro ψ hψ
  exact (weak_divergence_differentiated_local hU u w a hval A hA f heq ψ hψ).trans (hpair ψ hψ).symm

end GaussianTilt.MomentMapLinearDirichlet
