import GaussianTilt.MomentMapLinearDirichletVariableWeakAffineSubtraction
import GaussianTilt.MomentMapLinearDirichletVariableWeakVectorClosure

/-! # Actual local weak equation after compact affine subtraction -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapElliptic
variable {n : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 1000

def constantGradientJet (D:Set (CoordinateSpace n)) (hD:MeasurableSet D)
    (hfin:(volume:Measure (CoordinateSpace n)) D≠⊤) (p:KernelSpace n) : VolumeJet n :=
  WithLp.toLp 2 (Fin.cases 0 (fun k=>constantDomainL2 D hD hfin (p k)))

@[simp] lemma constantGradientJet_succ (D:Set (CoordinateSpace n)) (hD:MeasurableSet D)
    (hfin:(volume:Measure (CoordinateSpace n)) D≠⊤) (p:KernelSpace n) (i:Fin n) :
    constantGradientJet D hD hfin p i.succ=constantDomainL2 D hD hfin (p i) := rfl

/-- The new vector forcing is an actual L² function, masked only outside
the working ball, and the affine-subtracted jet obeys its literal equation. -/
theorem exists_dirichlet_affine_subtraction_equation {Ω:Set (CoordinateSpace n)}
    (a p:KernelSpace n) {r:ℝ} (hr:0<r) (hball:coordinateFullBall a (2*r)⊆Ω)
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm:∀ i k,AEStronglyMeasurable (fun x=>A x i k) volume)
    {K:ℝ} (hK:0≤K) (hAb:∀ i k,∀ᵐ x∂volume,|A x i k|≤K)
    (u:dirichletSobolev Ω) (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (G:Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (heq:∀τ:dirichletSobolev (coordinateFullBall a r),
      variableJetEnergy A hAm hK hAb u.1 τ.1=variableScalarVectorLoad (coordinateFullBall a r) f G τ) :
    ∃v:dirichletSobolev Ω,∃G':Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n)),
      (∀ᵐx∂volume,x∈coordinateFullBall a r → v.1 0 x=u.1 0 x-centeredAffineFunction a p x) ∧
      (∀i,∀ᵐx∂volume,x∈coordinateFullBall a r → v.1 i.succ x=u.1 i.succ x-p i) ∧
      (∀ᵐx∂(volume:Measure (KernelSpace n)),x∈Metric.ball a r → euclideanWeakGradient v.1 x=euclideanWeakGradient u.1 x-p) ∧
      (∀i,∀ᵐx∂volume,x∈coordinateFullBall a r → G' i x=G i x-∑ k:Fin n,A x i k*p k) ∧
      ∀τ:dirichletSobolev (coordinateFullBall a r),
        variableJetEnergy A hAm hK hAb v.1 τ.1=variableScalarVectorLoad (coordinateFullBall a r) f G' τ := by
  obtain ⟨v,hv0,hvD,hvE⟩ := exists_dirichlet_affine_subtraction a p hr hball u
  let D := coordinateFullBall a r
  have hD:MeasurableSet D := (isOpen_coordinateFullBall a r).measurableSet
  have hfin:(volume:Measure (CoordinateSpace n)) D≠⊤ := (isBounded_coordinateFullBall a r).measure_lt_top.ne
  let P := constantGradientJet D hD hfin p
  let Q:Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n)) := fun i=>
    ∑ k:Fin n,boundedL2Multiplier (hAm i k) hK (hAb i k) (P k.succ)
  let G':Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n)) := fun i=>G i-Q i
  have hP (k:Fin n) : ∀ᵐx∂volume,x∈D → P k.succ x=p k := by
    filter_upwards [constantDomainL2_ae D hD hfin (p k)] with x hx hxD
    change constantDomainL2 D hD hfin (p k) x=_
    simpa only [indicator_of_mem hxD] using hx
  have hQ (i:Fin n) : ∀ᵐx∂volume,x∈D → Q i x=∑k:Fin n,A x i k*p k := by
    have hm := ae_all_iff.mpr (fun k:Fin n=>boundedL2Multiplier_ae (hAm i k) hK (hAb i k) (P k.succ))
    filter_upwards [Lp_coeFn_finset_sum (fun k=>boundedL2Multiplier (hAm i k) hK (hAb i k) (P k.succ)) Finset.univ,
      hm,ae_all_iff.mpr hP] with x hx hm hp hxD
    change (∑k:Fin n,boundedL2Multiplier (hAm i k) hK (hAb i k) (P k.succ)) x=_
    rw [hx]
    apply Finset.sum_congr rfl
    intro k _
    rw [hm k,hp k hxD]
  have hG' (i:Fin n) : ∀ᵐx∂volume,x∈D → G' i x=G i x-∑k:Fin n,A x i k*p k := by
    filter_upwards [Lp.coeFn_sub (G i) (Q i),hQ i] with x hx hqx hxD
    change (G i-Q i) x=_
    rw [hx]
    simp only [Pi.sub_apply,hqx hxD]
  refine ⟨v,G',hv0,hvD,hvE,hG',?_⟩
  intro τ
  have hlocal : variableJetEnergy A hAm hK hAb v.1 τ.1=
      variableJetEnergy A hAm hK hAb (u.1-P) τ.1 := by
    rw [variableJetEnergy_integral,variableJetEnergy_integral]
    have hz := ae_all_iff.mpr (fun i:Fin n=>dirichletGradient_ae_zero_outside hD τ i)
    have hsub := ae_all_iff.mpr (fun k:Fin n=>Lp.coeFn_sub (u.1 k.succ) (P k.succ))
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hvD,ae_all_iff.mpr hP,hz,hsub] with x hvx hpx hzx hsx
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    by_cases hx:x∈D
    · change A x i k*v.1 k.succ x*τ.1 i.succ x=A x i k*(u.1 k.succ-P k.succ) x*τ.1 i.succ x
      rw [hsx k]
      simp only [Pi.sub_apply,hvx k hx,hpx k hx]
    · rw [hzx i hx,mul_zero,mul_zero]
  have hPQ : variableJetEnergy A hAm hK hAb P τ.1=∑i:Fin n,inner ℝ (Q i) (τ.1 i.succ) := by
    simp only [variableJetEnergy,ContinuousLinearMap.sum_apply,ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.comp_apply,volumeJetDerivative,PiLp.proj_apply,innerSL_apply,Q,sum_inner]
  have hload : variableScalarVectorLoad D f G' τ=variableScalarVectorLoad D f G τ-variableJetEnergy A hAm hK hAb P τ.1 := by
    rw [variableScalarVectorLoad_apply,variableScalarVectorLoad_apply,hPQ]
    simp only [G',inner_sub_left,Finset.sum_sub_distrib]
    ring
  rw [hlocal,map_sub,ContinuousLinearMap.sub_apply,heq τ,← hload]

end GaussianTilt.MomentMapLinearDirichlet
