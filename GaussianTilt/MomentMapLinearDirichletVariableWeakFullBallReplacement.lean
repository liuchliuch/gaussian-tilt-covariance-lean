import GaussianTilt.MomentMapLinearDirichletVariableWeakCenteredLoads
import GaussianTilt.MomentMapLinearDirichletLocalCoefficients

/-! # Actual centered full-ball replacement with local coefficients and sharp loads -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000

def coordinateFullBall (a:KernelSpace n) (r:ℝ) : Set (CoordinateSpace n) :=
  (dirichletCoordinateEquiv n).symm ⁻¹' Metric.ball a r

lemma isOpen_coordinateFullBall (a:KernelSpace n) (r:ℝ) : IsOpen (coordinateFullBall a r) :=
  Metric.isOpen_ball.preimage (dirichletCoordinateEquiv n).symm.continuous

lemma isBounded_coordinateFullBall (a:KernelSpace n) (r:ℝ) : Bornology.IsBounded (coordinateFullBall a r) := by
  apply ((isCompact_closedBall a r).image (dirichletCoordinateEquiv n).continuous).isBounded.subset
  intro x hx
  exact ⟨(dirichletCoordinateEquiv n).symm x,Metric.ball_subset_closedBall hx,
    (dirichletCoordinateEquiv n).apply_symm_apply x⟩

lemma coordinateFullBall_translated_strip (a:KernelSpace n) (i:Fin n) {r:ℝ} {x:CoordinateSpace n}
    (hx:x∈coordinateFullBall a r) : |x i-(dirichletCoordinateEquiv n a) i|≤r := by
  have hn := PiLp.norm_apply_le ((dirichletCoordinateEquiv n).symm x-a) i
  have hd : ‖(dirichletCoordinateEquiv n).symm x-a‖<r := by simpa only [coordinateFullBall,mem_preimage,Metric.mem_ball,dist_eq_norm] using hx
  exact hn.trans hd.le

lemma coordinateFullBall_global_strip (a:KernelSpace n) (i:Fin n) {r:ℝ} {x:CoordinateSpace n}
    (hx:x∈coordinateFullBall a r) : |x i|≤r+|a i| := by
  have hh := coordinateFullBall_translated_strip a i hx
  have ht := abs_add_le (x i-a i) (a i)
  simp only [sub_add_cancel] at ht
  exact ht.trans (add_le_add_right hh _)

lemma coordinateFullBall_real_volume [NeZero n] (a:KernelSpace n) {r:ℝ} (hr:0≤r) :
    volume.real (coordinateFullBall a r)=volume.real (Metric.ball (0:KernelSpace n) 1)*r^n := by
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have he := congrArg ENNReal.toReal (hμ.measure_preimage (isOpen_coordinateFullBall a r).measurableSet.nullMeasurableSet)
  have hpre : (dirichletCoordinateEquiv n) ⁻¹' coordinateFullBall a r=Metric.ball a r := by
    ext x
    simp only [coordinateFullBall,mem_preimage,ContinuousLinearEquiv.symm_apply_apply]
  rw [hpre] at he
  change volume.real (Metric.ball a r)=volume.real (coordinateFullBall a r) at he
  rw [← he,real_volume_euclidean_ball a hr]
  ring

theorem exists_centered_fullBall_harmonic_replacement [NeZero n]
    (a : KernelSpace n) {r β F H : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hF : 0 ≤ F) (hH : 0 ≤ H)
    (A B : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    (hBm : ∀ i k, AEStronglyMeasurable (fun x => B x i k) volume)
    {KA KB δ lam : ℝ} (hKA : 0 ≤ KA) (hKB : 0 ≤ KB) (hδ : 0 ≤ δ) (hlam : 0 < lam)
    (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ KA)
    (hBb : ∀ i k, ∀ᵐ x ∂volume, |B x i k| ≤ KB)
    (hDb : ∀ i k, ∀ᵐ x ∂volume, |B x i k-A x i k| ≤ δ)
    (hellB : ∀ᵐ x ∂volume, ∀ z : Fin n → ℝ, lam*(∑ i,(z i)^2) ≤ z ⬝ᵥ (B x *ᵥ z))
    (u : VolumeJet n) (hu : u ∈ weightedSobolev (volume : Measure (CoordinateSpace n)))
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (c : Fin n → ℝ)
    (hf : ∀ᵐ x ∂volume, x ∈ coordinateFullBall a r → |f x| ≤ F)
    (hG : ∀ k, ∀ᵐ x ∂volume, x ∈ coordinateFullBall a r → |G k x-c k| ≤ H*r^β)
    (heq : ∀ v : dirichletSobolev (coordinateFullBall a r),
      variableJetEnergy A hAm hKA hAb u v.1 = variableScalarVectorLoad (coordinateFullBall a r) f G v) :
    ∃ w : dirichletSobolev (coordinateFullBall a r),
      (u-w.1) ∈ weightedSobolev (volume : Measure (CoordinateSpace n)) ∧
      (∀ v : dirichletSobolev (coordinateFullBall a r), variableJetEnergy B hBm hKB hBb (u-w.1) v.1=0) ∧
      dirichletEnergy (coordinateFullBall a r) w w ≤
        (2*(n:ℝ)^4/lam^2)*δ^2*(∫ x in coordinateFullBall a r, ∑ i : Fin n,(u i.succ x)^2)+
        ((2/lam^2)*(2*F+(n:ℝ)*H)^2*volume.real (Metric.ball (0 : KernelSpace n) 1))*r^((n:ℝ)+2*β) := by
  let Ω := coordinateFullBall a r
  let j : Fin n := ⟨0,NeZero.pos n⟩
  have hΩm : MeasurableSet Ω := (isOpen_coordinateFullBall a r).measurableSet
  have hΩb : Bornology.IsBounded Ω := isBounded_coordinateFullBall a r
  have hfin : (volume : Measure (CoordinateSpace n)) Ω ≠ ∞ := hΩb.measure_lt_top.ne
  let L := (2*r*F+(n:ℝ)*H*r^β)*Real.sqrt (volume.real Ω)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hΦ : ∀ v : dirichletSobolev Ω, |variableScalarVectorLoad Ω f G v| ≤ L*jetGradientNorm v.1 :=
    variableScalarVectorLoad_abs_le_translated_centered hΩm hΩb hfin j (dirichletCoordinateEquiv n a) hr.le hF hH
      (fun x hx => coordinateFullBall_translated_strip a j hx) f G c hf hG
  obtain ⟨w,hw,hharm,hwnorm,hwE⟩ := exists_frozen_harmonic_replacement_local j (show 0 ≤ r+|a j| from add_nonneg hr.le (abs_nonneg _))
    (fun x hx => coordinateFullBall_global_strip a j hx) hΩm A B hAm hBm hKA hKB hδ hlam hL
    hAb hBb hDb hellB u hu (variableScalarVectorLoad Ω f G) hΦ heq
  have hload : L^2 ≤ ((2*F+(n:ℝ)*H)^2*volume.real (Metric.ball (0 : KernelSpace n) 1))*r^((n:ℝ)+2*β) :=
    centered_load_coefficient_sq_bound hr hr1 hF hH hβ hβ1 ENNReal.toReal_nonneg
      (coordinateFullBall_real_volume a hr.le).le
  have hs := replacement_square_split n (F := L) (δ := δ)
    (E := restrictedJetGradientNorm Ω hΩm u) hlam
  have hforce := mul_le_mul_of_nonneg_left hload (show 0 ≤ 2/lam^2 by positivity)
  refine ⟨w,hw,hharm,?_⟩
  apply (hwE.trans hs).trans
  rw [restrictedJetGradientNorm_sq Ω hΩm u]
  nlinarith only [hforce]


theorem exists_local_centered_fullBall_harmonic_replacement [NeZero n]
    (a : KernelSpace n) {r β F H : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hF : 0 ≤ F) (hH : 0 ≤ H)
    (A B : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    (hBm : ∀ i k, AEStronglyMeasurable (fun x => B x i k) volume)
    {KA KB δ lam : ℝ} (hKA : 0 ≤ KA) (hKB : 0 ≤ KB) (hδ : 0 ≤ δ) (hlam : 0 < lam)
    (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ KA)
    (hBb : ∀ i k, ∀ᵐ x ∂volume, |B x i k| ≤ KB)
    (hDb : ∀ i k, ∀ᵐ x ∂volume, x ∈ coordinateFullBall a r → |B x i k-A x i k| ≤ δ)
    (hellB : ∀ᵐ x ∂volume, ∀ z : Fin n → ℝ, lam*(∑ i,(z i)^2) ≤ z ⬝ᵥ (B x *ᵥ z))
    (u : VolumeJet n) (hu : u ∈ weightedSobolev (volume : Measure (CoordinateSpace n)))
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (c : Fin n → ℝ)
    (hf : ∀ᵐ x ∂volume, x ∈ coordinateFullBall a r → |f x| ≤ F)
    (hG : ∀ k, ∀ᵐ x ∂volume, x ∈ coordinateFullBall a r → |G k x-c k| ≤ H*r^β)
    (heq : ∀ v : dirichletSobolev (coordinateFullBall a r),
      variableJetEnergy A hAm hKA hAb u v.1 = variableScalarVectorLoad (coordinateFullBall a r) f G v) :
    ∃ w : dirichletSobolev (coordinateFullBall a r),
      (u-w.1) ∈ weightedSobolev (volume : Measure (CoordinateSpace n)) ∧
      (∀ v : dirichletSobolev (coordinateFullBall a r), variableJetEnergy B hBm hKB hBb (u-w.1) v.1=0) ∧
      dirichletEnergy (coordinateFullBall a r) w w ≤
        (2*(n:ℝ)^4/lam^2)*δ^2*(∫ x in coordinateFullBall a r, ∑ i : Fin n,(u i.succ x)^2)+
        ((2/lam^2)*(2*F+(n:ℝ)*H)^2*volume.real (Metric.ball (0 : KernelSpace n) 1))*r^((n:ℝ)+2*β) := by
  let Ω := coordinateFullBall a r
  have hΩ : MeasurableSet Ω := (isOpen_coordinateFullBall a r).measurableSet
  have hLA := localFrozenCoefficient_measurable hΩ A B hAm hBm
  have hLB := localFrozenCoefficient_bound (Ω := Ω) A B hAb hBb
  have hLD := localFrozenCoefficient_difference (Ω := Ω) A B hδ hDb
  have hLK : 0 ≤ max KA KB := hKA.trans (le_max_left _ _)
  apply exists_centered_fullBall_harmonic_replacement a hr hr1 hβ hβ1 hF hH
    (localFrozenCoefficient Ω A B) B hLA hBm hLK hKB hδ hlam hLB hBb hLD hellB
    u hu f G c hf hG
  intro v
  exact (variableJetEnergy_localFrozenCoefficient_eq hΩ A B hAm hBm hKA hKB hAb hBb u v).trans (heq v)


end GaussianTilt.MomentMapLinearDirichlet
