import GaussianTilt.MomentMapLinearDirichletCenteredLoadBounds
import GaussianTilt.MomentMapLinearDirichletTangentialDifferenceTranslation

/-! # True radius-sharp Poincaré and centered loads on translated strips -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1500000

theorem dirichlet_poincare_translated_strip {Ω:Set (CoordinateSpace n)}
    (i:Fin n) (a:CoordinateSpace n) {r:ℝ} (hr:0≤r)
    (hΩ:∀ x ∈ Ω,|x i-a i|≤r) (u:dirichletSobolev Ω) :
    ‖dirichletValue Ω u‖ ≤ 2*r*‖u.1 i.succ‖ := by
  let U := (fun x:CoordinateSpace n=>x+a) ⁻¹' Ω
  let v:dirichletSobolev U := ⟨volumeTranslateJet a u.1,volumeTranslateJet_mem_dirichlet a u⟩
  have hstrip:∀ x ∈ U,|x i|≤r := by
    intro x hx
    have hh := hΩ (x+a) hx
    simpa only [Pi.add_apply,add_sub_cancel_right] using hh
  have hp := dirichlet_poincare_strip i hr hstrip v
  change ‖volumeTranslate a (u.1 0)‖ ≤ 2*r*‖volumeTranslate a (u.1 i.succ)‖ at hp
  simpa only [norm_volumeTranslate] using hp

theorem variableScalarVectorLoad_abs_le_translated_strip {Ω:Set (CoordinateSpace n)}
    (i:Fin n) (a:CoordinateSpace n) {r:ℝ} (hr:0≤r)
    (hΩ:∀ x ∈ Ω,|x i-a i|≤r)
    (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (G:Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n))) (v:dirichletSobolev Ω) :
    |variableScalarVectorLoad Ω f G v| ≤ (2*r*‖f‖+∑ k,‖G k‖)*jetGradientNorm v.1 := by
  have hv : ‖dirichletValue Ω v‖ ≤ 2*r*jetGradientNorm v.1 :=
    (dirichlet_poincare_translated_strip i a hr hΩ v).trans
      (mul_le_mul_of_nonneg_left (norm_jetDerivative_le_gradient v.1 i) (by positivity))
  have hscalar : |inner ℝ f (dirichletValue Ω v)| ≤ (2*r*‖f‖)*jetGradientNorm v.1 := by
    have hh := (abs_real_inner_le_norm f (dirichletValue Ω v)).trans
      (mul_le_mul_of_nonneg_left hv (norm_nonneg f))
    nlinarith
  have hvector : |∑ k,inner ℝ (G k) (v.1 k.succ)| ≤ (∑ k,‖G k‖)*jetGradientNorm v.1 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun k _=>(abs_real_inner_le_norm (G k) _).trans
      (mul_le_mul_of_nonneg_left (norm_jetDerivative_le_gradient v.1 k) (norm_nonneg _)))
  rw [variableScalarVectorLoad_apply]
  exact (abs_add_le _ _).trans ((add_le_add hscalar hvector).trans_eq (by ring))

theorem variableScalarVectorLoad_abs_le_translated_local {Ω:Set (CoordinateSpace n)}
    (i:Fin n) (a:CoordinateSpace n) {r:ℝ} (hr:0≤r)
    (hstrip:∀ x ∈ Ω,|x i-a i|≤r) (hΩ:MeasurableSet Ω)
    (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (G:Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n))) (v:dirichletSobolev Ω) :
    |variableScalarVectorLoad Ω f G v| ≤
      (2*r*‖maskL2 Ω hΩ f‖+∑ k,‖maskL2 Ω hΩ (G k)‖)*jetGradientNorm v.1 := by
  rw [variableScalarVectorLoad_mask Ω hΩ f G]
  exact variableScalarVectorLoad_abs_le_translated_strip i a hr hstrip _ _ v

theorem variableScalarVectorLoad_abs_le_translated_centered {Ω : Set (CoordinateSpace n)}
    (hΩ : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω)
    (hfin : (volume : Measure (CoordinateSpace n)) Ω ≠ ⊤)
    (i : Fin n) (a : CoordinateSpace n) {r F H β : ℝ} (hr : 0 ≤ r) (hF : 0 ≤ F) (hH : 0 ≤ H)
    (hstrip : ∀ x ∈ Ω, |x i-a i| ≤ r)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (c : Fin n → ℝ)
    (hf : ∀ᵐ x ∂volume, x ∈ Ω → |f x| ≤ F)
    (hG : ∀ k, ∀ᵐ x ∂volume, x ∈ Ω → |G k x-c k| ≤ H*r^β)
    (v : dirichletSobolev Ω) :
    |variableScalarVectorLoad Ω f G v| ≤
      ((2*r*F+(n:ℝ)*H*r^β)*Real.sqrt (volume.real Ω))*jetGradientNorm v.1 := by
  have hfN : ‖maskL2 Ω hΩ f‖ ≤ F*Real.sqrt (volume.real Ω) := by
    have hh := norm_centeredMaskL2_le hΩ hfin f 0 hF (by simpa only [sub_zero] using hf)
    simpa only [centeredMaskL2,constantDomainL2_zero,sub_zero] using hh
  have hGN (k : Fin n) : ‖centeredMaskL2 Ω hΩ hfin (G k) (c k)‖ ≤
      (H*r^β)*Real.sqrt (volume.real Ω) :=
    norm_centeredMaskL2_le hΩ hfin (G k) (c k) (mul_nonneg hH (Real.rpow_nonneg hr _)) (hG k)
  have hs : (∑ k, ‖centeredMaskL2 Ω hΩ hfin (G k) (c k)‖) ≤
      (n:ℝ)*(H*r^β)*Real.sqrt (volume.real Ω) := by
    have hh := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hGN k)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hh
  rw [variableScalarVectorLoad_mask Ω hΩ f G,
    ← variableScalarVectorLoad_sub_const hΩ hΩb hfin (maskL2 Ω hΩ f) (fun k => maskL2 Ω hΩ (G k)) c]
  have hb := variableScalarVectorLoad_abs_le_translated_strip i a hr hstrip (maskL2 Ω hΩ f)
    (fun k => centeredMaskL2 Ω hΩ hfin (G k) (c k)) v
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (jetGradientNorm_nonneg v.1)
  have hscalar := mul_le_mul_of_nonneg_left hfN (by positivity : 0 ≤ 2*r)
  nlinarith


end GaussianTilt.MomentMapLinearDirichlet
