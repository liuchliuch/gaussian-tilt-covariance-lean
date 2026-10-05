import GaussianTilt.MomentMapLinearDirichletCenteredLoads
import GaussianTilt.MomentMapLinearDirichletRestrictedLoads

/-! # True centered Hölder divergence-load estimates -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

def centeredMaskL2 (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (hfin : (volume : Measure (CoordinateSpace n)) Ω ≠ ∞)
    (G : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (c : ℝ) : Lp ℝ 2 (volume : Measure (CoordinateSpace n)) :=
  maskL2 Ω hΩ G-constantDomainL2 Ω hΩ hfin c

lemma centeredMaskL2_ae (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (hfin : (volume : Measure (CoordinateSpace n)) Ω ≠ ∞)
    (G : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (c : ℝ) :
    centeredMaskL2 Ω hΩ hfin G c =ᵐ[volume] Ω.indicator (fun x => G x-c) := by
  filter_upwards [Lp.coeFn_sub (maskL2 Ω hΩ G) (constantDomainL2 Ω hΩ hfin c),
    maskL2_ae Ω hΩ G,constantDomainL2_ae Ω hΩ hfin c] with x hx hm hc
  change (maskL2 Ω hΩ G-constantDomainL2 Ω hΩ hfin c) x=_
  rw [hx]
  simp only [Pi.sub_apply]
  rw [hm,hc]
  by_cases hxΩ : x ∈ Ω
  · simp only [indicator_of_mem hxΩ]
  · simp only [indicator_of_notMem hxΩ,sub_self]

lemma norm_centeredMaskL2_sq (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (hfin : (volume : Measure (CoordinateSpace n)) Ω ≠ ∞)
    (G : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (c : ℝ) :
    ‖centeredMaskL2 Ω hΩ hfin G c‖^2 = ∫ x in Ω,(G x-c)^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def,← integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards [centeredMaskL2_ae Ω hΩ hfin G c] with x hx
  rw [hx]
  by_cases hxΩ : x ∈ Ω
  · simp only [indicator_of_mem hxΩ,RCLike.inner_apply,conj_trivial]
    ring
  · simp only [indicator_of_notMem hxΩ,inner_zero_left]

/-- Pointwise (or AE) oscillation controls the true centered L² load norm. -/
theorem norm_centeredMaskL2_le {Ω : Set (CoordinateSpace n)} (hΩ : MeasurableSet Ω)
    (hfin : (volume : Measure (CoordinateSpace n)) Ω ≠ ∞)
    (G : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (c : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂volume, x ∈ Ω → |G x-c| ≤ B) :
    ‖centeredMaskL2 Ω hΩ hfin G c‖ ≤ B*Real.sqrt (volume.real Ω) := by
  haveI : Fact ((volume : Measure (CoordinateSpace n)) Ω < ∞) := ⟨hfin.lt_top⟩
  have hI : IntegrableOn (fun x => (G x-c)^2) Ω :=
    (((Lp.memLp G).restrict Ω).sub (memLp_const c)).integrable_sq
  have hconst : IntegrableOn (fun _ : CoordinateSpace n => B^2) Ω := integrableOn_const hfin
  have hh := integral_mono_ae hI hconst (by
    filter_upwards [ae_restrict_of_ae hbound,ae_restrict_mem hΩ] with x hx hxΩ
    have hp := hx hxΩ
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (G x-c)) hB).mpr hp)
  simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ] at hh
  rw [← norm_centeredMaskL2_sq Ω hΩ hfin G c] at hh
  have hroot := Real.sq_sqrt (show 0 ≤ volume.real Ω from ENNReal.toReal_nonneg)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (Real.sqrt_nonneg _))).mp
  rw [mul_pow,hroot]
  simpa only [mul_comm] using hh

lemma constantDomainL2_zero (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (hfin : (volume : Measure (CoordinateSpace n)) Ω ≠ ∞) : constantDomainL2 Ω hΩ hfin 0=0 := by
  apply Lp.ext
  filter_upwards [constantDomainL2_ae Ω hΩ hfin 0,Lp.coeFn_zero (E := ℝ) (p := 2)
    (μ := (volume : Measure (CoordinateSpace n)))] with x hx hz
  rw [hx,hz]
  simp

/-- The genuine H₀¹ load bound uses local scalar size and centered vector
oscillation. This produces the r^(n+2β) correction energy rate. -/
theorem variableScalarVectorLoad_abs_le_centered {Ω : Set (CoordinateSpace n)}
    (hΩ : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω)
    (hfin : (volume : Measure (CoordinateSpace n)) Ω ≠ ∞)
    (i : Fin n) {r F H β : ℝ} (hr : 0 ≤ r) (hF : 0 ≤ F) (hH : 0 ≤ H)
    (hstrip : ∀ x ∈ Ω, |x i| ≤ r)
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
  have hb := variableScalarVectorLoad_abs_le_gradient i hr hstrip (maskL2 Ω hΩ f)
    (fun k => centeredMaskL2 Ω hΩ hfin (G k) (c k)) v
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (jetGradientNorm_nonneg v.1)
  have hscalar := mul_le_mul_of_nonneg_left hfN (by positivity : 0 ≤ 2*r)
  nlinarith

end GaussianTilt.MomentMapLinearDirichlet
