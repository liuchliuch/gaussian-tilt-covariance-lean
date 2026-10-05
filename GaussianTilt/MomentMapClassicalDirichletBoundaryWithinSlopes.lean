import GaussianTilt.MomentMapClassicalDirichletBoundaryWithinJets
import GaussianTilt.MomentMapClassicalDirichletMixedBarrier
import GaussianTilt.MomentMapClassicalDirichletBoundaryBounds

/-! # One-sided boundary slope estimates for intrinsic jets -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma hasDerivWithinAt_inward_line {S : Set X} {u : X → ℝ}
    {x e : X} {D : X →L[ℝ] ℝ} (hu : HasFDerivWithinAt u D S x)
    (hpath : ∀ᶠ t : ℝ in 𝓝[>] 0, x-t • e ∈ S) :
    HasDerivWithinAt (fun t : ℝ => u (x-t • e)) (-D e) (Ioi 0) 0 := by
  let γ := fun t : ℝ => x-t • e
  have hγ : HasDerivAt γ (-e) 0 := by
    simpa [γ] using (hasDerivAt_const (0:ℝ) x).sub ((hasDerivAt_id (0:ℝ)).smul_const e)
  have hγ0 : γ 0 = x := by simp [γ]
  have hnear : Tendsto γ (𝓝[>] 0) (𝓝[S] (γ 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hγ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,hpath⟩
  have hu' : HasFDerivWithinAt u D S (γ 0) := by simpa only [hγ0] using hu
  have hh := (hu'.comp_of_tendsto 0 hγ.hasFDerivAt.hasFDerivWithinAt hnear).hasDerivWithinAt
  simpa [γ] using hh

lemma derivWithin_nonpos_of_nonpos_right {f : ℝ → ℝ} {a : ℝ}
    (hf : HasDerivWithinAt f a (Ioi 0) 0) (hf0 : f 0 = 0)
    (hn : ∀ᶠ t in 𝓝[>] (0:ℝ), f t ≤ 0) : a ≤ 0 := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp hf
  apply le_of_tendsto ht
  filter_upwards [hn,self_mem_nhdsWithin] with t hft htp
  rw [slope_def_field,hf0,sub_zero,sub_zero]
  exact div_nonpos_of_nonpos_of_nonneg hft htp.le

/-- The transverse multiplier is bounded by the actual scaled barriers
using only the within-domain first derivative of the source. -/
theorem within_normal_multiplier_bounds_of_barriers
    {S : Set X} {u w : X → ℝ} {x e : X} {D : X →L[ℝ] ℝ}
    (hu : HasFDerivWithinAt u D S x) (hw : DifferentiableAt ℝ w x)
    (he : fderiv ℝ w x e = 1) (hux : u x = 0) (hwx : w x = 0)
    (hinside : ∀ᶠ y in 𝓝 x, w y < 0 → y ∈ S)
    {a b : ℝ} (hbar : ∀ᶠ y in 𝓝 x, w y < 0 → b*w y ≤ u y ∧ u y ≤ a*w y) :
    a ≤ D e ∧ D e ≤ b := by
  let γ := fun t : ℝ => x-t • e
  have hγ : HasDerivAt γ (-e) 0 := by
    simpa [γ] using (hasDerivAt_const (0:ℝ) x).sub ((hasDerivAt_id (0:ℝ)).smul_const e)
  have hγ0 : γ 0 = x := by simp [γ]
  have hwγ : HasDerivAt (fun t => w (γ t)) (-1) 0 := by
    have hw' : HasFDerivAt w (fderiv ℝ w x) (γ 0) := by simpa only [hγ0] using hw.hasFDerivAt
    simpa only [map_neg,he] using hw'.comp_hasDerivAt 0 hγ
  have hneg := eventually_neg_right_of_deriv_neg hwγ (by norm_num) (by simpa only [hγ0] using hwx)
  have hnear : Tendsto γ (𝓝[>] 0) (𝓝 x) := by
    simpa only [ContinuousAt,hγ0] using hγ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hpath : ∀ᶠ t in 𝓝[>] (0:ℝ), γ t ∈ S := by
    filter_upwards [hneg,hnear.eventually hinside] with t ht hs
    exact hs ht
  have huγ : HasDerivWithinAt (fun t => u (γ t)) (-D e) (Ioi 0) 0 := hasDerivWithinAt_inward_line hu hpath
  have hineq : ∀ᶠ t in 𝓝[>] (0:ℝ), b*w (γ t) ≤ u (γ t) ∧ u (γ t) ≤ a*w (γ t) := by
    filter_upwards [hneg,hnear.eventually hbar] with t ht hb
    exact hb ht
  have h1 := derivWithin_nonpos_of_nonpos_right (huγ.sub (hwγ.hasDerivWithinAt.const_mul a))
    (by change u (γ 0)-a*w (γ 0)=0; simp [hγ0,hux,hwx]) (hineq.mono (fun t ht => sub_nonpos.mpr ht.2))
  have h2 := derivWithin_nonpos_of_nonpos_right ((hwγ.hasDerivWithinAt.const_mul b).sub huγ)
    (by change b*w (γ 0)-u (γ 0)=0; simp [hγ0,hux,hwx]) (hineq.mono (fun t ht => sub_nonpos.mpr ht.1))
  constructor <;> linarith

lemma abs_derivWithin_le_of_right_domination {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasDerivWithinAt f a (Ioi 0) 0) (hg : HasDerivWithinAt g b (Ioi 0) 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfg : ∀ᶠ t in 𝓝[>] (0:ℝ), |f t| ≤ g t) : |a| ≤ b := by
  have hf' := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp hf
  have hg' := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp hg
  have hft : Tendsto (fun t : ℝ => f t/t) (𝓝[>] 0) (𝓝 a) := by
    simpa only [slope_fun_def_field,hf0,sub_zero] using hf'
  have hgt : Tendsto (fun t : ℝ => g t/t) (𝓝[>] 0) (𝓝 b) := by
    simpa only [slope_fun_def_field,hg0,sub_zero] using hg'
  apply le_of_tendsto_of_tendsto hft.abs hgt
  filter_upwards [hfg,self_mem_nhdsWithin] with t ht ht0
  rw [abs_div,abs_of_pos (show (0:ℝ)<t from ht0)]
  exact div_le_div_of_nonneg_right ht ht0.le

/-- The mixed boundary barrier estimates the actual intrinsic derivative
of the tangential field. It does not differentiate a fictitious extension. -/
theorem within_mixed_boundary_slope_bound
    {S P : Set X} {T w q : X → ℝ} {x e : X} {D : X →L[ℝ] ℝ} {K B : ℝ}
    (hT : HasFDerivWithinAt T D S x) (hw : DifferentiableAt ℝ w x) (hq : DifferentiableAt ℝ q x)
    (hT0 : T x = 0) (hw0 : w x = 0) (hq0 : q x = 0) (hDq : fderiv ℝ q x e = 0)
    (hPS : P ⊆ S) (hpath : ∀ᶠ t in 𝓝[>] (0:ℝ), x-t • e ∈ P)
    (hbound : ∀ y ∈ P, |T y| ≤ K*q y-B*w y) : |D e| ≤ B*fderiv ℝ w x e := by
  have hl : HasDerivAt (fun t : ℝ => x-t • e) (-e) 0 := by
    simpa using (hasDerivAt_const (0:ℝ) x).sub ((hasDerivAt_id (0:ℝ)).smul_const e)
  have hTd := hasDerivWithinAt_inward_line hT (hpath.mono (fun t ht => hPS ht))
  have hwd := (show HasFDerivAt w (fderiv ℝ w x) (x-(0:ℝ) • e) by simpa using hw.hasFDerivAt).comp_hasDerivAt (0:ℝ) hl
  have hqd := (show HasFDerivAt q (fderiv ℝ q x) (x-(0:ℝ) • e) by simpa using hq.hasFDerivAt).comp_hasDerivAt (0:ℝ) hl
  have hψd := (hqd.const_mul K).sub (hwd.const_mul B)
  have hb := abs_derivWithin_le_of_right_domination hTd hψd.hasDerivWithinAt
    (by simpa using hT0) (by simp [hq0,hw0]) (hpath.mono (fun t ht => hbound _ ht))
  simpa only [map_neg,hDq,neg_zero,mul_zero,zero_sub,neg_mul,mul_neg,neg_neg,abs_neg] using hb

end GaussianTilt.MomentMapRegularity
