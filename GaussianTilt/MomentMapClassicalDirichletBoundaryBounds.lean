import GaussianTilt.MomentMapClassicalDirichletBoundaryJets

/-! # Normal multipliers and tangential Hessian bounds from true barriers -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Gradient
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma fderiv_apply_eq_inner_gradient (w : E n → ℝ) (x v : E n) :
    fderiv ℝ w x v = inner ℝ (gradient w x) v := by
  change _ = (InnerProductSpace.toDual ℝ (E n) ((InnerProductSpace.toDual ℝ (E n)).symm
    (fderiv ℝ w x))) v
  rw [LinearIsometryEquiv.apply_symm_apply]

lemma exists_unit_transverse {w : E n → ℝ} {x : E n} (hg : gradient w x ≠ 0) :
    ∃ e : E n, fderiv ℝ w x e = 1 := by
  refine ⟨(‖gradient w x‖^2)⁻¹ • gradient w x, ?_⟩
  rw [map_smul, fderiv_apply_eq_inner_gradient, real_inner_self_eq_norm_sq, smul_eq_mul,
    inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hg))]

lemma deriv_nonpos_of_nonpos_right {f : ℝ → ℝ} {a : ℝ}
    (hf : HasDerivAt f a 0) (hf0 : f 0 = 0)
    (hn : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ≤ 0) : a ≤ 0 := by
  apply le_of_tendsto hf.tendsto_slope_zero_right
  filter_upwards [hn, self_mem_nhdsWithin] with t ht htp
  simp only [zero_add, hf0, sub_zero, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr htp.le) ht

lemma eventually_neg_right_of_deriv_neg {f : ℝ → ℝ} {a : ℝ}
    (hf : HasDerivAt f a 0) (ha : a < 0) (hf0 : f 0 = 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < 0 := by
  have hh := hf.tendsto_slope_zero_right.eventually (eventually_lt_nhds ha)
  filter_upwards [hh, self_mem_nhdsWithin] with t ht htp
  simp only [zero_add, hf0, sub_zero, smul_eq_mul] at ht
  by_contra hn
  exact (not_lt_of_ge (mul_nonneg (inv_nonneg.mpr htp.le) (not_lt.mp hn))) ht

/-- The multiplier is bounded by actual scaled defining-function barriers,
using only differentiability and one-sided approach from the domain. -/
theorem normal_multiplier_bounds_of_barriers {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {u w : X → ℝ} {x e : X}
    (hu : DifferentiableAt ℝ u x) (hw : DifferentiableAt ℝ w x)
    (he : fderiv ℝ w x e = 1) (hux : u x = 0) (hwx : w x = 0)
    {a b : ℝ}
    (hbar : ∀ᶠ y in 𝓝 x, w y < 0 → b*w y ≤ u y ∧ u y ≤ a*w y) :
    a ≤ fderiv ℝ u x e ∧ fderiv ℝ u x e ≤ b := by
  let l := fun t : ℝ => x+t • (-e)
  have hl : HasDerivAt l (-e) 0 := by
    simpa [l] using (hasDerivAt_const (0 : ℝ) x).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const (-e))
  have hl0 : l 0 = x := by simp [l]
  have hwl : HasDerivAt (fun t => w (l t)) (-1) 0 := by
    have hd : HasFDerivAt w (fderiv ℝ w x) (l 0) := by simpa [hl0] using hw.hasFDerivAt
    simpa only [map_neg, he] using hd.comp_hasDerivAt 0 hl
  have hul : HasDerivAt (fun t => u (l t)) (-fderiv ℝ u x e) 0 := by
    have hd : HasFDerivAt u (fderiv ℝ u x) (l 0) := by simpa [hl0] using hu.hasFDerivAt
    simpa only [map_neg] using hd.comp_hasDerivAt 0 hl
  have hneg := eventually_neg_right_of_deriv_neg hwl (by norm_num)
    (by simpa [hl0] using hwx)
  have hnear : Tendsto l (𝓝[>] 0) (𝓝 x) := by
    exact (show Tendsto l (𝓝 0) (𝓝 x) from by simpa [ContinuousAt,hl0] using hl.continuousAt).mono_left nhdsWithin_le_nhds
  have hineq : ∀ᶠ t in 𝓝[>] (0 : ℝ), b*w (l t) ≤ u (l t) ∧ u (l t) ≤ a*w (l t) := by
    filter_upwards [hneg, hnear.eventually hbar] with t ht hb
    exact hb ht
  have h1 := deriv_nonpos_of_nonpos_right (hul.sub (hwl.const_mul a))
    (by simp [hl0,hux,hwx]) (hineq.mono (fun t ht => sub_nonpos.mpr ht.2))
  have h2 := deriv_nonpos_of_nonpos_right ((hwl.const_mul b).sub hul)
    (by simp [hl0,hux,hwx]) (hineq.mono (fun t ht => sub_nonpos.mpr ht.1))
  constructor <;> linarith

lemma gradient_eq_smul_of_fderiv_eq_smul {u w : E n → ℝ} {x : E n} {lam : ℝ}
    (h : fderiv ℝ u x = lam • fderiv ℝ w x) : gradient u x = lam • gradient w x := by
  simp only [gradient, h, map_smul]

/-- Polarization upgrades the diagonal boundary identity to the full
bilinear tangential Hessian identity. -/
theorem secondFDeriv_tangent_bilinear_eq_of_level_constant {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {u w : X → ℝ} {x e v z : X}
    (hu : ContDiffAt ℝ 2 u x) (hw : ContDiffAt ℝ 2 w x)
    (he : fderiv ℝ w x e = 1) (hv : fderiv ℝ w x v = 0) (hz : fderiv ℝ w x z = 0)
    (hzero : ∀ᶠ y in 𝓝 x, w y = w x → u y = u x) :
    fderiv ℝ (fderiv ℝ u) x v z =
      (fderiv ℝ u x e) * fderiv ℝ (fderiv ℝ w) x v z := by
  have hvz : fderiv ℝ w x (v+z) = 0 := by simp [map_add,hv,hz]
  have h1 := secondFDeriv_tangent_eq_of_level_constant hu hw he hv hzero
  have h2 := secondFDeriv_tangent_eq_of_level_constant hu hw he hz hzero
  have h3 := secondFDeriv_tangent_eq_of_level_constant hu hw he hvz hzero
  have hus := hu.isSymmSndFDerivAt (by norm_num) z v
  have hws := hw.isSymmSndFDerivAt (by norm_num) z v
  simp only [map_add, ContinuousLinearMap.add_apply] at h3
  rw [hus,hws] at h3
  nlinarith

end GaussianTilt.MomentMapRegularity
