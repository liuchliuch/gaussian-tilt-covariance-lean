import GaussianTilt.MomentMapSchauderDifferenceBounds
import GaussianTilt.MomentMapSchauderRescaling

/-! # Actual vector-valued difference quotients and their uniform C¹,α bounds -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
open Set MeasureTheory
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def vectorDifferenceQuotient (f : E → F) (h : E) (s : ℝ) (x : E) : F :=
  s⁻¹ • (f (x+h)-f x)

lemma contDiff_vectorDifferenceQuotient {f : E → F} {k : WithTop ℕ∞}
    (hf : ContDiff ℝ k f) (h : E) (s : ℝ) :
    ContDiff ℝ k (vectorDifferenceQuotient f h s) :=
  contDiff_const.smul ((hf.comp (contDiff_id.add contDiff_const)).sub hf)

lemma fderiv_vectorDifferenceQuotient {f : E → F} (hf : Differentiable ℝ f)
    (h x : E) (s : ℝ) :
    fderiv ℝ (vectorDifferenceQuotient f h s) x =
      vectorDifferenceQuotient (fderiv ℝ f) h s x := by
  have ht : Differentiable ℝ (fun y => f (y+h)) := hf.comp (differentiable_id.add_const h)
  unfold vectorDifferenceQuotient
  change fderiv ℝ (s⁻¹ • (fun y => f (y+h)-f y)) x = _
  rw [fderiv_const_smul (𝕜 := ℝ) (f := fun y => f (y+h)-f y) ((ht x).sub (hf x)),
    fderiv_fun_sub (ht x) (hf x), fderiv_comp_add_right]

lemma secondFrechet_vectorDifferenceQuotient {f : E → F} (hf : ContDiff ℝ 2 f)
    (h x : E) (s : ℝ) :
    fderiv ℝ (fderiv ℝ (vectorDifferenceQuotient f h s)) x =
      vectorDifferenceQuotient (fderiv ℝ (fderiv ℝ f)) h s x := by
  have he : fderiv ℝ (vectorDifferenceQuotient f h s) =
      vectorDifferenceQuotient (fderiv ℝ f) h s := by
    funext y
    exact fderiv_vectorDifferenceQuotient (hf.differentiable (by norm_num)) h y s
  rw [he, fderiv_vectorDifferenceQuotient
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl)]

lemma vectorDifferenceQuotient_eq_integral [CompleteSpace F] {f : E → F}
    (hf : ContDiff ℝ 1 f) (x e : E) {s : ℝ} (hs : s ≠ 0) :
    vectorDifferenceQuotient f (s • e) s x =
      ∫ t in (0 : ℝ)..1, fderiv ℝ f (x+t • (s • e)) e := by
  have hc : Continuous (fun t : ℝ => fderiv ℝ f (x+t • (s • e)) e) :=
    ((hf.fderiv_right (m := 0) (by norm_num)).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hd (t : ℝ) : HasDerivAt (fun r : ℝ => f (x+r • (s • e)))
      (s • fderiv ℝ f (x+t • (s • e)) e) t := by
    simpa only [Function.comp_def, id_eq, one_smul, map_smul] using
      ((hf.differentiable le_rfl (x+t • (s • e))).hasFDerivAt.comp_hasDerivAt t
        (((hasDerivAt_id t).smul_const (s • e)).const_add x))
  have hi := (hc.const_smul s).intervalIntegrable (μ := volume) 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simp only [zero_smul, one_smul, add_zero, intervalIntegral.integral_smul] at he
  unfold vectorDifferenceQuotient
  rw [← he, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- FTC gives a step-independent norm bound for vector-valued quotients. -/
theorem norm_vectorDifferenceQuotient_le [CompleteSpace F] {f : E → F}
    (hf : ContDiff ℝ 1 f) (x e : E) {s M : ℝ} (hs : s ≠ 0)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ f (x+t • (s • e))‖ ≤ M) :
    ‖vectorDifferenceQuotient f (s • e) s x‖ ≤ M*‖e‖ := by
  rw [vectorDifferenceQuotient_eq_integral hf x e hs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := M*‖e‖)
    (f := fun t => fderiv ℝ f (x+t • (s • e)) e) ?_
  · simpa only [sub_zero, abs_one, mul_one] using hb
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self
      (by simpa only [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)
    exact ((fderiv ℝ f (x+t • (s • e))).le_opNorm e).trans
      (mul_le_mul_of_nonneg_right (hM t ht') (norm_nonneg e))

/-- Vector-valued quotient Hölder bounds follow from the actual derivative,
without a reciprocal-step loss. -/
theorem vectorDifferenceQuotient_holder_bound [CompleteSpace F] {f : E → F}
    (hf : ContDiff ℝ 1 f) {S : Set E} {C α : ℝ}
    (hH : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ C*‖x-y‖^α)
    (x y e : E) {s : ℝ} (hs : s ≠ 0)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, x+t • (s • e) ∈ S)
    (hy : ∀ t ∈ Icc (0 : ℝ) 1, y+t • (s • e) ∈ S) :
    ‖vectorDifferenceQuotient f (s • e) s x-vectorDifferenceQuotient f (s • e) s y‖ ≤
      (C*‖e‖)*‖x-y‖^α := by
  have hc (z : E) : Continuous (fun t : ℝ => fderiv ℝ f (z+t • (s • e)) e) :=
    ((hf.fderiv_right (m := 0) (by norm_num)).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  rw [vectorDifferenceQuotient_eq_integral hf x e hs, vectorDifferenceQuotient_eq_integral hf y e hs,
    ← intervalIntegral.integral_sub ((hc x).intervalIntegrable 0 1) ((hc y).intervalIntegrable 0 1)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := (C*‖e‖)*‖x-y‖^α)
    (f := fun t => fderiv ℝ f (x+t • (s • e)) e-fderiv ℝ f (y+t • (s • e)) e) ?_
  · simpa only [sub_zero, abs_one, mul_one] using hb
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self
      (by simpa only [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)
    have hh := hH _ (hx t ht') _ (hy t ht')
    have he : (x+t • (s • e))-(y+t • (s • e))=x-y := by abel
    rw [he] at hh
    have hn := (fderiv ℝ f (x+t • (s • e))-fderiv ℝ f (y+t • (s • e))).le_opNorm e
    exact hn.trans ((mul_le_mul_of_nonneg_right hh (norm_nonneg e)).trans_eq (by ring))

/-- A C²,α source supplies step-uniform C¹,α control of its genuine finite
differences. These are the lower-order data used in cutoff Schauder forcing. -/
theorem differenceQuotient_first_jet_bounds {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {S T : Set E} {M₁ M₂ H₁ H₂ α : ℝ}
    (hb₁ : ∀ x ∈ S, ‖fderiv ℝ f x‖ ≤ M₁)
    (hb₂ : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M₂)
    (hh₁ : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ H₁*‖x-y‖^α)
    (hh₂ : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y‖ ≤ H₂*‖x-y‖^α)
    (e : E) {s : ℝ} (hs : s ≠ 0)
    (hseg : ∀ x ∈ T, ∀ t ∈ Icc (0 : ℝ) 1, x+t • (s • e) ∈ S) :
    (∀ x ∈ T, |vectorDifferenceQuotient f (s • e) s x| ≤ M₁*‖e‖) ∧
    (∀ x ∈ T, ‖fderiv ℝ (vectorDifferenceQuotient f (s • e) s) x‖ ≤ M₂*‖e‖) ∧
    (∀ x ∈ T, ∀ y ∈ T,
      |vectorDifferenceQuotient f (s • e) s x-vectorDifferenceQuotient f (s • e) s y| ≤
        (H₁*‖e‖)*‖x-y‖^α) ∧
    (∀ x ∈ T, ∀ y ∈ T,
      ‖fderiv ℝ (vectorDifferenceQuotient f (s • e) s) x-
        fderiv ℝ (vectorDifferenceQuotient f (s • e) s) y‖ ≤ (H₂*‖e‖)*‖x-y‖^α) := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    simpa only [Real.norm_eq_abs] using norm_vectorDifferenceQuotient_le hf₁ x e hs
      (fun t ht => hb₁ _ (hseg x hx t ht))
  · intro x hx
    rw [fderiv_vectorDifferenceQuotient (hf.differentiable (by norm_num))]
    exact norm_vectorDifferenceQuotient_le hDf x e hs (fun t ht => hb₂ _ (hseg x hx t ht))
  · intro x hx y hy
    simpa only [Real.norm_eq_abs] using vectorDifferenceQuotient_holder_bound hf₁ hh₁ x y e hs
      (hseg x hx) (hseg y hy)
  · intro x hx y hy
    rw [fderiv_vectorDifferenceQuotient (hf.differentiable (by norm_num)),
      fderiv_vectorDifferenceQuotient (hf.differentiable (by norm_num))]
    exact vectorDifferenceQuotient_holder_bound hDf hh₂ x y e hs (hseg x hx) (hseg y hy)

/-- The initial finite Hessian modulus exists for each nonzero step. Its
reciprocal-step constant is subsequently absorbed by the proved Schauder
iteration, rather than retained in the source estimate. -/
theorem differenceQuotient_initial_second_jet_holder {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {S T : Set E} {H α : ℝ}
    (hh : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y‖ ≤ H*‖x-y‖^α)
    (h : E) (s : ℝ) (hT : T ⊆ S) (hshift : ∀ x ∈ T, x+h ∈ S) :
    ∀ x ∈ T, ∀ y ∈ T,
      ‖fderiv ℝ (fderiv ℝ (vectorDifferenceQuotient f h s)) x-
        fderiv ℝ (fderiv ℝ (vectorDifferenceQuotient f h s)) y‖ ≤
      (2*|s⁻¹| * H)*‖x-y‖^α := by
  intro x hx y hy
  rw [secondFrechet_vectorDifferenceQuotient hf, secondFrechet_vectorDifferenceQuotient hf]
  unfold vectorDifferenceQuotient
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  have he : (fderiv ℝ (fderiv ℝ f) (x+h)-fderiv ℝ (fderiv ℝ f) x)-
      (fderiv ℝ (fderiv ℝ f) (y+h)-fderiv ℝ (fderiv ℝ f) y) =
      (fderiv ℝ (fderiv ℝ f) (x+h)-fderiv ℝ (fderiv ℝ f) (y+h))-
      (fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y) := by abel
  rw [he]
  have hb := (norm_sub_le _ _).trans (add_le_add (hh _ (hshift x hx) _ (hshift y hy))
    (hh x (hT hx) y (hT hy)))
  simp only [add_sub_add_right_eq_sub] at hb
  exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (by ring)

end GaussianTilt.MomentMapSchauder
