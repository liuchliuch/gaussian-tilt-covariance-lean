import GaussianTilt.MomentMapLinearDirichletHarmonicLocal
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Actual smooth one-sided boundary cutoffs

The fixed smooth transition vanishes below height one and equals one
above height two. Its first and second derivatives have genuinely compact
support and finite bounds, so rescaling gives the precise boundary-layer
estimates needed for reflection of the weak equation.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet

def flatBoundaryStep (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

lemma flatBoundaryStep_contDiff : ContDiff ℝ ∞ flatBoundaryStep :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma flatBoundaryStep_nonneg (t : ℝ) : 0 ≤ flatBoundaryStep t := Real.smoothTransition.nonneg _
lemma flatBoundaryStep_le_one (t : ℝ) : flatBoundaryStep t ≤ 1 := Real.smoothTransition.le_one _
lemma flatBoundaryStep_zero {t : ℝ} (ht : t ≤ 1) : flatBoundaryStep t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
lemma flatBoundaryStep_one {t : ℝ} (ht : 2 ≤ t) : flatBoundaryStep t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma flatBoundaryStep_eventually_zero {t : ℝ} (ht : t < 1) :
    flatBoundaryStep =ᶠ[𝓝 t] (fun _ => 0) := by
  filter_upwards [gt_mem_nhds ht] with s hs
  exact flatBoundaryStep_zero hs.le

lemma flatBoundaryStep_eventually_one {t : ℝ} (ht : 2 < t) :
    flatBoundaryStep =ᶠ[𝓝 t] (fun _ => 1) := by
  filter_upwards [lt_mem_nhds ht] with s hs
  exact flatBoundaryStep_one hs.le

lemma flatBoundaryStep_deriv_support : Function.support (deriv flatBoundaryStep) ⊆ Icc (1 : ℝ) 2 := by
  intro t ht
  by_contra hh
  have hcases : t < 1 ∨ 2 < t := by simpa only [mem_Icc, not_and_or, not_le] using hh
  rcases hcases with h | h
  · exact ht (by rw [(flatBoundaryStep_eventually_zero h).deriv_eq]; simp)
  · exact ht (by rw [(flatBoundaryStep_eventually_one h).deriv_eq]; simp)

lemma flatBoundaryStep_deriv_compact : HasCompactSupport (deriv flatBoundaryStep) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc flatBoundaryStep_deriv_support

lemma flatBoundaryStep_second_deriv_support :
    Function.support (deriv (deriv flatBoundaryStep)) ⊆ Icc (1 : ℝ) 2 := by
  intro t ht
  have hts : tsupport (deriv flatBoundaryStep) ⊆ Icc (1 : ℝ) 2 :=
    closure_minimal flatBoundaryStep_deriv_support isClosed_Icc
  exact hts (support_deriv_subset ht)

lemma exists_flatBoundaryStep_derivative_bounds : ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧
    (∀ t, |deriv flatBoundaryStep t| ≤ M₁) ∧
    (∀ t, |deriv (deriv flatBoundaryStep) t| ≤ M₂) := by
  have hd : ContDiff ℝ ∞ (deriv flatBoundaryStep) := (flatBoundaryStep_contDiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdd : ContDiff ℝ ∞ (deriv (deriv flatBoundaryStep)) := (hd.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  obtain ⟨M₁, hM₁⟩ := flatBoundaryStep_deriv_compact.exists_bound_of_continuous hd.continuous
  obtain ⟨M₂, hM₂⟩ := flatBoundaryStep_deriv_compact.deriv.exists_bound_of_continuous hdd.continuous
  exact ⟨max M₁ 0, max M₂ 0, le_max_right _ _, le_max_right _ _,
    fun t => (hM₁ t).trans (le_max_left _ _), fun t => (hM₂ t).trans (le_max_left _ _)⟩

def scaledFlatBoundaryStep (ε t : ℝ) : ℝ := flatBoundaryStep (t / ε)

lemma scaledFlatBoundaryStep_contDiff (ε : ℝ) : ContDiff ℝ ∞ (scaledFlatBoundaryStep ε) :=
  flatBoundaryStep_contDiff.comp (contDiff_id.div_const ε)

lemma scaledFlatBoundaryStep_deriv (ε t : ℝ) :
    deriv (scaledFlatBoundaryStep ε) t = ε⁻¹ * deriv flatBoundaryStep (t / ε) := by
  have h := ((flatBoundaryStep_contDiff.differentiable (by simp) (t/ε)).hasDerivAt).comp t
    ((hasDerivAt_id t).div_const ε)
  convert h.deriv using 1 <;> simp [scaledFlatBoundaryStep, div_eq_mul_inv, mul_comm]

lemma scaledFlatBoundaryStep_second_deriv (ε t : ℝ) :
    deriv (deriv (scaledFlatBoundaryStep ε)) t = ε⁻¹ ^ 2 * deriv (deriv flatBoundaryStep) (t / ε) := by
  have hd : ContDiff ℝ ∞ (deriv flatBoundaryStep) := (flatBoundaryStep_contDiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have he : deriv (scaledFlatBoundaryStep ε) = fun s => ε⁻¹ * deriv flatBoundaryStep (s/ε) :=
    funext (scaledFlatBoundaryStep_deriv ε)
  rw [he]
  have h := (((hd.differentiable (by simp) (t/ε)).hasDerivAt).comp t
    ((hasDerivAt_id t).div_const ε)).const_mul ε⁻¹
  convert h.deriv using 1 <;> simp only [one_div] <;> ring

lemma scaledFlatBoundaryStep_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ ε) :
    scaledFlatBoundaryStep ε t = 0 := flatBoundaryStep_zero ((div_le_one hε).mpr ht)

lemma scaledFlatBoundaryStep_one {ε t : ℝ} (hε : 0 < ε) (ht : 2 * ε ≤ t) :
    scaledFlatBoundaryStep ε t = 1 := flatBoundaryStep_one ((le_div_iff₀ hε).mpr ht)

lemma scaledFlatBoundaryStep_weighted_deriv_bound {ε t M : ℝ}
    (hε : 0 < ε) (ht : 0 ≤ t) (hM : 0 ≤ M) (hb : ∀ s, |deriv flatBoundaryStep s| ≤ M) :
    t * |deriv (scaledFlatBoundaryStep ε) t| ≤ 2 * M := by
  rw [scaledFlatBoundaryStep_deriv, abs_mul, abs_of_pos (inv_pos.mpr hε)]
  by_cases hz : deriv flatBoundaryStep (t/ε) = 0
  · simp only [hz, abs_zero, mul_zero]
    positivity
  · have hs := flatBoundaryStep_deriv_support hz
    have hr : 0 ≤ t/ε := div_nonneg ht hε.le
    calc
      _ = (t/ε) * |deriv flatBoundaryStep (t/ε)| := by ring
      _ ≤ 2 * M := mul_le_mul hs.2 (hb _) (abs_nonneg _) (by norm_num)

lemma scaledFlatBoundaryStep_weighted_second_deriv_bound {ε t M : ℝ}
    (hε : 0 < ε) (ht : 0 ≤ t) (hM : 0 ≤ M) (hb : ∀ s, |deriv (deriv flatBoundaryStep) s| ≤ M) :
    t ^ 2 * |deriv (deriv (scaledFlatBoundaryStep ε)) t| ≤ 4 * M := by
  rw [scaledFlatBoundaryStep_second_deriv, abs_mul, abs_of_nonneg (sq_nonneg _)]
  by_cases hz : deriv (deriv flatBoundaryStep) (t/ε) = 0
  · simp only [hz, abs_zero, mul_zero]
    positivity
  · have hs := flatBoundaryStep_second_deriv_support hz
    have hr : 0 ≤ t/ε := div_nonneg ht hε.le
    have hsquare : (t/ε)^2 ≤ 4 := by nlinarith [hs.2]
    calc
      _ = (t/ε)^2 * |deriv (deriv flatBoundaryStep) (t/ε)| := by ring
      _ ≤ 4 * M := mul_le_mul hsquare (hb _) (abs_nonneg _) (by norm_num)

end GaussianTilt.MomentMapLinearDirichlet
