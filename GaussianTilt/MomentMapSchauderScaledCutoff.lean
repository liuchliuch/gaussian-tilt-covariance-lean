import GaussianTilt.MomentMapSchauderRescaling
import GaussianTilt.MomentMapSchauderHolderInterpolation
import GaussianTilt.MomentMapSchauderLocalization

/-!
# Constructed cutoffs with scale-uniform derivative estimates

One fixed genuine smooth bump is translated and dilated. Compactness bounds
its first three actual derivatives; exact chain-rule scaling gives the
radius powers needed in the interior Schauder absorption argument.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 500000
set_option maxSynthPendingDepth 1000
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def scaledInteriorCutoff (a : E) (r : ℝ) : E → ℝ :=
  centeredRescale (default : ContDiffBump (0 : E)) a r⁻¹

lemma scaledInteriorCutoff_contDiff (a : E) (r : ℝ) : ContDiff ℝ ∞ (scaledInteriorCutoff a r) :=
  contDiff_centeredRescale (default : ContDiffBump (0 : E)).contDiff a r⁻¹

lemma scaledInteriorCutoff_nonneg (a x : E) (r : ℝ) : 0 ≤ scaledInteriorCutoff a r x :=
  (default : ContDiffBump (0 : E)).nonneg

lemma scaledInteriorCutoff_le_one (a x : E) (r : ℝ) : scaledInteriorCutoff a r x ≤ 1 :=
  (default : ContDiffBump (0 : E)).le_one

lemma scaledInteriorCutoff_one {a x : E} {r : ℝ} (hr : 0 < r) (hx : ‖x-a‖ ≤ r) :
    scaledInteriorCutoff a r x = 1 := by
  apply (default : ContDiffBump (0 : E)).one_of_mem_closedBall
  change dist (r⁻¹ • (x-a)) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  exact (inv_mul_le_one₀ hr).mpr hx

lemma scaledInteriorCutoff_zero {a x : E} {r : ℝ} (hr : 0 < r) (hx : 2 * r ≤ ‖x-a‖) :
    scaledInteriorCutoff a r x = 0 := by
  apply (default : ContDiffBump (0 : E)).zero_of_le_dist
  change (2 : ℝ) ≤ dist (r⁻¹ • (x-a)) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), ← div_eq_inv_mul]
  exact (le_div_iff₀ hr).mpr hx

lemma tsupport_scaledInteriorCutoff_subset (a : E) {r : ℝ} (hr : 0 < r) :
    tsupport (scaledInteriorCutoff a r) ⊆ Metric.closedBall a (2 * r) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hxball
  have hxnorm : 2 * r < ‖x-a‖ := by simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hxball
  exact hx (scaledInteriorCutoff_zero hr hxnorm.le)

lemma scaledInteriorCutoff_compact (a : E) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (scaledInteriorCutoff a r) :=
  (isCompact_closedBall a (2*r)).of_isClosed_subset (isClosed_tsupport _) (tsupport_scaledInteriorCutoff_subset a hr)

/-- Constants for the first three derivatives of the fixed bump, obtained
from actual compact support and continuity. -/
theorem exists_fixed_bump_derivative_bounds : ∃ B₁ B₂ B₃ : ℝ,
    0 < B₁ ∧ 0 < B₂ ∧ 0 < B₃ ∧
    (∀ x : E, ‖fderiv ℝ (default : ContDiffBump (0 : E)) x‖ ≤ B₁) ∧
    (∀ x : E, ‖fderiv ℝ (fderiv ℝ (default : ContDiffBump (0 : E))) x‖ ≤ B₂) ∧
    (∀ x : E, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (default : ContDiffBump (0 : E)))) x‖ ≤ B₃) := by
  let b : E → ℝ := (default : ContDiffBump (0 : E))
  have hs : HasCompactSupport b := (default : ContDiffBump (0 : E)).hasCompactSupport
  have hb : ContDiff ℝ 3 b := (default : ContDiffBump (0 : E)).contDiff
  have hc₁ := (hb.fderiv_right (m := 2) (by norm_num)).continuous
  have hc₂ := ((hb.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).continuous
  have hc₃ := (((hb.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
    (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  obtain ⟨B₁, hB₁⟩ := (hs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hc₁
  obtain ⟨B₂, hB₂⟩ := ((hs.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).exists_bound_of_continuous hc₂
  obtain ⟨B₃, hB₃⟩ := (((hs.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).exists_bound_of_continuous hc₃
  exact ⟨max B₁ 1, max B₂ 1, max B₃ 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun x => (hB₁ x).trans (le_max_left _ _), fun x => (hB₂ x).trans (le_max_left _ _),
    fun x => (hB₃ x).trans (le_max_left _ _)⟩

/-- The radius powers are proved for the first three true derivatives of
all translated/dilated cutoffs, using constants fixed before center/radius. -/
theorem exists_scaled_cutoff_derivative_bounds : ∃ B₁ B₂ B₃ : ℝ,
    0 < B₁ ∧ 0 < B₂ ∧ 0 < B₃ ∧ ∀ a : E, ∀ r : ℝ, 0 < r → ∀ x : E,
      ‖fderiv ℝ (scaledInteriorCutoff a r) x‖ ≤ B₁ / r ∧
      ‖fderiv ℝ (fderiv ℝ (scaledInteriorCutoff a r)) x‖ ≤ B₂ / r ^ 2 ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (scaledInteriorCutoff a r))) x‖ ≤ B₃ / r ^ 3 := by
  obtain ⟨B₁, B₂, B₃, hB₁, hB₂, hB₃, hb₁, hb₂, hb₃⟩ := exists_fixed_bump_derivative_bounds (E := E)
  refine ⟨B₁, B₂, B₃, hB₁, hB₂, hB₃, ?_⟩
  intro a r hr x
  have hb : ContDiff ℝ 3 (default : ContDiffBump (0 : E)) := (default : ContDiffBump (0 : E)).contDiff
  constructor
  · rw [scaledInteriorCutoff, fderiv_centeredRescale (hb.differentiable (by norm_num)),
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact (mul_le_mul_of_nonneg_left (hb₁ _) (inv_nonneg.mpr hr.le)).trans_eq (by ring)
  constructor
  · rw [scaledInteriorCutoff, secondFrechet_centeredRescale (hb.of_le (by norm_num)),
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (hb₂ _) (sq_nonneg _)).trans_eq (by rw [inv_pow]; ring)
  · rw [scaledInteriorCutoff, thirdFrechet_centeredRescale hb,
      norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (inv_pos.mpr hr) _)]
    exact (mul_le_mul_of_nonneg_left (hb₃ _) (pow_nonneg (inv_nonneg.mpr hr.le) _)).trans_eq (by rw [inv_pow]; ring)

end GaussianTilt.MomentMapSchauder
