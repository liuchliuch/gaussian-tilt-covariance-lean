import GaussianTilt.MomentMapLinearDirichletZeroExtension

/-!
# Actual smooth contractions approximating absolute value

These explicit scalar regularizations vanish at zero, are globally
1-Lipschitz and C∞, and converge to absolute value. They will be applied
to genuine interior-supported smooth tests before passing to H₀¹.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet

/-- A smooth zero-preserving approximation to the absolute value. -/
def smoothAbs (ε t : ℝ) : ℝ := Real.sqrt (t ^ 2 + ε ^ 2) - ε

lemma smoothAbs_zero {ε : ℝ} (hε : 0 < ε) : smoothAbs ε 0 = 0 := by
  simp only [smoothAbs, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add,
    Real.sqrt_sq_eq_abs, abs_of_pos hε, sub_self]

lemma smoothAbs_bounds {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 ≤ smoothAbs ε t ∧ smoothAbs ε t ≤ |t| := by
  have hsq := Real.sq_sqrt (show 0 ≤ t ^ 2 + ε ^ 2 by positivity)
  have hroot := Real.sqrt_nonneg (t ^ 2 + ε ^ 2)
  have ht := sq_abs t
  have ha := abs_nonneg t
  have hcross := mul_nonneg ha hε.le
  unfold smoothAbs
  constructor <;> nlinarith

lemma contDiff_smoothAbs {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (smoothAbs ε) := by
  have hp : ContDiff ℝ ∞ (fun t : ℝ => t ^ 2 + ε ^ 2) := (contDiff_id.pow 2).add contDiff_const
  exact (hp.sqrt (fun t => (show 0 < t ^ 2 + ε ^ 2 by positivity).ne')).sub contDiff_const

lemma hasDerivAt_smoothAbs {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (smoothAbs ε) (t / Real.sqrt (t ^ 2 + ε ^ 2)) t := by
  have hp : 0 < t ^ 2 + ε ^ 2 := by positivity
  have hroot : Real.sqrt (t ^ 2 + ε ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hh := ((((hasDerivAt_id t).pow 2).add_const (ε ^ 2)).sqrt hp.ne').sub_const ε
  convert hh using 1
  norm_num
  field_simp

lemma norm_deriv_smoothAbs_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) : ‖deriv (smoothAbs ε) t‖ ≤ 1 := by
  have hp : 0 < t ^ 2 + ε ^ 2 := by positivity
  have hroot : 0 < Real.sqrt (t ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr hp
  rw [(hasDerivAt_smoothAbs hε t).deriv, Real.norm_eq_abs, abs_div, abs_of_pos hroot]
  apply (div_le_one hroot).mpr
  have hsq := Real.sq_sqrt hp.le
  nlinarith [sq_abs t, abs_nonneg t]

lemma lipschitzWith_smoothAbs {ε : ℝ} (hε : 0 < ε) : LipschitzWith 1 (smoothAbs ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hasDerivAt_smoothAbs hε t).differentiableAt)
  intro t
  exact_mod_cast norm_deriv_smoothAbs_le hε t

/-- A concrete positive regularization scale decreasing to zero. -/
def absRegularizationScale (k : ℕ) : ℝ := ((k : ℝ) + 1)⁻¹

lemma absRegularizationScale_pos (k : ℕ) : 0 < absRegularizationScale k := by
  unfold absRegularizationScale
  positivity

lemma absRegularizationScale_tendsto : Tendsto absRegularizationScale atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

lemma smoothAbs_tendsto_abs (t : ℝ) :
    Tendsto (fun k : ℕ => smoothAbs (absRegularizationScale k) t) atTop (𝓝 |t|) := by
  have hsq : Tendsto (fun k => t ^ 2 + absRegularizationScale k ^ 2) atTop (𝓝 (t ^ 2)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      (tendsto_const_nhds.add (absRegularizationScale_tendsto.pow 2))
  have hh := (Real.continuous_sqrt.tendsto _ |>.comp hsq).sub absRegularizationScale_tendsto
  simpa only [smoothAbs, sub_zero, Real.sqrt_sq_eq_abs] using hh

end GaussianTilt.MomentMapLinearDirichlet
