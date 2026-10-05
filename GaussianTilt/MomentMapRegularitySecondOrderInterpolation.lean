import GaussianTilt.MomentMapRegularitySecondOrderPerturbation

/-!
# Convex interpolation of a uniform approximation

A uniform approximation by a function with Lipschitz first derivative
controls every actual supporting slope. This is the first-derivative
interpolation estimate used in section perturbation arguments. The convex
function being approximated need not have a classical Hessian.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- A local affine upper approximation and a genuine supporting slope give
a quantitative bound for the difference of the two slopes. -/
theorem supporting_slope_error_of_upper_approximation {u : E n → ℝ}
    {x p q : E n} {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (hps : ∀ y ∈ Metric.closedBall x r, u x + inner ℝ p (y - x) ≤ u y)
    (hup : ∀ y ∈ Metric.closedBall x r,
      u y - u x - inner ℝ q (y - x) ≤ ε) :
    ‖p - q‖ ≤ ε / r := by
  by_cases hpq : p = q
  · simp only [hpq, sub_self, norm_zero]
    exact div_nonneg hε hr.le
  have hnorm : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq)
  let h : E n := (r / ‖p - q‖) • (p - q)
  have hhnorm : ‖h‖ = r := by
    simp only [h, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hnorm)]
    exact div_mul_cancel₀ r hnorm.ne'
  have hy : x + h ∈ Metric.closedBall x r := by
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hhnorm, le_refl]
  have hp := hps (x + h) hy
  have hq := hup (x + h) hy
  simp only [add_sub_cancel_left] at hp hq
  have hi : inner ℝ (p - q) h = r * ‖p - q‖ := by
    rw [show h = (r / ‖p - q‖) • (p - q) from rfl,
      inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hh : r * ‖p - q‖ ≤ ε := by
    rw [← hi, inner_sub_left]
    linarith
  apply (le_div_iff₀ hr).mpr
  nlinarith

/-- Uniform approximation plus a quadratic upper remainder of the smooth
comparison function controls all supporting slopes of the rough function. -/
theorem supporting_slope_error_of_uniform_approximation {u v : E n → ℝ}
    {x p q : E n} {r ε M : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hps : ∀ y ∈ Metric.closedBall x r, u x + inner ℝ p (y - x) ≤ u y)
    (he : ∀ y ∈ Metric.closedBall x r, |u y - v y| ≤ ε)
    (hv : ∀ y ∈ Metric.closedBall x r,
      v y - v x - inner ℝ q (y - x) ≤ M * r ^ 2) :
    ‖p - q‖ ≤ 2 * ε / r + M * r := by
  have hx : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
  have hbound := supporting_slope_error_of_upper_approximation hr
    (show 0 ≤ 2 * ε + M * r ^ 2 by positivity) hps
    (fun y hy => show u y - u x - inner ℝ q (y - x) ≤ 2 * ε + M * r ^ 2 from by
      have hyb := abs_le.mp (he y hy)
      have hxb := abs_le.mp (he x hx)
      have hvr := hv y hy
      linarith)
  convert hbound using 1
  field_simp

/-- Lipschitz first derivatives of the reference potential supply the
quadratic remainder required by the slope interpolation estimate. -/
theorem supporting_slope_error_of_lipschitz_fderiv {u v : E n → ℝ}
    {x p : E n} {r ε : ℝ} {M : ℝ≥0} (hr : 0 < r) (hε : 0 ≤ ε)
    (hps : ∀ y ∈ Metric.closedBall x r, u x + inner ℝ p (y - x) ≤ u y)
    (he : ∀ y ∈ Metric.closedBall x r, |u y - v y| ≤ ε)
    (hvd : ∀ y ∈ Metric.closedBall x r, DifferentiableAt ℝ v y)
    (hvL : LipschitzOnWith M (fderiv ℝ v) (Metric.closedBall x r)) :
    ‖p - gradient v x‖ ≤ 2 * ε / r + M * r := by
  apply supporting_slope_error_of_uniform_approximation hr hε M.coe_nonneg hps he
  intro y hy
  have hx : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
  have hbd : ∀ z ∈ Metric.closedBall x r, ‖fderiv ℝ v z - fderiv ℝ v x‖ ≤ (M : ℝ) * r := by
    intro z hz
    have hh := hvL.dist_le_mul z hz x hx
    rw [dist_eq_norm, dist_eq_norm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz) M.coe_nonneg)
  have ht := (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le' hvd hbd hx hy
  have hgrad : fderiv ℝ v x (y - x) = inner ℝ (gradient v x) (y - x) := by
    change fderiv ℝ v x (y - x) = (InnerProductSpace.toDual ℝ (E n))
      ((InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ v x)) (y - x)
    rw [(InnerProductSpace.toDual ℝ (E n)).apply_symm_apply]
  rw [hgrad, Real.norm_eq_abs] at ht
  apply (le_abs_self _).trans (ht.trans _)
  have hdist : ‖y - x‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
  nlinarith [mul_le_mul_of_nonneg_left hdist (mul_nonneg M.coe_nonneg hr.le)]

/-- A square-root interpolation estimate. Choosing the step size `sqrt ε`
turns a uniform error `ε` into a slope error of order `sqrt ε`. -/
theorem supporting_slope_error_sqrt {u v : E n → ℝ}
    {x p : E n} {ε : ℝ} {M : ℝ≥0} (hε : 0 < ε)
    (hps : ∀ y ∈ Metric.closedBall x (Real.sqrt ε), u x + inner ℝ p (y - x) ≤ u y)
    (he : ∀ y ∈ Metric.closedBall x (Real.sqrt ε), |u y - v y| ≤ ε)
    (hvd : ∀ y ∈ Metric.closedBall x (Real.sqrt ε), DifferentiableAt ℝ v y)
    (hvL : LipschitzOnWith M (fderiv ℝ v) (Metric.closedBall x (Real.sqrt ε))) :
    ‖p - gradient v x‖ ≤ (2 + (M : ℝ)) * Real.sqrt ε := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hb := supporting_slope_error_of_lipschitz_fderiv hs hε.le hps he hvd hvL
  convert hb using 1
  have heq := Real.sq_sqrt hε.le
  field_simp
  nlinarith

end GaussianTilt.MomentMapRegularity
