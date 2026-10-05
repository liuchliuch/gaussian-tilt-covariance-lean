import GaussianTilt.Prekopa

/-!
# Infinitesimal Prékopa: the functional variance calculation

For bounded observables X and A, the second derivative of
`-log E[exp(t X - t² A/2)]` at zero is `E[A] - Var(X)`. Every derivative
under the integral is justified by an explicit integrable envelope. Thus
convexity of this genuine marginal potential yields the functional variance
estimate needed by the Brascamp–Lieb perturbation argument.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace GaussianTilt.FunctionalBrascampLieb

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def perturbWeight (X A : Ω → ℝ) (t : ℝ) (x : Ω) : ℝ :=
  Real.exp (t * X x - t ^ 2 / 2 * A x)
def partition (X A : Ω → ℝ) (t : ℝ) : ℝ := ∫ x, perturbWeight X A t x ∂μ
def partitionSlope (X A : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ x, (X x - t * A x) * perturbWeight X A t x ∂μ

lemma perturb_hasDerivAt (X A : Ω → ℝ) (t : ℝ) (x : Ω) :
    HasDerivAt (fun s ↦ perturbWeight X A s x)
      ((X x - t * A x) * perturbWeight X A t x) t := by
  convert (((hasDerivAt_id t).mul_const (X x)).sub
    ((((hasDerivAt_id t).pow 2).div_const 2).mul_const (A x))).exp using 1 <;>
      simp only [perturbWeight, id_eq, Nat.cast_ofNat, pow_one, Pi.sub_apply, Pi.pow_apply] <;> ring

lemma perturbSlope_hasDerivAt (X A : Ω → ℝ) (t : ℝ) (x : Ω) :
    HasDerivAt (fun s ↦ (X x - s * A x) * perturbWeight X A s x)
      (((X x - t * A x) ^ 2 - A x) * perturbWeight X A t x) t := by
  convert ((hasDerivAt_const t (X x)).sub ((hasDerivAt_id t).mul_const (A x))).mul
    (perturb_hasDerivAt X A t x) using 1 <;> simp only [id_eq, one_mul, zero_sub, Pi.sub_apply, Pi.mul_apply] <;> ring

lemma perturb_bounds {u v s B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hu : |u| ≤ B) (hv : |v| ≤ B) (hs : |s| ≤ R) :
    Real.exp (s * u - s ^ 2 / 2 * v) ≤ Real.exp ((R + R ^ 2) * B) ∧
      |u - s * v| ≤ (1 + R) * B := by
  have hs₂ : s ^ 2 ≤ R ^ 2 := by
    have hh := mul_le_mul hs hs (abs_nonneg s) hR
    nlinarith [sq_abs s]
  have hsu : s * u ≤ R * B := (le_abs_self _).trans
    (by rw [abs_mul]; exact mul_le_mul hs hu (abs_nonneg _) hR)
  have hvs : -v ≤ B := (neg_le_abs v).trans hv
  have hsv := mul_le_mul_of_nonneg_left hvs (sq_nonneg s)
  have hsqB := mul_le_mul_of_nonneg_right hs₂ hB
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sq_nonneg R) hB]
  · calc
      |u - s * v| ≤ |u| + |s * v| := abs_sub _ _
      _ ≤ B + R * B := add_le_add hu (by rw [abs_mul]; exact mul_le_mul hs hv (abs_nonneg _) hR)
      _ = (1 + R) * B := by ring

lemma bound_parameter_ball (t : ℝ) {s : ℝ} (hs : s ∈ Metric.ball t 1) : |s| ≤ |t| + 1 := by
  have hst : |s - t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hs
  calc
    |s| = |(s - t) + t| := by congr 1; ring
    _ ≤ |s - t| + |t| := abs_add_le _ _
    _ ≤ |t| + 1 := by linarith

section Finite
variable [IsFiniteMeasure μ] {X A : Ω → ℝ} {B : ℝ}
    (hX : Measurable X) (hA : Measurable A) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂μ, |X x| ≤ B ∧ |A x| ≤ B)
include hX hA hB hb

lemma perturb_integrable (t : ℝ) : Integrable (perturbWeight X A t) μ := by
  apply (integrable_const (Real.exp ((|t| + |t| ^ 2) * B))).mono' (by apply Measurable.aestronglyMeasurable; unfold perturbWeight; fun_prop)
  filter_upwards [hb] with x hx
  rw [perturbWeight, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (perturb_bounds hB (abs_nonneg t) hx.1 hx.2 le_rfl).1

lemma perturbSlope_integrable (t : ℝ) : Integrable (fun x ↦ (X x - t * A x) * perturbWeight X A t x) μ := by
  apply (integrable_const (((1 + |t|) * B) * Real.exp ((|t| + |t| ^ 2) * B))).mono'
    (by apply Measurable.aestronglyMeasurable; unfold perturbWeight; fun_prop)
  filter_upwards [hb] with x hx
  rw [norm_mul, Real.norm_eq_abs, perturbWeight, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h := perturb_bounds hB (abs_nonneg t) hx.1 hx.2 le_rfl
  exact mul_le_mul h.2 h.1 (Real.exp_pos _).le (by positivity)

lemma partition_hasDerivAt (t : ℝ) :
    HasDerivAt (partition (μ := μ) X A) (partitionSlope (μ := μ) X A t) t := by
  let R := |t| + 1
  let C := ((1 + R) * B) * Real.exp ((R + R ^ 2) * B)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun s x ↦ perturbWeight X A s x)
    (F' := fun s x ↦ (X x - s * A x) * perturbWeight X A s x)
    (bound := fun _ ↦ C) (x₀ := t) (ε := 1) (by norm_num)
    (Filter.Eventually.of_forall (fun s ↦ (perturb_integrable hX hA hB hb s).aestronglyMeasurable))
    (perturb_integrable hX hA hB hb t)
    (perturbSlope_integrable hX hA hB hb t).aestronglyMeasurable ?_
    (integrable_const C) (Filter.Eventually.of_forall (fun x s _ ↦ perturb_hasDerivAt X A s x))
  · exact h.2
  · filter_upwards [hb] with x hx s hs
    have h := perturb_bounds hB (show 0 ≤ R by dsimp [R]; positivity) hx.1 hx.2 (bound_parameter_ball t hs)
    rw [norm_mul, Real.norm_eq_abs, perturbWeight, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul h.2 h.1 (Real.exp_pos _).le (by dsimp [R]; positivity)

lemma partitionSlope_hasDerivAt (t : ℝ) :
    HasDerivAt (partitionSlope (μ := μ) X A)
      (∫ x, ((X x - t * A x) ^ 2 - A x) * perturbWeight X A t x ∂μ) t := by
  let R := |t| + 1
  let D := (1 + R) * B
  let C := (D ^ 2 + B) * Real.exp ((R + R ^ 2) * B)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun s x ↦ (X x - s * A x) * perturbWeight X A s x)
    (F' := fun s x ↦ ((X x - s * A x) ^ 2 - A x) * perturbWeight X A s x)
    (bound := fun _ ↦ C) (x₀ := t) (ε := 1) (by norm_num)
    (Filter.Eventually.of_forall (fun s ↦ (perturbSlope_integrable hX hA hB hb s).aestronglyMeasurable))
    (perturbSlope_integrable hX hA hB hb t) (by apply Measurable.aestronglyMeasurable; unfold perturbWeight; fun_prop) ?_
    (integrable_const C) (Filter.Eventually.of_forall (fun x s _ ↦ perturbSlope_hasDerivAt X A s x))
  · exact h.2
  · filter_upwards [hb] with x hx s hs
    have hD : 0 ≤ D := by dsimp [D, R]; positivity
    have h := perturb_bounds hB (show 0 ≤ R by dsimp [R]; positivity) hx.1 hx.2 (bound_parameter_ball t hs)
    have hsq : (X x - s * A x) ^ 2 ≤ D ^ 2 := by
      have hh := mul_le_mul h.2 h.2 (abs_nonneg _) hD
      nlinarith [sq_abs (X x - s * A x)]
    have hpoly : |(X x - s * A x) ^ 2 - A x| ≤ D ^ 2 + B := by
      calc
        _ ≤ |(X x - s * A x) ^ 2| + |A x| := abs_sub _ _
        _ = (X x - s * A x) ^ 2 + |A x| := by rw [abs_of_nonneg (sq_nonneg _)]
        _ ≤ D ^ 2 + B := add_le_add hsq hx.2
    rw [norm_mul, Real.norm_eq_abs, perturbWeight, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul hpoly h.1 (Real.exp_pos _).le (by positivity)

end Finite

section Probability
variable [IsProbabilityMeasure μ] {X A : Ω → ℝ} {B : ℝ}
    (hX : Measurable X) (hA : Measurable A) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂μ, |X x| ≤ B ∧ |A x| ≤ B)
include hX hA hB hb

lemma partition_pos (t : ℝ) : 0 < partition (μ := μ) X A t :=
  integral_exp_pos (perturb_integrable hX hA hB hb t)

omit hX hA hB hb in
@[simp] lemma partition_zero : partition (μ := μ) X A 0 = 1 := by simp [partition, perturbWeight]
omit hX hA hB hb in
@[simp] lemma partitionSlope_zero : partitionSlope (μ := μ) X A 0 = ∫ x, X x ∂μ := by simp [partitionSlope, perturbWeight]

lemma negLogPartition_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s ↦ -Real.log (partition (μ := μ) X A s))
      (-(partitionSlope (μ := μ) X A t / partition (μ := μ) X A t)) t :=
  ((partition_hasDerivAt hX hA hB hb t).log (partition_pos hX hA hB hb t).ne').neg

/-- The differential core of the functional Brascamp–Lieb argument.
Convexity here is an ordinary local convexity statement for a genuine
integral, not a hypothesized covariance or Poincaré bound. -/
theorem variance_le_of_convex_negLogPartition {δ : ℝ} (hδ : 0 < δ)
    (hc : ConvexOn ℝ (Ioo (-δ) δ) (fun t ↦ -Real.log (partition (μ := μ) X A t))) :
    variance X μ ≤ ∫ x, A x ∂μ := by
  have hXi : Integrable X μ := (integrable_const B).mono' hX.aestronglyMeasurable
    (hb.mono (fun x hx ↦ by simpa only [Real.norm_eq_abs] using hx.1))
  have hAi : Integrable A μ := (integrable_const B).mono' hA.aestronglyMeasurable
    (hb.mono (fun x hx ↦ by simpa only [Real.norm_eq_abs] using hx.2))
  have hX₂ : Integrable (fun x ↦ X x ^ 2) μ := (integrable_const (B ^ 2)).mono'
    (hX.pow_const 2).aestronglyMeasurable (hb.mono (fun x hx ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hh := mul_le_mul hx.1 hx.1 (abs_nonneg _) hB
      nlinarith [sq_abs (X x)]))
  have hLp : MemLp X 2 μ := (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mpr hX₂
  have hder : deriv (fun t ↦ -Real.log (partition (μ := μ) X A t)) =
      (fun t ↦ -(partitionSlope (μ := μ) X A t / partition (μ := μ) X A t)) :=
    funext (fun t ↦ (negLogPartition_hasDerivAt hX hA hB hb t).deriv)
  have hS := partitionSlope_hasDerivAt hX hA hB hb 0
  simp only [perturbWeight, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero,
    Real.exp_zero, mul_one] at hS
  rw [integral_sub hX₂ hAi] at hS
  have hP := partition_hasDerivAt hX hA hB hb 0
  have hsecond := (hS.div hP (partition_pos hX hA hB hb 0).ne').neg
  change HasDerivAt (fun t ↦ -(partitionSlope (μ := μ) X A t / partition (μ := μ) X A t)) _ 0 at hsecond
  have hmono := hc.monotoneOn_deriv (fun t _ ↦ (negLogPartition_hasDerivAt hX hA hB hb t).differentiableAt)
  have hnonneg : 0 ≤ deriv (deriv (fun t ↦ -Real.log (partition (μ := μ) X A t))) 0 := by
    have h := hmono.derivWithin_nonneg (x := (0 : ℝ))
    rwa [derivWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) hδ)] at h
  rw [hder, hsecond.deriv] at hnonneg
  simp only [partition_zero, partitionSlope_zero, mul_one, one_pow, div_one] at hnonneg
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply]
  nlinarith

end Probability
end GaussianTilt.FunctionalBrascampLieb
