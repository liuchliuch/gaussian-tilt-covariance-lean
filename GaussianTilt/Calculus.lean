import GaussianTilt.Measure

/-!
# Differentiation along the Gaussian-tilt path

These theorems differentiate the actual normalized Lebesgue integral, using
compact support to supply every domination and integrability condition.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GaussianTilt.CompactProbability

variable {n : ℕ} (P : CompactProbability n)

lemma hasDerivAt_weightedIntegral {f : Point n → ℝ}
    (hf : Integrable f P.measure) (t : ℝ) :
    HasDerivAt (P.weightedIntegral f)
      (-P.weightedIntegral (fun x ↦ f x * energy x) t) t := by
  let B : ℝ := Real.exp ((|t| + 1) * P.bound)
  have hB : 0 < B := Real.exp_pos _
  have hderiv (s : ℝ) (x : Point n) :
      HasDerivAt (fun u ↦ P.weight u x * f x)
        (-(P.weight s x * (f x * energy x))) s := by
    convert (((hasDerivAt_id s).neg.mul_const (energy x)).exp.mul_const (f x)) using 1 <;>
      simp only [weight, Pi.neg_apply, id_eq] <;> ring
  have hbound : ∀ᵐ x ∂P.measure, ∀ s ∈ Metric.ball t 1,
      ‖-(P.weight s x * (f x * energy x))‖ ≤ (B * P.bound) * ‖f x‖ := by
    filter_upwards [P.ae_energy_le] with x hx s hs
    have hst : |s - t| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hs
    have habs : |s| ≤ |t| + 1 := by
      calc
        |s| = |(s - t) + t| := by congr 1; ring
        _ ≤ |s - t| + |t| := abs_add_le _ _
        _ ≤ |t| + 1 := by linarith
    have hw : P.weight s x ≤ B := (P.weight_le s hx).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right habs P.bound_nonneg))
    simp only [norm_neg, norm_mul, Real.norm_of_nonneg (P.weight_pos s x).le,
      Real.norm_of_nonneg (energy_nonneg x)]
    calc
      P.weight s x * (‖f x‖ * energy x) ≤ B * (‖f x‖ * P.bound) :=
        mul_le_mul hw (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) (energy_nonneg x)) hB.le
      _ = B * P.bound * ‖f x‖ := by ring
  have hmeas (s : ℝ) : AEStronglyMeasurable
      (fun x ↦ -(P.weight s x * (f x * energy x))) P.measure :=
    ((P.continuous_weight s).aestronglyMeasurable.mul
      (hf.aestronglyMeasurable.mul continuous_energy.aestronglyMeasurable)).neg
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P.measure)
    (F := fun s x ↦ P.weight s x * f x)
    (F' := fun s x ↦ -(P.weight s x * (f x * energy x)))
    (bound := fun x ↦ (B * P.bound) * ‖f x‖)
    (x₀ := t) (ε := 1) (by norm_num)
    (Filter.Eventually.of_forall fun s ↦ (P.integrable_weight_mul hf s).aestronglyMeasurable)
    (P.integrable_weight_mul hf t) (hmeas t) hbound
    (hf.norm.const_mul _) (Filter.Eventually.of_forall fun x s _ ↦ hderiv s x)
  simpa only [weightedIntegral, integral_neg] using H.2

lemma hasDerivAt_partition (t : ℝ) :
    HasDerivAt P.partition (-P.weightedIntegral energy t) t := by
  have h := P.hasDerivAt_weightedIntegral (integrable_const (1 : ℝ)) t
  change HasDerivAt (fun s ↦ ∫ x, P.weight s x * 1 ∂P.measure)
    (- ∫ x, P.weight t x * (1 * energy x) ∂P.measure) t at h
  simpa only [mul_one, one_mul] using h

lemma hasDerivAt_logPartition (t : ℝ) :
    HasDerivAt P.logPartition (-P.expectation t energy) t := by
  convert (P.hasDerivAt_partition t).log (P.partition_ne_zero t) using 1 <;>
    simp [logPartition, expectation, neg_div]

lemma hasDerivAt_expectation {f : Point n → ℝ}
    (hf : Integrable f P.measure) (t : ℝ) :
    HasDerivAt (fun s ↦ P.expectation s f) (-P.covariance t f energy) t := by
  have H := (P.hasDerivAt_weightedIntegral hf t).div
    (P.hasDerivAt_partition t) (P.partition_ne_zero t)
  convert H using 1
  unfold covariance expectation
  field_simp
  <;> ring

lemma deriv_logPartition (t : ℝ) : deriv P.logPartition t = -P.expectation t energy :=
  (P.hasDerivAt_logPartition t).deriv

lemma hasDerivAt_deriv_logPartition (t : ℝ) :
    HasDerivAt (deriv P.logPartition) (P.variance t energy) t := by
  rw [show deriv P.logPartition = (fun s ↦ -P.expectation s energy) from
    funext (P.deriv_logPartition)]
  simpa only [neg_neg, variance] using (P.hasDerivAt_expectation P.integrable_energy t).neg

lemma deriv2_logPartition (t : ℝ) :
    deriv (deriv P.logPartition) t = P.variance t energy :=
  (P.hasDerivAt_deriv_logPartition t).deriv

/-- Rényi divergence defined from the genuine Radon–Nikodym derivative. -/
def renyi (r s t : ℝ) : ℝ :=
  Real.log (∫ x, ((P.tilt s).rnDeriv (P.tilt t) x).toReal ^ r ∂P.tilt t) / (r - 1)

/-- Relative entropy of the endpoint with respect to the base law. -/
def entropy (t : ℝ) : ℝ :=
  ∫ x, Real.log (((P.tilt t).rnDeriv P.measure x).toReal) ∂P.tilt t

lemma renyi_integral (r s t : ℝ) :
    (∫ x, ((P.tilt s).rnDeriv (P.tilt t) x).toReal ^ r ∂P.tilt t) =
      Real.exp (P.logPartition (t + r * (s - t)) - r * P.logPartition s +
        (r - 1) * P.logPartition t) := by
  have hrn : (fun x ↦ ((P.tilt s).rnDeriv (P.tilt t) x).toReal ^ r) =ᵐ[P.tilt t]
      fun x ↦ Real.exp (-(s - t) * energy x - P.logPartition s + P.logPartition t) ^ r :=
    (P.rnDeriv_tilt s t).mono fun x hx ↦ congrArg (fun z : ℝ ↦ z ^ r) hx
  rw [integral_congr_ae hrn, P.integral_tilt]
  unfold expectation weightedIntegral
  have hpoint (x : Point n) :
      P.weight t x * Real.exp (-(s - t) * energy x - P.logPartition s +
        P.logPartition t) ^ r =
      Real.exp (-r * P.logPartition s + r * P.logPartition t) *
        P.weight (t + r * (s - t)) x := by
    rw [← Real.exp_mul]
    unfold weight
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  change Real.exp (-r * P.logPartition s + r * P.logPartition t) *
    P.partition (t + r * (s - t)) / P.partition t = _
  rw [← Real.exp_log (P.partition_pos (t + r * (s - t))),
    ← Real.exp_log (P.partition_pos t), ← Real.exp_add, ← Real.exp_sub]
  congr 1
  unfold logPartition
  ring

lemma integrable_rnDeriv_rpow (r s t : ℝ) :
    Integrable (fun x ↦ ((P.tilt s).rnDeriv (P.tilt t) x).toReal ^ r) (P.tilt t) := by
  by_contra hi
  have h := P.renyi_integral r s t
  rw [integral_undef hi] at h
  exact (Real.exp_pos _).ne' h.symm

lemma tilt_mutually_absolutelyContinuous (s t : ℝ) : P.tilt s ≪ P.tilt t :=
  (P.tilt_absolutelyContinuous s).trans (P.absolutelyContinuous_tilt t)

lemma log_rnDeriv_tilt_base (t : ℝ) :
    (fun x ↦ Real.log (((P.tilt t).rnDeriv P.measure x).toReal)) =ᵐ[P.tilt t]
      fun x ↦ -t * energy x - P.logPartition t := by
  apply (P.tilt_absolutelyContinuous t).ae_le
  filter_upwards [P.rnDeriv_tilt_base t] with x hx
  rw [hx, P.density_eq_exp, Real.log_exp]

lemma integrable_log_rnDeriv (t : ℝ) :
    Integrable (fun x ↦ Real.log (((P.tilt t).rnDeriv P.measure x).toReal)) (P.tilt t) := by
  exact (((P.integrable_tilt P.integrable_energy t).const_mul (-t)).sub
    (integrable_const (P.logPartition t))).congr (P.log_rnDeriv_tilt_base t).symm

/-- The entropy integral is exactly mathlib's extended-valued KL divergence, and finite. -/
lemma klDiv_eq_ofReal_entropy (t : ℝ) :
    InformationTheory.klDiv (P.tilt t) P.measure = ENNReal.ofReal (P.entropy t) := by
  rw [InformationTheory.klDiv_of_ac_of_integrable
    (P.tilt_absolutelyContinuous t) (P.integrable_log_rnDeriv t)]
  simp only [measureReal_univ_eq_one, add_sub_cancel_right]
  rfl

lemma entropy_eq_toReal_klDiv (t : ℝ) :
    P.entropy t = (InformationTheory.klDiv (P.tilt t) P.measure).toReal := by
  exact (InformationTheory.toReal_klDiv_of_measure_eq
    (P.tilt_absolutelyContinuous t) (by simp)).symm

lemma entropy_nonneg_real (t : ℝ) : 0 ≤ P.entropy t := by
  rw [P.entropy_eq_toReal_klDiv]
  exact ENNReal.toReal_nonneg


/-- Equation (9), valid for all real precisions and in particular for every order `r > 1`. -/
lemma renyi_eq (r s t : ℝ) :
    P.renyi r s t =
      (P.logPartition (t + r * (s - t)) - r * P.logPartition s +
        (r - 1) * P.logPartition t) / (r - 1) := by
  rw [renyi, P.renyi_integral, Real.log_exp]

lemma entropy_eq (t : ℝ) :
    P.entropy t = -t * P.expectation t energy - P.logPartition t := by
  have hlog : (fun x ↦ Real.log (((P.tilt t).rnDeriv P.measure x).toReal)) =ᵐ[P.tilt t]
      fun x ↦ -t * energy x - P.logPartition t := by
    apply (P.tilt_absolutelyContinuous t).ae_le
    filter_upwards [P.rnDeriv_tilt_base t] with x hx
    rw [hx, P.density_eq_exp, Real.log_exp]
  rw [entropy, integral_congr_ae hlog,
    integral_sub ((P.integrable_tilt P.integrable_energy t).const_mul _) (integrable_const _),
    integral_const_mul, integral_const, P.integral_tilt]
  simp

lemma entropy_eq_logPartition (t : ℝ) :
    P.entropy t = t * deriv P.logPartition t - P.logPartition t := by
  rw [P.entropy_eq, P.deriv_logPartition]
  ring

lemma hasDerivAt_entropy (t : ℝ) :
    HasDerivAt P.entropy (t * P.variance t energy) t := by
  have h := ((hasDerivAt_id t).mul (P.hasDerivAt_deriv_logPartition t)).sub
    (P.hasDerivAt_logPartition t)
  rw [show P.entropy = (fun s ↦ s * deriv P.logPartition s - P.logPartition s) from
    funext (P.entropy_eq_logPartition)]
  convert h using 1
  rw [P.deriv_logPartition]
  simp only [id_eq]
  ring

lemma deriv_entropy (t : ℝ) : deriv P.entropy t = t * P.variance t energy :=
  (P.hasDerivAt_entropy t).deriv

@[simp] lemma entropy_zero : P.entropy 0 = 0 := by simp [P.entropy_eq]

lemma variance_eq_probabilityVariance {f : Point n → ℝ}
    (hf : MemLp f 2 (P.tilt t)) :
    P.variance t f = ProbabilityTheory.variance f (P.tilt t) := by
  rw [ProbabilityTheory.variance_eq_sub hf]
  simp only [P.integral_tilt, variance, covariance, pow_two]
  rfl

lemma variance_energy_nonneg (t : ℝ) : 0 ≤ P.variance t energy := by
  have hi : Integrable (fun x : Point n ↦ energy x ^ 2) (P.tilt t) := by
    simpa only [pow_two] using
      P.integrable_tilt (P.integrable_energy_mul P.integrable_energy) t
  have hm : MemLp (@energy n) 2 (P.tilt t) :=
    (memLp_two_iff_integrable_sq continuous_energy.aestronglyMeasurable).mpr hi
  rw [P.variance_eq_probabilityVariance hm]
  exact ProbabilityTheory.variance_nonneg _ _

lemma convex_logPartition : ConvexOn ℝ Set.univ P.logPartition := by
  apply convexOn_univ_of_deriv2_nonneg
    (fun t ↦ (P.hasDerivAt_logPartition t).differentiableAt)
    (fun t ↦ (P.hasDerivAt_deriv_logPartition t).differentiableAt)
  intro t
  simpa only [Function.iterate_succ_apply, Function.iterate_zero, id_eq,
    P.deriv2_logPartition] using P.variance_energy_nonneg t

lemma monotoneOn_entropy : MonotoneOn P.entropy (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun t _ ↦ (P.hasDerivAt_entropy t).continuousAt.continuousWithinAt)
    (fun t _ ↦ (P.hasDerivAt_entropy t).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [P.deriv_entropy]
  exact mul_nonneg (Set.mem_Ici.mp (interior_subset ht)) (P.variance_energy_nonneg t)

lemma entropy_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ P.entropy t := by
  simpa only [P.entropy_zero] using P.monotoneOn_entropy (by simp) ht ht

end GaussianTilt.CompactProbability
