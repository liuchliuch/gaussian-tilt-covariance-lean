import Mathlib

/-!
# Compactly supported probability measures and genuine Gaussian tilts

The support assumption is an almost-everywhere bound on the squared Euclidean
norm. In finite dimension this is exactly the usual compact-support condition.
No regularity, moment, derivative, or covariance bounds are assumed.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace GaussianTilt

abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)

def energy {n : ℕ} (x : Point n) : ℝ := ‖x‖ ^ 2

structure CompactProbability (n : ℕ) where
  measure : Measure (Point n)
  probability : IsProbabilityMeasure measure
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  ae_energy_le : ∀ᵐ x ∂measure, energy x ≤ bound

attribute [instance] CompactProbability.probability

namespace CompactProbability

variable {n : ℕ} (P : CompactProbability n)

def weight (P : CompactProbability n) (t : ℝ) (x : Point n) : ℝ := Real.exp (-t * energy x)
def partition (t : ℝ) : ℝ := ∫ x, P.weight t x ∂P.measure
def logPartition (t : ℝ) : ℝ := Real.log (P.partition t)
def weightedIntegral (f : Point n → ℝ) (t : ℝ) : ℝ :=
  ∫ x, P.weight t x * f x ∂P.measure
def expectation (t : ℝ) (f : Point n → ℝ) : ℝ :=
  P.weightedIntegral f t / P.partition t
def covariance (t : ℝ) (f g : Point n → ℝ) : ℝ :=
  P.expectation t (fun x ↦ f x * g x) - P.expectation t f * P.expectation t g
def variance (t : ℝ) (f : Point n → ℝ) : ℝ := P.covariance t f f

def density (t : ℝ) (x : Point n) : ℝ := P.weight t x / P.partition t

def tilt (t : ℝ) : Measure (Point n) :=
  P.measure.withDensity (fun x ↦ ENNReal.ofReal (P.density t x))

lemma energy_nonneg (x : Point n) : 0 ≤ energy x := sq_nonneg _
lemma continuous_energy : Continuous (@energy n) := continuous_norm.pow 2
lemma continuous_weight (t : ℝ) : Continuous (P.weight t) := by
  unfold weight energy
  fun_prop
lemma weight_pos (t : ℝ) (x : Point n) : 0 < P.weight t x := Real.exp_pos _

lemma weight_le (t : ℝ) {x : Point n} (hx : energy x ≤ P.bound) :
    P.weight t x ≤ Real.exp (|t| * P.bound) := by
  apply Real.exp_le_exp.mpr
  calc
    -t * energy x ≤ |t| * energy x := mul_le_mul_of_nonneg_right (neg_le_abs t) (energy_nonneg x)
    _ ≤ |t| * P.bound := mul_le_mul_of_nonneg_left hx (abs_nonneg t)

lemma integrable_weight_mul {f : Point n → ℝ} (hf : Integrable f P.measure) (t : ℝ) :
    Integrable (fun x ↦ P.weight t x * f x) P.measure := by
  apply hf.bdd_mul' (P.continuous_weight t).aestronglyMeasurable
  filter_upwards [P.ae_energy_le] with x hx
  simpa only [Real.norm_eq_abs, abs_of_pos (P.weight_pos t x)] using P.weight_le t hx

lemma integrable_weight (t : ℝ) : Integrable (P.weight t) P.measure := by
  simpa using P.integrable_weight_mul (integrable_const (1 : ℝ)) t

lemma partition_pos (t : ℝ) : 0 < P.partition t :=
  integral_exp_pos (P.integrable_weight t)

lemma partition_ne_zero (t : ℝ) : P.partition t ≠ 0 := (P.partition_pos t).ne'

lemma integrable_energy_mul {f : Point n → ℝ} (hf : Integrable f P.measure) :
    Integrable (fun x ↦ energy x * f x) P.measure := by
  apply hf.bdd_mul' continuous_energy.aestronglyMeasurable
  filter_upwards [P.ae_energy_le] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (energy_nonneg x)] using hx

lemma integrable_energy : Integrable (@energy n) P.measure := by
  simpa using P.integrable_energy_mul (integrable_const (1 : ℝ))

lemma density_pos (t : ℝ) (x : Point n) : 0 < P.density t x :=
  div_pos (P.weight_pos t x) (P.partition_pos t)

lemma continuous_density (t : ℝ) : Continuous (P.density t) :=
  (P.continuous_weight t).div_const _

lemma integrable_density (t : ℝ) : Integrable (P.density t) P.measure :=
  (P.integrable_weight t).div_const _

lemma integral_density (t : ℝ) : (∫ x, P.density t x ∂P.measure) = 1 := by
  simp only [density, integral_div]
  exact div_self (P.partition_ne_zero t)

lemma integral_tilt (t : ℝ) (f : Point n → ℝ) :
    (∫ x, f x ∂P.tilt t) = P.expectation t f := by
  rw [tilt, integral_withDensity_eq_integral_toReal_smul
    (P.continuous_density t).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (le_of_lt (P.density_pos t _)), smul_eq_mul]
  simp only [density, expectation, weightedIntegral]
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div]

lemma tilt_probability (t : ℝ) : IsProbabilityMeasure (P.tilt t) := by
  constructor
  rw [tilt, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (P.integrable_density t)
    (Filter.Eventually.of_forall fun x ↦ (P.density_pos t x).le), P.integral_density]
  simp

instance (t : ℝ) : IsProbabilityMeasure (P.tilt t) := P.tilt_probability t

@[simp] lemma partition_zero : P.partition 0 = 1 := by
  simp [partition, weight]

@[simp] lemma logPartition_zero : P.logPartition 0 = 0 := by
  simp [logPartition]

@[simp] lemma expectation_zero (f : Point n → ℝ) :
    P.expectation 0 f = ∫ x, f x ∂P.measure := by
  simp [expectation, weightedIntegral, weight]

@[simp] lemma expectation_one (t : ℝ) : P.expectation t (fun _ ↦ 1) = 1 := by
  unfold expectation weightedIntegral
  simpa only [partition, mul_one] using div_self (P.partition_ne_zero t)

lemma tilt_eq_tilted (t : ℝ) : P.tilt t = P.measure.tilted (fun x ↦ -t * energy x) := rfl

lemma integrable_tilt {f : Point n → ℝ} (hf : Integrable f P.measure) (t : ℝ) :
    Integrable f (P.tilt t) := by
  rw [P.tilt_eq_tilted, integrable_tilted_iff (P.integrable_weight t)]
  exact P.integrable_weight_mul hf t

lemma tilt_absolutelyContinuous (t : ℝ) : P.tilt t ≪ P.measure :=
  withDensity_absolutelyContinuous _ _

lemma absolutelyContinuous_tilt (t : ℝ) : P.measure ≪ P.tilt t := by
  rw [P.tilt_eq_tilted]
  exact absolutelyContinuous_tilted (P.integrable_weight t)

lemma density_eq_exp (t : ℝ) (x : Point n) :
    P.density t x = Real.exp (-t * energy x - P.logPartition t) := by
  rw [Real.exp_sub, logPartition, Real.exp_log (P.partition_pos t)]
  rfl

lemma rnDeriv_tilt_base (t : ℝ) :
    (fun x ↦ ((P.tilt t).rnDeriv P.measure x).toReal) =ᵐ[P.measure] P.density t := by
  have h := toReal_rnDeriv_tilted_left P.measure (ν := P.measure)
    (f := fun x ↦ -t * energy x) (by unfold energy; fun_prop)
  rw [← P.tilt_eq_tilted] at h
  filter_upwards [h, Measure.rnDeriv_self P.measure] with x hx hself
  simpa only [hself, ENNReal.toReal_one, mul_one] using hx

lemma rnDeriv_tilt (s t : ℝ) :
    (fun x ↦ ((P.tilt s).rnDeriv (P.tilt t) x).toReal) =ᵐ[P.tilt t]
      fun x ↦ Real.exp (-(s - t) * energy x - P.logPartition s + P.logPartition t) := by
  have h := toReal_rnDeriv_tilted_right (P.tilt s) P.measure (P.integrable_weight t)
  rw [← P.tilt_eq_tilted] at h
  apply (P.tilt_absolutelyContinuous t).ae_le
  filter_upwards [h, P.rnDeriv_tilt_base s] with x hx hs
  rw [hx, hs, P.density_eq_exp]
  change Real.exp (-(-t * energy x)) * P.partition t *
    Real.exp (-s * energy x - P.logPartition s) = _
  rw [← Real.exp_log (P.partition_pos t)]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold logPartition
  ring

@[simp] lemma tilt_zero : P.tilt 0 = P.measure := by
  simp [tilt, density, weight]

end CompactProbability
end GaussianTilt
