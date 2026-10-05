import GaussianTilt.LowerProbability
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Complex.Exponential

/-!
# Exponential-tilt estimates for the cube-square law

This module proves estimates for the actual normalized Lebesgue cube law.
It does not postulate a normal approximation or a local central limit theorem.
The Cramér–Petrov relative-tail theorem and its local-mass consequence are not
claimed here: the quantitative local-mass step remains separate.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal Topology

namespace GaussianTilt.ModerateDeviations
open LowerProbability

/-- The centered energy deficit of one uniform cube coordinate. -/
def coordinateDeficit (x : ℝ) : ℝ := 1 - x ^ 2

lemma coordinateDeficit_measurable : Measurable coordinateDeficit := by
  unfold coordinateDeficit
  fun_prop

lemma coordinateDeficit_range :
    ∀ᵐ x ∂cubeCoordinateLaw, coordinateDeficit x ∈ Set.Icc (-2 : ℝ) 1 := by
  filter_upwards [cubeCoordinate_square_range] with x hx
  simp only [coordinateDeficit, Set.mem_Icc] at *
  constructor <;> linarith

lemma coordinateDeficit_abs_le :
    ∀ᵐ x ∂cubeCoordinateLaw, |coordinateDeficit x| ≤ 2 := by
  filter_upwards [coordinateDeficit_range] with x hx
  exact abs_le.mpr ⟨hx.1, hx.2.trans (by norm_num)⟩

lemma coordinateDeficit_integrable : Integrable coordinateDeficit cubeCoordinateLaw :=
  Integrable.of_mem_Icc (-2) 1 coordinateDeficit_measurable.aemeasurable coordinateDeficit_range

lemma coordinateDeficit_mean : ∫ x, coordinateDeficit x ∂cubeCoordinateLaw = 0 := by
  have hi : Integrable (fun x : ℝ ↦ x ^ 2) cubeCoordinateLaw :=
    Integrable.of_mem_Icc 0 3 (by fun_prop) cubeCoordinate_square_range
  unfold coordinateDeficit
  rw [integral_sub (integrable_const 1) hi,
    cubeCoordinate_square_mean]
  simp

lemma coordinateDeficit_secondMoment :
    ∫ x, coordinateDeficit x ^ 2 ∂cubeCoordinateLaw = (4 / 5 : ℝ) :=
  cubeCoordinate_centered_secondMoment

lemma coordinateDeficit_sq_integrable :
    Integrable (fun x ↦ coordinateDeficit x ^ 2) cubeCoordinateLaw := by
  apply Integrable.of_mem_Icc 0 4 (coordinateDeficit_measurable.pow_const 2).aemeasurable
  filter_upwards [coordinateDeficit_abs_le] with x hx
  refine ⟨sq_nonneg _, ?_⟩
  have h := (sq_le_sq₀ (abs_nonneg (coordinateDeficit x)) (show (0 : ℝ) ≤ 2 by norm_num)).mpr hx
  simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using h

lemma coordinateDeficit_exp_integrable (t : ℝ) :
    Integrable (fun x ↦ Real.exp (t * coordinateDeficit x)) cubeCoordinateLaw :=
  integrable_exp_mul_of_mem_Icc coordinateDeficit_measurable.aemeasurable coordinateDeficit_range

lemma coordinateDeficit_integrableExpSet :
    integrableExpSet coordinateDeficit cubeCoordinateLaw = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  exact coordinateDeficit_exp_integrable t

/-- Exact quantitative third-order remainder for the one-coordinate MGF. -/
theorem coordinateDeficit_mgf_remainder {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |mgf coordinateDeficit cubeCoordinateLaw t - (1 + (2 / 5 : ℝ) * t ^ 2)| ≤
      (16 / 9 : ℝ) * t ^ 3 := by
  let P : ℝ → ℝ := fun x ↦ 1 + t * coordinateDeficit x + (t * coordinateDeficit x) ^ 2 / 2
  have hP : Integrable P cubeCoordinateLaw := by
    convert ((integrable_const 1).add (coordinateDeficit_integrable.const_mul t)).add
      (coordinateDeficit_sq_integrable.const_mul (t ^ 2 / 2)) using 1
    ext x
    simp only [P, Pi.add_apply]
    ring
  have hiP : ∫ x, P x ∂cubeCoordinateLaw = 1 + (2 / 5 : ℝ) * t ^ 2 := by
    have heq : P = fun x ↦ (1 + t * coordinateDeficit x) +
        (t ^ 2 / 2) * coordinateDeficit x ^ 2 := by ext x; dsimp [P]; ring
    have hlin : Integrable (fun x ↦ 1 + t * coordinateDeficit x) cubeCoordinateLaw :=
      (integrable_const 1).add (coordinateDeficit_integrable.const_mul t)
    rw [heq, integral_add hlin
      (coordinateDeficit_sq_integrable.const_mul (t ^ 2 / 2)),
      integral_add (integrable_const 1) (coordinateDeficit_integrable.const_mul t),
      integral_const_mul, integral_const_mul, coordinateDeficit_mean,
      coordinateDeficit_secondMoment]
    simp
    ring
  have hpoint : ∀ᵐ x ∂cubeCoordinateLaw,
      ‖Real.exp (t * coordinateDeficit x) - P x‖ ≤ (16 / 9 : ℝ) * t ^ 3 := by
    filter_upwards [coordinateDeficit_abs_le] with x hx
    have htx : |t * coordinateDeficit x| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_left hx ht.1).trans (by linarith [ht.2])
    have he := Real.exp_bound (n := 3) htx (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at he
    have hp : |t * coordinateDeficit x| ^ 3 ≤ (2 * t) ^ 3 := by
      apply pow_le_pow_left₀ (abs_nonneg _)
      rw [abs_mul, abs_of_nonneg ht.1]
      nlinarith [mul_le_mul_of_nonneg_left hx ht.1]
    rw [Real.norm_eq_abs]
    dsimp [P]
    calc
      _ ≤ |t * coordinateDeficit x| ^ 3 * (2 / 9 : ℝ) := by
        simpa only [abs_mul] using he
      _ ≤ (2 * t) ^ 3 * (2 / 9 : ℝ) := mul_le_mul_of_nonneg_right hp (by norm_num)
      _ = _ := by ring
  have hb := norm_integral_le_of_norm_le_const hpoint
  rw [integral_sub (coordinateDeficit_exp_integrable t) hP, hiP, Real.norm_eq_abs] at hb
  simpa [mgf] using hb

lemma one_le_coordinateDeficit_mgf (t : ℝ) :
    1 ≤ mgf coordinateDeficit cubeCoordinateLaw t := by
  have h := integral_mono (by exact (coordinateDeficit_integrable.const_mul t).add (integrable_const 1))
    (coordinateDeficit_exp_integrable t) (fun x ↦ Real.add_one_le_exp (t * coordinateDeficit x))
  rw [integral_add (coordinateDeficit_integrable.const_mul t) (integrable_const 1),
    integral_const_mul, coordinateDeficit_mean] at h
  simpa [mgf] using h

/-- A cubic cumulant error with the exact variance coefficient `2/5`.
This is a genuine analytic bound, uniform over the stated interval. -/
theorem coordinateDeficit_cgf_remainder {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |cgf coordinateDeficit cubeCoordinateLaw t - (2 / 5 : ℝ) * t ^ 2| ≤ 4 * t ^ 3 := by
  have ht0 := ht.1
  have ht1 := ht.2
  let m := mgf coordinateDeficit cubeCoordinateLaw t
  have hm : 1 ≤ m := one_le_coordinateDeficit_mgf t
  have hpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have he := (abs_le.mp (coordinateDeficit_mgf_remainder ht))
  change -((16 / 9 : ℝ) * t ^ 3) ≤ m - (1 + (2 / 5 : ℝ) * t ^ 2) ∧
    m - (1 + (2 / 5 : ℝ) * t ^ 2) ≤ (16 / 9 : ℝ) * t ^ 3 at he
  have h3 : 0 ≤ t ^ 3 := by positivity
  have ht3 : t ^ 3 ≤ t ^ 2 / 2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1)]
  have hmub : m - 1 ≤ 2 * t ^ 2 := by nlinarith [sq_nonneg t]
  have hlogub : Real.log m ≤ m - 1 := Real.log_le_sub_one_of_pos hpos
  have hloglb : (m - 1) - (m - 1) ^ 2 ≤ Real.log m := by
    have h := Real.one_sub_inv_le_log_of_pos hpos
    have haux : (m - 1) - (m - 1) ^ 2 ≤ 1 - m⁻¹ := by
      calc
        _ ≤ (m - 1) / m := by
          apply (le_div_iff₀ hpos).mpr
          nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg (m - 1))]
        _ = 1 - m⁻¹ := by field_simp
    exact haux.trans h
  have hmsq : (m - 1) ^ 2 ≤ 4 * t ^ 4 := by
    have hh := sq_le_sq₀ (sub_nonneg.mpr hm) (show 0 ≤ 2 * t ^ 2 by positivity)
    have := hh.mpr hmub
    nlinarith
  have ht4 : 4 * t ^ 4 ≤ 2 * t ^ 3 := by
    nlinarith [mul_nonneg h3 (sub_nonneg.mpr ht.2)]
  change |Real.log m - (2 / 5 : ℝ) * t ^ 2| ≤ _
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The one-coordinate exponential family used in the saddlepoint argument. -/
def deficitTilt (t : ℝ) : Measure ℝ :=
  cubeCoordinateLaw.tilted (fun x ↦ t * coordinateDeficit x)

instance deficitTilt_probability (t : ℝ) : IsProbabilityMeasure (deficitTilt t) :=
  isProbabilityMeasure_tilted (coordinateDeficit_exp_integrable t)

/-- Centering an energy does not change its exponentially tilted probability law. -/
lemma deficitTilt_eq_tiltedCoordinateLaw (t : ℝ) :
    deficitTilt t = tiltedCoordinateLaw t := by
  have heq : (fun x : ℝ ↦ t * coordinateDeficit x) =
      (fun x : ℝ ↦ -t * x ^ 2) + (fun _ ↦ t) := by
    funext x
    simp only [coordinateDeficit, Pi.add_apply]
    ring
  rw [deficitTilt, heq, ← tilted_tilted (tiltedCoordinate_exponential_integrable t)]
  haveI := isProbabilityMeasure_tilted (tiltedCoordinate_exponential_integrable t)
  exact tilted_const _ _

lemma coordinateDeficit_cgf_analytic (t : ℝ) :
    AnalyticAt ℝ (cgf coordinateDeficit cubeCoordinateLaw) t := by
  apply analyticAt_cgf
  simp [coordinateDeficit_integrableExpSet]

lemma coordinateDeficit_cgf_deriv_zero :
    deriv (cgf coordinateDeficit cubeCoordinateLaw) 0 = 0 := by
  rw [deriv_cgf_zero (by simp [coordinateDeficit_integrableExpSet]), coordinateDeficit_mean]
  simp

lemma coordinateDeficit_cgf_deriv (t : ℝ) :
    deriv (cgf coordinateDeficit cubeCoordinateLaw) t =
      ∫ x, coordinateDeficit x ∂deficitTilt t := by
  exact (integral_tilted_mul_self (by simp [coordinateDeficit_integrableExpSet])).symm

lemma coordinateDeficit_cgf_second (t : ℝ) :
    iteratedDeriv 2 (cgf coordinateDeficit cubeCoordinateLaw) t =
      variance coordinateDeficit (deficitTilt t) := by
  exact (variance_tilted_mul (by simp [coordinateDeficit_integrableExpSet])).symm

/-- The tilted mean moves by at least a fixed positive multiple of the tilt.
The coefficient comes from the already proved covariance calculation for the
actual uniform coordinate law. -/
theorem coordinateDeficit_cgf_deriv_lower {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    meanDeficitConstant * t ≤ deriv (cgf coordinateDeficit cubeCoordinateLaw) t := by
  rw [coordinateDeficit_cgf_deriv, deficitTilt_eq_tiltedCoordinateLaw]
  have hi : Integrable (fun x : ℝ ↦ x ^ 2) (tiltedCoordinateLaw t) :=
    Integrable.of_mem_Icc 0 3 (by fun_prop) (tiltedCoordinate_square_range t)
  unfold coordinateDeficit
  rw [integral_sub (integrable_const 1) hi]
  have h := tiltedCoordinate_square_mean_le ht
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  linarith

/-- The saddlepoint exists and is quantitatively small. No mean-matching
parameter is assumed: it is obtained by continuity of the actual cumulant. -/
theorem exists_cube_saddlepoint {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) meanDeficitConstant) :
    ∃ t ∈ Set.Icc (0 : ℝ) (δ / meanDeficitConstant),
      deriv (cgf coordinateDeficit cubeCoordinateLaw) t = δ := by
  have hc := meanDeficitConstant_pos
  have hb0 : 0 ≤ δ / meanDeficitConstant := div_nonneg hδ.1 hc.le
  have hb1 : δ / meanDeficitConstant ≤ 1 := (div_le_one hc).mpr hδ.2
  have hcont : Continuous (deriv (cgf coordinateDeficit cubeCoordinateLaw)) :=
    continuous_iff_continuousAt.mpr (fun t ↦ (coordinateDeficit_cgf_analytic t).deriv.continuousAt)
  have hbound := coordinateDeficit_cgf_deriv_lower ⟨hb0, hb1⟩
  have hprod : meanDeficitConstant * (δ / meanDeficitConstant) = δ := by field_simp
  rw [hprod] at hbound
  have hmem : δ ∈ Set.Icc (deriv (cgf coordinateDeficit cubeCoordinateLaw) 0)
      (deriv (cgf coordinateDeficit cubeCoordinateLaw) (δ / meanDeficitConstant)) := by
    rw [coordinateDeficit_cgf_deriv_zero]
    exact ⟨hδ.1, hbound⟩
  exact intermediate_value_Icc hb0 hcont.continuousOn hmem

/-- A uniform variance bound throughout the tilted family. -/
theorem deficitTilt_variance_le (t : ℝ) :
    variance coordinateDeficit (deficitTilt t) ≤ (9 / 4 : ℝ) := by
  have hr : ∀ᵐ x ∂deficitTilt t, coordinateDeficit x ∈ Set.Icc (-2 : ℝ) 1 :=
    tilted_absolutelyContinuous _ _ coordinateDeficit_range
  have h := variance_le_sq_of_bounded hr coordinateDeficit_measurable.aemeasurable
  norm_num at h
  exact h

/-- Total centered energy deficit under the genuine `d`-dimensional cube law. -/
def cubeDeficit (d : ℕ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, coordinateDeficit (x i)

lemma cubeDeficit_measurable (d : ℕ) : Measurable (cubeDeficit d) := by
  unfold cubeDeficit
  exact Finset.measurable_sum _ (fun i _ ↦ coordinateDeficit_measurable.comp (measurable_pi_apply i))

lemma cubeDeficit_independent (d : ℕ) :
    iIndepFun (fun i : Fin d ↦ fun x : Fin d → ℝ ↦ coordinateDeficit (x i)) (cubeLaw d) :=
  iIndepFun_pi (fun _ ↦ coordinateDeficit_measurable.aemeasurable)

lemma cubeDeficit_coordinate_mgf (d : ℕ) (i : Fin d) (t : ℝ) :
    mgf (fun x : Fin d → ℝ ↦ coordinateDeficit (x i)) (cubeLaw d) t =
      mgf coordinateDeficit cubeCoordinateLaw t := by
  have hm := measurePreserving_eval (fun _ : Fin d ↦ cubeCoordinateLaw) i
  have h := integral_map (μ := cubeLaw d) hm.measurable.aemeasurable
    (f := fun x : ℝ ↦ Real.exp (t * coordinateDeficit x))
    ((coordinateDeficit_measurable.const_mul t).exp.aestronglyMeasurable)
  change ∫ y, Real.exp (t * coordinateDeficit y) ∂Measure.map (Function.eval i)
    (Measure.pi (fun _ : Fin d ↦ cubeCoordinateLaw)) = _ at h
  rw [hm.map_eq] at h
  exact h.symm

/-- Exact tensorization of the cumulant generating function, with no iid premise
left for the user to discharge. -/
theorem cubeDeficit_cgf (d : ℕ) (t : ℝ) :
    cgf (cubeDeficit d) (cubeLaw d) t =
      (d : ℝ) * cgf coordinateDeficit cubeCoordinateLaw t := by
  have h := (cubeDeficit_independent d).mgf_sum
    (fun i ↦ coordinateDeficit_measurable.comp (measurable_pi_apply i)) Finset.univ (t := t)
  simp only [cubeDeficit_coordinate_mgf, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at h
  have heq : cubeDeficit d = ∑ i : Fin d, (fun x : Fin d → ℝ ↦ coordinateDeficit (x i)) := by
    funext x
    simp [cubeDeficit]
  rw [heq, cgf, h, Real.log_pow]
  rfl

lemma cubeDeficit_range (d : ℕ) :
    ∀ᵐ x ∂cubeLaw d, cubeDeficit d x ∈ Set.Icc (-2 * (d : ℝ)) d := by
  have ha : ∀ i : Fin d, ∀ᵐ x ∂cubeLaw d,
      coordinateDeficit (x i) ∈ Set.Icc (-2 : ℝ) 1 := by
    intro i
    filter_upwards [cube_square_range d i] with x hx
    simp only [coordinateDeficit, Set.mem_Icc] at *
    constructor <;> linarith
  filter_upwards [ae_all_iff.mpr ha] with x hx
  constructor
  · have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
      (fun i _ ↦ (hx i).1)
    simpa [cubeDeficit, mul_comm] using h
  · have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
      (fun i _ ↦ (hx i).2)
    simpa [cubeDeficit] using h

lemma cubeDeficit_exp_integrable (d : ℕ) (t : ℝ) :
    Integrable (fun x ↦ Real.exp (t * cubeDeficit d x)) (cubeLaw d) :=
  integrable_exp_mul_of_mem_Icc (cubeDeficit_measurable d).aemeasurable (cubeDeficit_range d)

/-- Exponential tilt by the total cube deficit. -/
def tiltedDeficitCube (d : ℕ) (t : ℝ) : Measure (Fin d → ℝ) :=
  (cubeLaw d).tilted (fun x ↦ t * cubeDeficit d x)

instance tiltedDeficitCube_probability (d : ℕ) (t : ℝ) :
    IsProbabilityMeasure (tiltedDeficitCube d t) :=
  isProbabilityMeasure_tilted (cubeDeficit_exp_integrable d t)

lemma cubeDeficit_integrableExpSet (d : ℕ) :
    integrableExpSet (cubeDeficit d) (cubeLaw d) = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  exact cubeDeficit_exp_integrable d t

lemma tiltedDeficitCube_mean (d : ℕ) (t : ℝ) :
    ∫ x, cubeDeficit d x ∂tiltedDeficitCube d t =
      (d : ℝ) * deriv (cgf coordinateDeficit cubeCoordinateLaw) t := by
  have h := integral_tilted_mul_self (X := cubeDeficit d) (μ := cubeLaw d)
    (t := t) (by simp [cubeDeficit_integrableExpSet])
  have heq : cgf (cubeDeficit d) (cubeLaw d) =
      fun u ↦ (d : ℝ) * cgf coordinateDeficit cubeCoordinateLaw u := by
    funext u
    exact cubeDeficit_cgf d u
  rw [heq, deriv_const_mul_field] at h
  exact h

lemma tiltedDeficitCube_variance (d : ℕ) (t : ℝ) :
    variance (cubeDeficit d) (tiltedDeficitCube d t) =
      (d : ℝ) * variance coordinateDeficit (deficitTilt t) := by
  have h := variance_tilted_mul (X := cubeDeficit d) (μ := cubeLaw d)
    (t := t) (by simp [cubeDeficit_integrableExpSet])
  have heq : cgf (cubeDeficit d) (cubeLaw d) =
      fun u ↦ (d : ℝ) * cgf coordinateDeficit cubeCoordinateLaw u := by
    funext u
    exact cubeDeficit_cgf d u
  rw [heq, iteratedDeriv_const_mul (coordinateDeficit_cgf_analytic t).contDiffAt,
    coordinateDeficit_cgf_second] at h
  exact h

lemma tiltedDeficitCube_variance_le (d : ℕ) (t : ℝ) :
    variance (cubeDeficit d) (tiltedDeficitCube d t) ≤ (9 / 4 : ℝ) * d := by
  rw [tiltedDeficitCube_variance]
  have h := mul_le_mul_of_nonneg_left (deficitTilt_variance_le t) (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  nlinarith

/-- An unconditional quantitative mass bound for a central band of the actual
exponentially tilted cube. Its width is on the central-limit scale. -/
theorem tiltedDeficitCube_central_band (d : ℕ) (hd : 0 < d) (t : ℝ) :
    (3 / 4 : ℝ) ≤ (tiltedDeficitCube d t).real
      {x | |cubeDeficit d x - (d : ℝ) * deriv (cgf coordinateDeficit cubeCoordinateLaw) t| <
        3 * Real.sqrt d} := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hw : 0 < 3 * Real.sqrt (d : ℝ) := by positivity
  have hLp : MemLp (cubeDeficit d) 2 (tiltedDeficitCube d t) :=
    memLp_tilted_mul (by simp [cubeDeficit_integrableExpSet]) 2
  have hcheb := meas_ge_le_variance_div_sq hLp hw
  have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hcheb
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at hreal
  change (tiltedDeficitCube d t).real
    {x | 3 * Real.sqrt d ≤ |cubeDeficit d x - ∫ y, cubeDeficit d y ∂tiltedDeficitCube d t|} ≤ _ at hreal
  rw [tiltedDeficitCube_mean] at hreal
  have hvar := tiltedDeficitCube_variance_le d t
  have hsqrt := Real.sq_sqrt hdpos.le
  have htail : (tiltedDeficitCube d t).real
      {x | 3 * Real.sqrt d ≤ |cubeDeficit d x - (d : ℝ) *
        deriv (cgf coordinateDeficit cubeCoordinateLaw) t|} ≤ 1 / 4 := by
    refine hreal.trans ?_
    apply (div_le_iff₀ (sq_pos_of_pos hw)).mpr
    nlinarith
  have hm : MeasurableSet {x | |cubeDeficit d x - (d : ℝ) *
      deriv (cgf coordinateDeficit cubeCoordinateLaw) t| < 3 * Real.sqrt d} := by
    exact measurableSet_lt ((cubeDeficit_measurable d).sub_const _).abs measurable_const
  have heq : {x | |cubeDeficit d x - (d : ℝ) *
      deriv (cgf coordinateDeficit cubeCoordinateLaw) t| < 3 * Real.sqrt d}ᶜ =
      {x | 3 * Real.sqrt d ≤ |cubeDeficit d x - (d : ℝ) *
        deriv (cgf coordinateDeficit cubeCoordinateLaw) t|} := by
    ext x
    simp
  rw [← heq, measureReal_compl hm, measureReal_univ_eq_one] at htail
  linarith

/-- The precise Gaussian exponent, with an explicit cubic cumulant error.
This is sharper than Hoeffding, but intentionally makes no claim about the
Cramér–Petrov polynomial prefactor. -/
theorem cubeDeficit_chernoff {d : ℕ} (hd : 0 < d) {a : ℝ}
    (ha : 0 ≤ a) (hsmall : 5 * a ≤ 2 * (d : ℝ)) :
    (cubeLaw d).real {x | a ≤ cubeDeficit d x} ≤
      Real.exp (-(5 / 8 : ℝ) * a ^ 2 / d + (125 / 16 : ℝ) * a ^ 3 / (d : ℝ) ^ 2) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  let t : ℝ := 5 * a / (4 * d)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 / 2 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 4 * (d : ℝ))).mpr
    nlinarith
  have hb := measure_ge_le_exp_cgf (μ := cubeLaw d) (X := cubeDeficit d)
    a ht0 (cubeDeficit_exp_integrable d t)
  rw [cubeDeficit_cgf] at hb
  have hc := (abs_le.mp (coordinateDeficit_cgf_remainder ⟨ht0, ht1⟩)).2
  calc
    _ ≤ Real.exp (-t * a + (d : ℝ) * cgf coordinateDeficit cubeCoordinateLaw t) := hb
    _ ≤ Real.exp (-t * a + (d : ℝ) * ((2 / 5 : ℝ) * t ^ 2 + 4 * t ^ 3)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hc hdpos.le]
    _ = _ := by
      congr 1
      dsimp [t]
      field_simp
      ring

/-- Concrete sharp-exponent upper estimate for the paper's actual slice event. -/
theorem cubeSlice_chernoff {d : ℕ} (hd : 0 < d) {Δ s : ℝ}
    (hΔ : 0 ≤ Δ) (hs : 0 ≤ s) (hsmall : 5 * Δ * (1 + s) ≤ d) :
    cubeSlice d Δ s ≤ Real.exp
      (-(5 / 2 : ℝ) * (Δ ^ 2 / d) * (1 + s) ^ 2 +
        (125 / 2 : ℝ) * (Δ ^ 3 / (d : ℝ) ^ 2) * (1 + s) ^ 3) := by
  have h := cubeDeficit_chernoff hd (a := 2 * Δ * (1 + s))
    (by positivity) (by nlinarith)
  have hevent : {x : Fin d → ℝ | 2 * Δ * (1 + s) ≤ cubeDeficit d x} =
      {x | (∑ i, ((x i) ^ 2 - 1)) ≤ -2 * Δ * (1 + s)} := by
    ext x
    have heq : cubeDeficit d x = -(∑ i, ((x i) ^ 2 - 1)) := by
      simp only [cubeDeficit, coordinateDeficit, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp only [Set.mem_setOf_eq, heq]
    constructor <;> intro hx <;> linarith
  rw [hevent] at h
  convert h using 1
  congr 1
  ring

section ChangeOfMeasure
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ}

/-- Exponential tilting preserves the mass of a short energy band up to the
explicit likelihood-ratio cost. This is the exact local-mass reduction needed
by a moderate-deviation proof. It does not assume a tail estimate. -/
theorem tilted_band_lower_bound (hX : Measurable X) {t a b : ℝ} (ht : 0 ≤ t)
    (hi : Integrable (fun x ↦ Real.exp (t * X x)) μ) :
    Real.exp (-t * b) * mgf X μ t *
        (μ.tilted (fun x ↦ t * X x)).real {x | a ≤ X x ∧ X x ≤ b} ≤
      μ.real {x | a ≤ X x} := by
  let B : Set Ω := {x | a ≤ X x ∧ X x ≤ b}
  have hB : MeasurableSet B := (measurableSet_le measurable_const hX).inter
    (measurableSet_le hX measurable_const)
  have hM : 0 < mgf X μ t := mgf_pos hi
  have hform : (μ.tilted (fun x ↦ t * X x)).real B =
      ∫ x in B, Real.exp (t * X x) / mgf X μ t ∂μ := by
    simp only [measureReal_def, tilted_apply_eq_ofReal_integral, mgf]
    exact ENNReal.toReal_ofReal (integral_nonneg (fun _ ↦ by positivity))
  have hbound : (μ.tilted (fun x ↦ t * X x)).real B ≤
      μ.real B * (Real.exp (t * b) / mgf X μ t) := by
    rw [hform, ← smul_eq_mul, ← setIntegral_const]
    apply integral_mono_ae (hi.integrableOn.div_const _) (integrable_const _)
    filter_upwards [ae_restrict_mem hB] with x hx
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hx.2 ht)) hM.le
  have hcost : 0 ≤ Real.exp (-t * b) * mgf X μ t := by positivity
  have hm := mul_le_mul_of_nonneg_left hbound hcost
  have heq : Real.exp (-t * b) * mgf X μ t *
      (μ.real B * (Real.exp (t * b) / mgf X μ t)) = μ.real B := by
    have he : Real.exp (-t * b) * Real.exp (t * b) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      _ = (Real.exp (-t * b) * Real.exp (t * b)) * μ.real B := by
        field_simp [hM.ne']
      _ = _ := by rw [he, one_mul]
  rw [heq] at hm
  exact hm.trans (measureReal_mono (fun x hx ↦ hx.1))

end ChangeOfMeasure

/-- A proved two-sided moderate-deviation input for the actual cube law: an
explicit lower tail bound with the exact Gaussian leading exponent and a
central-band likelihood cost. This is a logarithmic-scale bound; it is not
claimed to be the relative-error Cramér–Petrov theorem. -/
theorem cubeDeficit_lower_tail {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 ≤ a)
    (hsmall : a + 3 * Real.sqrt d ≤ meanDeficitConstant * (d : ℝ) / 2) :
    (3 / 4 : ℝ) * Real.exp
      (-(5 / 8 : ℝ) * a ^ 2 / d -
        6 * ((a + 3 * Real.sqrt d) / ((d : ℝ) * meanDeficitConstant)) * Real.sqrt d -
        4 * (d : ℝ) * ((a + 3 * Real.sqrt d) / ((d : ℝ) * meanDeficitConstant)) ^ 3) ≤
      (cubeLaw d).real {x | a ≤ cubeDeficit d x} := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hc := meanDeficitConstant_pos
  let δ : ℝ := (a + 3 * Real.sqrt d) / d
  let T : ℝ := (a + 3 * Real.sqrt d) / ((d : ℝ) * meanDeficitConstant)
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hδsmall : δ ≤ meanDeficitConstant / 2 := by
    apply (div_le_iff₀ hdpos).mpr
    nlinarith
  have hδ : δ ∈ Set.Icc (0 : ℝ) meanDeficitConstant := ⟨hδ0, by linarith⟩
  obtain ⟨t, ht, hmean⟩ := exists_cube_saddlepoint hδ
  have htT : t ≤ T := by
    have he : δ / meanDeficitConstant = T := by dsimp [δ, T]; ring
    simpa only [he] using ht.2
  have hT : 0 ≤ T := ht.1.trans htT
  have htHalf : t ≤ 1 / 2 := by
    apply ht.2.trans
    apply (div_le_iff₀ hc).mpr
    nlinarith
  have hband := tiltedDeficitCube_central_band d hd t
  rw [hmean] at hband
  have hdδ : (d : ℝ) * δ = a + 3 * Real.sqrt d := by
    dsimp [δ]
    field_simp
  rw [hdδ] at hband
  have hband' : (3 / 4 : ℝ) ≤ (tiltedDeficitCube d t).real
      {x | a ≤ cubeDeficit d x ∧ cubeDeficit d x ≤ a + 6 * Real.sqrt d} := by
    apply hband.trans
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    simp only [Set.mem_setOf_eq, abs_lt] at hx ⊢
    constructor <;> linarith
  have hchange := tilted_band_lower_bound (cubeDeficit_measurable d)
    (a := a) (b := a + 6 * Real.sqrt d) ht.1 (cubeDeficit_exp_integrable d t)
  have hcost : Real.exp (-t * (a + 6 * Real.sqrt d)) * mgf (cubeDeficit d) (cubeLaw d) t =
      Real.exp (-t * (a + 6 * Real.sqrt d) +
        (d : ℝ) * cgf coordinateDeficit cubeCoordinateLaw t) := by
    rw [← exp_cgf (cubeDeficit_exp_integrable d t), cubeDeficit_cgf, ← Real.exp_add]
  rw [hcost] at hchange
  have hcgf := (abs_le.mp (coordinateDeficit_cgf_remainder ⟨ht.1, htHalf⟩)).1
  have hquad : -(5 / 8 : ℝ) * a ^ 2 / d ≤ -t * a + (d : ℝ) * ((2 / 5 : ℝ) * t ^ 2) := by
    have hid : -t * a + (d : ℝ) * ((2 / 5 : ℝ) * t ^ 2) +
        (5 / 8 : ℝ) * a ^ 2 / d =
        (2 * (d : ℝ) / 5) * (t - 5 * a / (4 * d)) ^ 2 := by
      field_simp
      ring
    have hp : 0 ≤ (2 * (d : ℝ) / 5) * (t - 5 * a / (4 * d)) ^ 2 := by positivity
    rw [← hid] at hp
    simpa only [neg_mul, neg_div] using (neg_le_iff_add_nonneg.mpr hp)
  have ht3 : t ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ ht.1 htT 3
  have hlinear := mul_le_mul_of_nonneg_right htT (show 0 ≤ 6 * Real.sqrt (d : ℝ) by positivity)
  have hcubic := mul_le_mul_of_nonneg_left ht3 (show 0 ≤ 4 * (d : ℝ) by positivity)
  have hcgfmul := mul_le_mul_of_nonneg_left hcgf hdpos.le
  have hexp : -(5 / 8 : ℝ) * a ^ 2 / d - 6 * T * Real.sqrt d - 4 * (d : ℝ) * T ^ 3 ≤
      -t * (a + 6 * Real.sqrt d) + (d : ℝ) * cgf coordinateDeficit cubeCoordinateLaw t := by
    nlinarith
  calc
    _ ≤ (3 / 4 : ℝ) * Real.exp (-t * (a + 6 * Real.sqrt d) +
        (d : ℝ) * cgf coordinateDeficit cubeCoordinateLaw t) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)
    _ ≤ Real.exp (-t * (a + 6 * Real.sqrt d) +
        (d : ℝ) * cgf coordinateDeficit cubeCoordinateLaw t) *
        (tiltedDeficitCube d t).real {x | a ≤ cubeDeficit d x ∧
          cubeDeficit d x ≤ a + 6 * Real.sqrt d} := by
      nlinarith [mul_le_mul_of_nonneg_left hband'
        (Real.exp_nonneg (-t * (a + 6 * Real.sqrt d) +
          (d : ℝ) * cgf coordinateDeficit cubeCoordinateLaw t))]
    _ ≤ _ := hchange

/-- The preceding genuine lower bound directly in the paper's slice notation. -/
theorem cubeSlice_lower_tail {d : ℕ} (hd : 0 < d) {Δ s : ℝ}
    (hΔ : 0 ≤ Δ) (hs : 0 ≤ s)
    (hsmall : 2 * Δ * (1 + s) + 3 * Real.sqrt d ≤ meanDeficitConstant * (d : ℝ) / 2) :
    (3 / 4 : ℝ) * Real.exp
      (-(5 / 2 : ℝ) * (Δ ^ 2 / d) * (1 + s) ^ 2 -
        6 * ((2 * Δ * (1 + s) + 3 * Real.sqrt d) / ((d : ℝ) * meanDeficitConstant)) * Real.sqrt d -
        4 * (d : ℝ) * ((2 * Δ * (1 + s) + 3 * Real.sqrt d) / ((d : ℝ) * meanDeficitConstant)) ^ 3) ≤
      cubeSlice d Δ s := by
  have h := cubeDeficit_lower_tail hd (a := 2 * Δ * (1 + s)) (by positivity) hsmall
  have hevent : {x : Fin d → ℝ | 2 * Δ * (1 + s) ≤ cubeDeficit d x} =
      {x | (∑ i, ((x i) ^ 2 - 1)) ≤ -2 * Δ * (1 + s)} := by
    ext x
    have heq : cubeDeficit d x = -(∑ i, ((x i) ^ 2 - 1)) := by
      simp only [cubeDeficit, coordinateDeficit, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp only [Set.mem_setOf_eq, heq]
    constructor <;> intro hx <;> linarith
  rw [hevent] at h
  convert h using 1
  congr 2
  ring

/-- The tilted mean has a quadratic error about its exact linear coefficient. -/
theorem coordinateDeficit_cgf_deriv_remainder {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |deriv (cgf coordinateDeficit cubeCoordinateLaw) t - (4 / 5 : ℝ) * t| ≤ 9 * t ^ 2 := by
  have ht0 := ht.1
  have ht1 := ht.2
  let N : ℝ := ∫ x, coordinateDeficit x * Real.exp (t * coordinateDeficit x) ∂cubeCoordinateLaw
  let M : ℝ := mgf coordinateDeficit cubeCoordinateLaw t
  have hNi : Integrable (fun x ↦ coordinateDeficit x * Real.exp (t * coordinateDeficit x)) cubeCoordinateLaw := by
    simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet
      (X := coordinateDeficit) (μ := cubeCoordinateLaw) (v := t)
      (by simp [coordinateDeficit_integrableExpSet]) 1
  have hPi : Integrable (fun x ↦ coordinateDeficit x + t * coordinateDeficit x ^ 2) cubeCoordinateLaw :=
    coordinateDeficit_integrable.add (coordinateDeficit_sq_integrable.const_mul t)
  have hb : ∀ᵐ x ∂cubeCoordinateLaw,
      ‖coordinateDeficit x * Real.exp (t * coordinateDeficit x) -
        (coordinateDeficit x + t * coordinateDeficit x ^ 2)‖ ≤ 8 * t ^ 2 := by
    filter_upwards [coordinateDeficit_abs_le] with x hx
    have htx : |t * coordinateDeficit x| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ht0]
      exact (mul_le_mul_of_nonneg_left hx ht0).trans (by linarith)
    have he := Real.abs_exp_sub_one_sub_id_le htx
    have heq : coordinateDeficit x * Real.exp (t * coordinateDeficit x) -
        (coordinateDeficit x + t * coordinateDeficit x ^ 2) =
        coordinateDeficit x * (Real.exp (t * coordinateDeficit x) - 1 - t * coordinateDeficit x) := by ring
    rw [heq, Real.norm_eq_abs, abs_mul]
    have hpow := pow_le_pow_left₀ (abs_nonneg (coordinateDeficit x)) hx 3
    calc
      _ ≤ |coordinateDeficit x| * (t * coordinateDeficit x) ^ 2 :=
        mul_le_mul_of_nonneg_left he (abs_nonneg _)
      _ = t ^ 2 * |coordinateDeficit x| ^ 3 := by rw [mul_pow, ← sq_abs (coordinateDeficit x)]; ring
      _ ≤ t ^ 2 * 2 ^ 3 := mul_le_mul_of_nonneg_left hpow (sq_nonneg t)
      _ = _ := by ring
  have hN := norm_integral_le_of_norm_le_const hb
  rw [integral_sub hNi hPi, integral_add coordinateDeficit_integrable
    (coordinateDeficit_sq_integrable.const_mul t), integral_const_mul,
    coordinateDeficit_mean, coordinateDeficit_secondMoment] at hN
  have hN' : |N - (4 / 5 : ℝ) * t| ≤ 8 * t ^ 2 := by
    simpa [N, Real.norm_eq_abs, mul_comm] using hN
  have hM : 1 ≤ M := one_le_coordinateDeficit_mgf t
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hmerr := (abs_le.mp (coordinateDeficit_mgf_remainder ht)).2
  have ht3 : t ^ 3 ≤ t ^ 2 / 2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1)]
  have hMub : M - 1 ≤ 2 * t ^ 2 := by
    change M - (1 + (2 / 5 : ℝ) * t ^ 2) ≤ (16 / 9 : ℝ) * t ^ 3 at hmerr
    nlinarith [sq_nonneg t]
  have hMerr : 0 ≤ (4 / 5 : ℝ) * t * (M - 1) ∧
      (4 / 5 : ℝ) * t * (M - 1) ≤ t ^ 2 := by
    constructor
    · exact mul_nonneg (by positivity) (sub_nonneg.mpr hM)
    · nlinarith [mul_le_mul_of_nonneg_left hMub (show 0 ≤ (4 / 5 : ℝ) * t by positivity)]
  have hNum : |N - (4 / 5 : ℝ) * t * M| ≤ 9 * t ^ 2 := by
    have hn := abs_le.mp hN'
    apply abs_le.mpr
    constructor <;> nlinarith [hMerr.1, hMerr.2, sq_nonneg t]
  rw [deriv_cgf (by simp [coordinateDeficit_integrableExpSet])]
  change |N / M - (4 / 5 : ℝ) * t| ≤ _
  calc
    _ = |N - (4 / 5 : ℝ) * t * M| / M := by
      rw [← abs_of_pos hMpos, ← abs_div]
      congr 1
      rw [abs_of_pos hMpos]
      field_simp
    _ ≤ (9 * t ^ 2) / M := div_le_div_of_nonneg_right hNum hMpos.le
    _ ≤ _ := div_le_self (by positivity) hM

/-- The saddlepoint rate has the exact Gaussian coefficient with a uniform
cubic error, proved from the actual MGF and tilted-mean calculations. -/
theorem coordinateDeficit_saddlepoint_rate {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |cgf coordinateDeficit cubeCoordinateLaw t -
      t * deriv (cgf coordinateDeficit cubeCoordinateLaw) t +
      (5 / 8 : ℝ) * deriv (cgf coordinateDeficit cubeCoordinateLaw) t ^ 2| ≤ 30 * t ^ 3 := by
  have hK := abs_le.mp (coordinateDeficit_cgf_remainder ht)
  have hm := coordinateDeficit_cgf_deriv_remainder ht
  have hm2 := (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ 9 * t ^ 2 by positivity)).mpr hm
  rw [sq_abs] at hm2
  have ht4 : t ^ 4 ≤ t ^ 3 / 2 := by
    nlinarith [mul_nonneg (pow_nonneg ht.1 3) (sub_nonneg.mpr ht.2)]
  have hsq := sq_nonneg (deriv (cgf coordinateDeficit cubeCoordinateLaw) t - (4 / 5 : ℝ) * t)
  apply abs_le.mpr
  constructor <;> nlinarith [pow_nonneg ht.1 3]

end GaussianTilt.ModerateDeviations
