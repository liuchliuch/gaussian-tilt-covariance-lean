import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Probability estimates for the lower-bound construction

The variables here are real random variables on an actual probability space.
The bounded-variable estimates are consequences of mathlib's proved Hoeffding
lemma.  No moderate-deviation estimate is assumed in this file.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal

namespace GaussianTilt
namespace LowerProbability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Hoeffding's lower-tail inequality at the exact constants used for the cube squares. -/
theorem bounded_lower_tail {d : ℕ} [IsProbabilityMeasure μ]
    (W : Fin d → Ω → ℝ) (h_indep : iIndepFun W μ)
    (h_meas : ∀ i, AEMeasurable (W i) μ)
    (h_range : ∀ i, ∀ᵐ ω ∂μ, W i ω ∈ Set.Icc 0 3)
    (h_mean : ∀ i, ∫ ω, W i ω ∂μ = 1)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | (∑ i, (W i ω - 1)) ≤ -u} ≤
      Real.exp (-2 * u ^ 2 / (9 * (d : ℝ))) := by
  let X : Fin d → Ω → ℝ := fun i ω ↦ 1 - W i ω
  have hi : iIndepFun X μ :=
    h_indep.comp (fun _ x ↦ 1 - x) (fun _ ↦ measurable_const.sub measurable_id)
  have hg (i : Fin d) : HasSubgaussianMGF (X i) (9 / 4) μ := by
    have h := (hasSubgaussianMGF_of_mem_Icc (h_meas i) (h_range i)).neg
    simp only [h_mean i] at h
    convert h using 1
    · ext ω
      simp [X]
    · norm_num [Real.nnnorm_of_nonneg]
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hi
    (s := Finset.univ) (c := fun _ ↦ (9 / 4 : ℝ≥0)) (fun i _ ↦ hg i) hu
  have hevent : {ω | u ≤ ∑ i ∈ Finset.univ, X i ω} =
      {ω | (∑ i, (W i ω - 1)) ≤ -u} := by
    ext ω
    simp only [Set.mem_setOf_eq, X]
    have heq : (∑ i, (1 - W i ω)) = -(∑ i, (W i ω - 1)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    constructor <;> intro hh <;> linarith
  rw [hevent] at h
  convert h using 1
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_ofNat]
  ring

/-- The slice function is the actual probability of the centered quadratic-energy event. -/
def sliceProbability {d : ℕ} (μ : Measure Ω) (W : Fin d → Ω → ℝ)
    (Δ s : ℝ) : ℝ :=
  μ.real {ω | (∑ i, (W i ω - 1)) ≤ -2 * Δ * (1 + s)}

/-- Lemma 4.5, expressed with the deviation scale as a parameter. -/
theorem global_slice_tail {d : ℕ} [IsProbabilityMeasure μ]
    (W : Fin d → Ω → ℝ) (h_indep : iIndepFun W μ)
    (h_meas : ∀ i, AEMeasurable (W i) μ)
    (h_range : ∀ i, ∀ᵐ ω ∂μ, W i ω ∈ Set.Icc 0 3)
    (h_mean : ∀ i, ∫ ω, W i ω ∂μ = 1)
    {Δ s : ℝ} (hΔ : 0 ≤ Δ) (hs : 0 ≤ s) :
    sliceProbability μ W Δ s ≤
      Real.exp (-(8 / 9 : ℝ) * (Δ ^ 2 / (d : ℝ)) * (1 + s) ^ 2) := by
  have h := bounded_lower_tail W h_indep h_meas h_range h_mean
    (show 0 ≤ 2 * Δ * (1 + s) by positivity)
  convert h using 1
  · simp [sliceProbability, neg_mul]
  · congr 1
    ring

/-- The very-low-energy estimate used in Lemma 4.7. -/
theorem low_energy_tail {d : ℕ} [IsProbabilityMeasure μ]
    (W : Fin d → Ω → ℝ) (h_indep : iIndepFun W μ)
    (h_meas : ∀ i, AEMeasurable (W i) μ)
    (h_range : ∀ i, ∀ᵐ ω ∂μ, W i ω ∈ Set.Icc 0 3)
    (h_mean : ∀ i, ∫ ω, W i ω ∂μ = 1) (hd : 0 < d) :
    μ.real {ω | (∑ i, W i ω) ≤ (d : ℝ) / 2} ≤ Real.exp (-(d : ℝ) / 18) := by
  have h := bounded_lower_tail W h_indep h_meas h_range h_mean
    (show 0 ≤ (d : ℝ) / 2 by positivity)
  have hevent : {ω | (∑ i, (W i ω - 1)) ≤ -((d : ℝ) / 2)} =
      {ω | (∑ i, W i ω) ≤ (d : ℝ) / 2} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    constructor <;> intro hh <;> linarith
  rw [hevent] at h
  convert h using 1
  congr 1
  have hdn : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  field_simp
  <;> ring

/-- Upper-tail Hoeffding estimate for the actual independent tilted coordinates.
The expectations are Bochner integrals, not supplied abstract numbers. -/
theorem bounded_upper_tail {d : ℕ} [IsProbabilityMeasure μ]
    (W : Fin d → Ω → ℝ) (h_indep : iIndepFun W μ)
    (h_meas : ∀ i, AEMeasurable (W i) μ)
    (h_range : ∀ i, ∀ᵐ ω ∂μ, W i ω ∈ Set.Icc 0 3)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ ∑ i, (W i ω - ∫ x, W i x ∂μ)} ≤
      Real.exp (-2 * u ^ 2 / (9 * (d : ℝ))) := by
  let X : Fin d → Ω → ℝ := fun i ω ↦ W i ω - ∫ x, W i x ∂μ
  have hi : iIndepFun X μ := h_indep.comp
    (fun i x ↦ x - ∫ y, W i y ∂μ) (fun _ ↦ measurable_id.sub measurable_const)
  have hg (i : Fin d) : HasSubgaussianMGF (X i) (9 / 4) μ := by
    convert hasSubgaussianMGF_of_mem_Icc (h_meas i) (h_range i) using 1
    norm_num [Real.nnnorm_of_nonneg]
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hi
    (s := Finset.univ) (c := fun _ ↦ (9 / 4 : ℝ≥0)) (fun i _ ↦ hg i) hu
  convert h using 1
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_ofNat]
  ring

/-- Concentration component of Lemma 4.9. The mean-deficit hypothesis is
explicit: this helper does not claim to establish that deficit for the tilted law. -/
theorem slice_acceptance_of_mean_gap {d : ℕ} [IsProbabilityMeasure μ]
    (W : Fin d → Ω → ℝ) (h_indep : iIndepFun W μ)
    (h_meas : ∀ i, Measurable (W i))
    (h_range : ∀ i, ∀ᵐ ω ∂μ, W i ω ∈ Set.Icc 0 3)
    {Δ threshold : ℝ} (hΔ : 0 ≤ Δ)
    (h_gap : (∑ i, ∫ x, W i x ∂μ) + Δ ≤ threshold) :
    1 - Real.exp (-2 * Δ ^ 2 / (9 * (d : ℝ))) ≤
      μ.real {ω | (∑ i, W i ω) ≤ threshold} := by
  have h := bounded_upper_tail W h_indep (fun i ↦ (h_meas i).aemeasurable) h_range hΔ
  have hs : MeasurableSet {ω | (∑ i, W i ω) ≤ threshold} := by
    exact measurableSet_le (Finset.measurable_sum _ fun i _ ↦ h_meas i) measurable_const
  have hsub : {ω | (∑ i, W i ω) ≤ threshold}ᶜ ⊆
      {ω | Δ ≤ ∑ i, (W i ω - ∫ x, W i x ∂μ)} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
    simp only [Set.mem_setOf_eq, Finset.sum_sub_distrib]
    linarith
  have hc := (measureReal_mono hsub).trans h
  rw [measureReal_compl hs] at hc
  simp only [measureReal_univ_eq_one] at hc
  linarith

/-- The one-dimensional transverse law before any tilt: normalized Lebesgue
measure on exactly the interval specified in the paper. -/
def cubeCoordinateLaw : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc (-Real.sqrt 3) (Real.sqrt 3))

instance cubeCoordinateLaw_probability : IsProbabilityMeasure cubeCoordinateLaw := by
  apply cond_isProbabilityMeasure_of_finite
  · simp only [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero]
    push_neg
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
  · simp only [Real.volume_Icc, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]

/-- The actual finite product law of the uniform transverse coordinates. -/
def cubeLaw (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ ↦ cubeCoordinateLaw)

instance cubeLaw_probability (d : ℕ) : IsProbabilityMeasure (cubeLaw d) := by
  unfold cubeLaw
  infer_instance

lemma cubeCoordinate_square_range :
    ∀ᵐ x ∂cubeCoordinateLaw, x ^ 2 ∈ Set.Icc (0 : ℝ) 3 := by
  filter_upwards [ae_cond_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with x hx
  refine ⟨sq_nonneg x, ?_⟩
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hsq : x ^ 2 ≤ (Real.sqrt 3) ^ 2 := sq_le_sq' hx.1 hx.2
  linarith

lemma cubeCoordinate_square_mean : ∫ x, x ^ 2 ∂cubeCoordinateLaw = (1 : ℝ) := by
  have hpos : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  rw [cubeCoordinateLaw, ProbabilityTheory.cond, integral_smul_measure]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), integral_pow]
  simp only [Real.volume_Icc, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul]
  norm_num
  field_simp
  nlinarith [sq_nonneg (Real.sqrt (3 : ℝ))]

lemma cubeCoordinate_fourth_mean : ∫ x, x ^ 4 ∂cubeCoordinateLaw = (9 / 5 : ℝ) := by
  have hpos : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  rw [cubeCoordinateLaw, ProbabilityTheory.cond, integral_smul_measure]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), integral_pow]
  simp only [Real.volume_Icc, ENNReal.toReal_inv, smul_eq_mul]
  norm_num
  field_simp
  nlinarith [sq_nonneg (Real.sqrt (3 : ℝ)), sq_nonneg ((Real.sqrt (3 : ℝ)) ^ 2 - 3)]

lemma cubeCoordinate_square_memLp : MemLp (fun x : ℝ ↦ x ^ 2) 2 cubeCoordinateLaw := by
  apply MemLp.of_bound (by fun_prop) 3
  filter_upwards [cubeCoordinate_square_range] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

/-- The variance parameter in the paper is computed for its actual uniform law. -/
lemma cubeCoordinate_square_variance :
    variance (fun x : ℝ ↦ x ^ 2) cubeCoordinateLaw = (4 / 5 : ℝ) := by
  rw [variance_eq_sub cubeCoordinate_square_memLp]
  have heq : (fun x : ℝ ↦ x ^ 2) ^ 2 = (fun x ↦ x ^ 4) := by
    ext x
    simp only [Pi.pow_apply]
    ring
  rw [heq, cubeCoordinate_square_mean, cubeCoordinate_fourth_mean]
  norm_num

lemma cubeCoordinate_centered_secondMoment :
    ∫ x, (1 - x ^ 2) ^ 2 ∂cubeCoordinateLaw = (4 / 5 : ℝ) := by
  have h := cubeCoordinate_square_variance
  rw [variance_eq_integral (by fun_prop), cubeCoordinate_square_mean] at h
  convert h using 1
  congr 1
  ext x
  ring

lemma cube_squares_independent (d : ℕ) :
    iIndepFun (fun i : Fin d ↦ fun x : Fin d → ℝ ↦ (x i) ^ 2) (cubeLaw d) :=
  iIndepFun_pi (fun _ ↦ (measurable_id.pow_const 2).aemeasurable)

lemma cube_square_range (d : ℕ) (i : Fin d) :
    ∀ᵐ x ∂cubeLaw d, (x i) ^ 2 ∈ Set.Icc (0 : ℝ) 3 := by
  have hm := measurePreserving_eval (fun _ : Fin d ↦ cubeCoordinateLaw) i
  have h := cubeCoordinate_square_range
  rw [← hm.map_eq] at h
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h

lemma cube_square_mean (d : ℕ) (i : Fin d) :
    ∫ x : Fin d → ℝ, (x i) ^ 2 ∂cubeLaw d = (1 : ℝ) := by
  have hm := measurePreserving_eval (fun _ : Fin d ↦ cubeCoordinateLaw) i
  have h := integral_map (μ := cubeLaw d) hm.measurable.aemeasurable
    (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
  change ∫ y, y ^ 2 ∂Measure.map (Function.eval i) (Measure.pi (fun _ : Fin d ↦ cubeCoordinateLaw)) = _ at h
  rw [hm.map_eq] at h
  exact h.symm.trans cubeCoordinate_square_mean

/-- The paper's actual slice probability, for independent uniform cube coordinates. -/
def cubeSlice (d : ℕ) (Δ s : ℝ) : ℝ :=
  sliceProbability (cubeLaw d) (fun i x ↦ (x i) ^ 2) Δ s

/-- Original global slice bound for the normalized Lebesgue product cube law. -/
theorem cubeSlice_global_tail (d : ℕ) {Δ s : ℝ} (hΔ : 0 ≤ Δ) (hs : 0 ≤ s) :
    cubeSlice d Δ s ≤
      Real.exp (-(8 / 9 : ℝ) * (Δ ^ 2 / (d : ℝ)) * (1 + s) ^ 2) :=
  global_slice_tail (μ := cubeLaw d) (fun i x ↦ (x i) ^ 2) (cube_squares_independent d)
    (fun i ↦ ((measurable_pi_apply i).pow_const 2).aemeasurable)
    (cube_square_range d) (cube_square_mean d) hΔ hs

/-- The concrete cube energy estimate used to prevent collapse of transverse variance. -/
theorem cube_low_energy_tail (d : ℕ) (hd : 0 < d) :
    (cubeLaw d).real {x | (∑ i, (x i) ^ 2) ≤ (d : ℝ) / 2} ≤
      Real.exp (-(d : ℝ) / 18) :=
  low_energy_tail (μ := cubeLaw d) (fun i x ↦ (x i) ^ 2) (cube_squares_independent d)
    (fun i ↦ ((measurable_pi_apply i).pow_const 2).aemeasurable)
    (cube_square_range d) (cube_square_mean d) hd

/-- Lower slope bound for the exponential on the interval used by the tilt. -/
lemma exp_sub_lower {x y : ℝ} (hy : -3 ≤ y) (hxy : y ≤ x) :
    Real.exp (-3) * (x - y) ≤ Real.exp x - Real.exp y := by
  have he := Real.add_one_le_exp (x - y)
  have hem := mul_le_mul_of_nonneg_left he (Real.exp_nonneg y)
  have hex : Real.exp y * Real.exp (x - y) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hex] at hem
  have hc : Real.exp (-3) * (x - y) ≤ Real.exp y * (x - y) :=
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hy) (sub_nonneg.mpr hxy)
  nlinarith

/-- Elementary quantitative covariance inequality. It yields the transverse
mean deficit without an unproved differentiation-under-the-integral assertion. -/
lemma tilt_covariance_pointwise {τ w : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hw : w ∈ Set.Icc (0 : ℝ) 3) :
    τ * Real.exp (-3) * (1 - w) ^ 2 ≤
      (1 - w) * (Real.exp (-τ * w) - Real.exp (-τ)) := by
  rcases le_total w 1 with h | h
  · have hex := exp_sub_lower (x := -τ * w) (y := -τ)
      (by linarith [hτ.2]) (by nlinarith [hτ.1])
    have hm := mul_le_mul_of_nonneg_left hex (show 0 ≤ 1 - w by linarith)
    nlinarith
  · have hex := exp_sub_lower (x := -τ) (y := -τ * w)
      (by nlinarith [hτ.1, hτ.2, hw.1, hw.2]) (by nlinarith [hτ.1])
    have hm := mul_le_mul_of_nonneg_left hex (show 0 ≤ w - 1 by linarith)
    nlinarith

/-- The paper's one-coordinate transverse tilted law. -/
def tiltedCoordinateLaw (τ : ℝ) : Measure ℝ :=
  cubeCoordinateLaw.tilted (fun x ↦ -τ * x ^ 2)

lemma tiltedCoordinate_exponential_integrable (τ : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (-τ * x ^ 2)) cubeCoordinateLaw :=
  integrable_exp_mul_of_mem_Icc (by fun_prop) cubeCoordinate_square_range

instance tiltedCoordinateLaw_probability (τ : ℝ) :
    IsProbabilityMeasure (tiltedCoordinateLaw τ) :=
  isProbabilityMeasure_tilted (tiltedCoordinate_exponential_integrable τ)

lemma tiltedCoordinate_square_range (τ : ℝ) :
    ∀ᵐ x ∂tiltedCoordinateLaw τ, x ^ 2 ∈ Set.Icc (0 : ℝ) 3 :=
  tilted_absolutelyContinuous cubeCoordinateLaw _ cubeCoordinate_square_range

/-- A numerical universal deficit coefficient. -/
def meanDeficitConstant : ℝ := (4 / 5 : ℝ) * Real.exp (-3)

lemma meanDeficitConstant_pos : 0 < meanDeficitConstant := by
  unfold meanDeficitConstant
  positivity

/-- Quantitative form of the tilted mean estimate in Lemma 4.9 for the actual
one-dimensional density. -/
theorem tiltedCoordinate_square_mean_le {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ∫ x, x ^ 2 ∂tiltedCoordinateLaw τ ≤ 1 - meanDeficitConstant * τ := by
  let Z : ℝ := ∫ x, Real.exp (-τ * x ^ 2) ∂cubeCoordinateLaw
  let N : ℝ := ∫ x, x ^ 2 * Real.exp (-τ * x ^ 2) ∂cubeCoordinateLaw
  have hZ := tiltedCoordinate_exponential_integrable τ
  have hZpos : 0 < Z := integral_exp_pos hZ
  have hZle : Z ≤ 1 := by
    calc
      Z ≤ ∫ _x : ℝ, (1 : ℝ) ∂cubeCoordinateLaw := by
        apply integral_mono_ae hZ (integrable_const 1)
        filter_upwards [cubeCoordinate_square_range] with x hx
        exact Real.exp_le_one_iff.mpr (by nlinarith [hτ.1, hx.1])
      _ = 1 := by simp
  have hW : Integrable (fun x : ℝ ↦ x ^ 2) cubeCoordinateLaw :=
    Integrable.of_mem_Icc 0 3 (by fun_prop) cubeCoordinate_square_range
  have hN : Integrable (fun x : ℝ ↦ x ^ 2 * Real.exp (-τ * x ^ 2)) cubeCoordinateLaw := by
    apply hW.mono' (by fun_prop)
    filter_upwards [cubeCoordinate_square_range] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right hx.1 (Real.exp_le_one_iff.mpr (by nlinarith [hτ.1, hx.1]))
  have hC : Integrable (fun x : ℝ ↦ (1 - x ^ 2) ^ 2) cubeCoordinateLaw := by
    apply Integrable.of_mem_Icc 0 4 (by fun_prop)
    filter_upwards [cubeCoordinate_square_range] with x hx
    refine ⟨sq_nonneg _, ?_⟩
    have hb : (1 - x ^ 2) ^ 2 ≤ (2 : ℝ) ^ 2 := sq_le_sq' (by linarith [hx.2]) (by linarith [hx.1])
    norm_num at hb ⊢
    exact hb
  have hi : Integrable (fun x : ℝ ↦ (1 - x ^ 2) *
      (Real.exp (-τ * x ^ 2) - Real.exp (-τ))) cubeCoordinateLaw := by
    convert ((hZ.sub hN).sub (integrable_const (Real.exp (-τ)))).add
      (hW.const_mul (Real.exp (-τ))) using 1
    ext x
    dsimp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    ring
  have he := integral_mono_ae (hC.const_mul (τ * Real.exp (-3))) hi
    (cubeCoordinate_square_range.mono fun x hx ↦ tilt_covariance_pointwise hτ hx)
  have hid : (∫ x, (1 - x ^ 2) * (Real.exp (-τ * x ^ 2) - Real.exp (-τ))
      ∂cubeCoordinateLaw) = Z - N := by
    have hf : (fun x : ℝ ↦ (1 - x ^ 2) * (Real.exp (-τ * x ^ 2) - Real.exp (-τ))) =
        (fun x ↦ (Real.exp (-τ * x ^ 2) - x ^ 2 * Real.exp (-τ * x ^ 2) -
          Real.exp (-τ)) + Real.exp (-τ) * x ^ 2) := by ext x; ring
    have hdiff : Integrable (fun x : ℝ ↦ Real.exp (-τ * x ^ 2) - x ^ 2 * Real.exp (-τ * x ^ 2)) cubeCoordinateLaw := hZ.sub hN
    have hconst : Integrable (fun x : ℝ ↦ Real.exp (-τ * x ^ 2) - x ^ 2 * Real.exp (-τ * x ^ 2) - Real.exp (-τ)) cubeCoordinateLaw := hdiff.sub (integrable_const _)
    have hwmul : Integrable (fun x : ℝ ↦ Real.exp (-τ) * x ^ 2) cubeCoordinateLaw := hW.const_mul _
    rw [hf, integral_add hconst hwmul,
      integral_sub hdiff (integrable_const _), integral_sub hZ hN,
      integral_const_mul, cubeCoordinate_square_mean]
    simp [Z, N]
  rw [integral_const_mul, cubeCoordinate_centered_secondMoment, hid] at he
  have hdef : meanDeficitConstant * τ ≤ Z - N := by unfold meanDeficitConstant; nlinarith
  have hm : (∫ x, x ^ 2 ∂tiltedCoordinateLaw τ) = N / Z := by
    rw [tiltedCoordinateLaw, integral_tilted]
    simp only [smul_eq_mul]
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [N, Z]
    ring
  rw [hm]
  apply (div_le_iff₀ hZpos).mpr
  have hc : 0 ≤ meanDeficitConstant * τ := mul_nonneg meanDeficitConstant_pos.le hτ.1
  have hmul := mul_le_mul_of_nonneg_left hZle hc
  nlinarith

/-- Independent copies of the one-dimensional tilted transverse law. -/
def tiltedCubeLaw (d : ℕ) (τ : ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ ↦ tiltedCoordinateLaw τ)

instance tiltedCubeLaw_probability (d : ℕ) (τ : ℝ) :
    IsProbabilityMeasure (tiltedCubeLaw d τ) := by
  unfold tiltedCubeLaw
  infer_instance

lemma tilted_cube_squares_independent (d : ℕ) (τ : ℝ) :
    iIndepFun (fun i : Fin d ↦ fun x : Fin d → ℝ ↦ (x i) ^ 2) (tiltedCubeLaw d τ) :=
  iIndepFun_pi (fun _ ↦ (measurable_id.pow_const 2).aemeasurable)

lemma tilted_cube_square_range (d : ℕ) (τ : ℝ) (i : Fin d) :
    ∀ᵐ x ∂tiltedCubeLaw d τ, (x i) ^ 2 ∈ Set.Icc (0 : ℝ) 3 := by
  have hm := measurePreserving_eval (fun _ : Fin d ↦ tiltedCoordinateLaw τ) i
  have h := tiltedCoordinate_square_range τ
  rw [← hm.map_eq] at h
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h

lemma tilted_cube_square_mean (d : ℕ) (τ : ℝ) (i : Fin d) :
    ∫ x : Fin d → ℝ, (x i) ^ 2 ∂tiltedCubeLaw d τ =
      ∫ u, u ^ 2 ∂tiltedCoordinateLaw τ := by
  have hm := measurePreserving_eval (fun _ : Fin d ↦ tiltedCoordinateLaw τ) i
  have h := integral_map (μ := Measure.pi (fun _ : Fin d ↦ tiltedCoordinateLaw τ))
    hm.measurable.aemeasurable (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
  rw [hm.map_eq] at h
  exact h.symm

/-- Actual transverse acceptance probability at isotropized axial coordinate `z`. -/
def tiltedSlice (d : ℕ) (τ Δ b z : ℝ) : ℝ :=
  (tiltedCubeLaw d τ).real
    {x | (∑ i, (x i) ^ 2) ≤ (d : ℝ) - 2 * Δ * (1 + Real.sqrt b * |z|)}

lemma tiltedSlice_measurable (d : ℕ) (τ Δ b : ℝ) :
    Measurable (tiltedSlice d τ Δ b) := by
  have hs : MeasurableSet {q : ℝ × (Fin d → ℝ) |
      (∑ i, (q.2 i) ^ 2) ≤ (d : ℝ) - 2 * Δ * (1 + Real.sqrt b * |q.1|)} := by
    apply measurableSet_le <;> fun_prop
  exact (measurable_measure_prodMk_left (ν := tiltedCubeLaw d τ) hs).ennreal_toReal

lemma tiltedSlice_even (d : ℕ) (τ Δ b z : ℝ) :
    tiltedSlice d τ Δ b (-z) = tiltedSlice d τ Δ b z := by
  simp [tiltedSlice]

lemma tiltedSlice_mem_Icc (d : ℕ) (τ Δ b z : ℝ) :
    tiltedSlice d τ Δ b z ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

/-- The quantitative slice-acceptance theorem for the actual product tilted law.
The remaining hypotheses are only the deterministic scale inequalities to be
verified after the raw covariance estimates. -/
theorem tiltedSlice_acceptance_of_deficit (d : ℕ) {τ Δ b z : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hΔ : 0 ≤ Δ)
    (hdef : 2 * Δ * (1 + Real.sqrt b * |z|) + Δ ≤
      (d : ℝ) * meanDeficitConstant * τ) :
    1 - Real.exp (-2 * Δ ^ 2 / (9 * (d : ℝ))) ≤ tiltedSlice d τ Δ b z := by
  apply slice_acceptance_of_mean_gap (μ := tiltedCubeLaw d τ)
    (fun i x ↦ (x i) ^ 2) (tilted_cube_squares_independent d τ)
    (fun i ↦ (measurable_pi_apply i).pow_const 2) (tilted_cube_square_range d τ) hΔ
  have hm : (∑ i : Fin d, ∫ x : Fin d → ℝ, (x i) ^ 2 ∂tiltedCubeLaw d τ) ≤
      (d : ℝ) * (1 - meanDeficitConstant * τ) := by
    calc
      _ ≤ ∑ _i : Fin d, (1 - meanDeficitConstant * τ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [tilted_cube_square_mean]
        exact tiltedCoordinate_square_mean_le hτ
      _ = _ := by simp; ring
  nlinarith

end LowerProbability
end GaussianTilt
