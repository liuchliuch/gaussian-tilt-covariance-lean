import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Local integrability of the Newtonian singularity

Layer cake and the actual Haar scaling formula for balls prove local
integrability of inverse powers with exponent strictly below the dimension.
No polar-coordinate or fundamental-solution identity is assumed.
-/
noncomputable section
open MeasureTheory Set Filter Module
open scoped ENNReal Topology
namespace GaussianTilt.MomentMapSchauder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma inversePower_superlevel_subset_closedBall {k t : ℝ}
    (hk : 0 < k) (ht : 0 < t) :
    {x : E | t ≤ ‖x‖ ^ (-k)} ⊆ Metric.closedBall 0 (t ^ (-k⁻¹)) := by
  intro x hx
  change t ≤ ‖x‖ ^ (-k) at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_cases hx0 : x = 0
  · subst x
    simp only [norm_zero, Real.zero_rpow (neg_ne_zero.mpr hk.ne')] at hx
    exact (not_le_of_gt ht hx).elim
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    simpa only [neg_inv] using
      (Real.le_rpow_inv_iff_of_neg hn ht (neg_lt_zero.mpr hk)).mpr hx

/-- Layer-cake finiteness for a subcritical inverse power on any finite ball. -/
theorem finite_lintegral_norm_neg_rpow_closedBall {k : ℝ}
    (hk : 0 < k) (hkn : k < (finrank ℝ E : ℝ)) (R : ℝ) :
    (∫⁻ x in Metric.closedBall (0 : E) R, ENNReal.ofReal (‖x‖ ^ (-k)) ∂μ) < ∞ := by
  have hm : Measurable (fun x : E => ‖x‖ ^ (-k)) := by fun_prop
  have hn : ∀ x : E, 0 ≤ ‖x‖ ^ (-k) := fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [lintegral_eq_lintegral_meas_le (μ.restrict (Metric.closedBall (0 : E) R))
    (Eventually.of_forall hn) hm.aemeasurable]
  let f : ℝ → ℝ≥0∞ := fun t =>
    (μ.restrict (Metric.closedBall (0 : E) R)) {x : E | t ≤ ‖x‖ ^ (-k)}
  change (∫⁻ t in Ioi (0 : ℝ), f t) < ∞
  calc
    _ ≤ ∫⁻ t in Ioc 0 1 ∪ Ioi 1, f t := lintegral_mono_set Ioi_subset_Ioc_union_Ioi
    _ ≤ (∫⁻ t in Ioc 0 1, f t) + ∫⁻ t in Ioi 1, f t := lintegral_union_le _ _ _
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · have hb : ∀ t : ℝ, f t ≤ μ (Metric.closedBall (0 : E) R) := by
      intro t
      calc
        _ ≤ (μ.restrict (Metric.closedBall (0 : E) R)) univ := measure_mono (subset_univ _)
        _ = _ := Measure.restrict_apply_univ _
    apply lt_of_le_of_lt (lintegral_mono (fun t => hb t))
    simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc,
      sub_zero, ENNReal.ofReal_one, mul_one]
    exact measure_closedBall_lt_top
  · have htail : ∀ t ∈ Ioi (1 : ℝ), f t ≤
        ENNReal.ofReal (t ^ (-(k⁻¹ * (finrank ℝ E : ℝ)))) * μ (Metric.ball (0 : E) 1) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      calc
        _ ≤ μ {x : E | t ≤ ‖x‖ ^ (-k)} := Measure.restrict_apply_le _ _
        _ ≤ μ (Metric.closedBall 0 (t ^ (-k⁻¹))) :=
          measure_mono (inversePower_superlevel_subset_closedBall hk ht0)
        _ = _ := by
          rw [μ.addHaar_closedBall (0 : E) (Real.rpow_nonneg ht0.le _)]
          congr 2
          simp [Real.rpow_mul ht0.le, ← neg_mul]
    apply lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi htail)
    rw [lintegral_mul_const' _ _ measure_ball_lt_top.ne]
    apply ENNReal.mul_lt_top _ measure_ball_lt_top
    apply IntegrableOn.setLIntegral_lt_top
    apply integrableOn_Ioi_rpow_of_lt _ zero_lt_one
    have hdiv : (1 : ℝ) < (finrank ℝ E : ℝ) / k := (lt_div_iff₀ hk).mpr (by simpa using hkn)
    have hmul : (1 : ℝ) < k⁻¹ * (finrank ℝ E : ℝ) := by
      simpa only [div_eq_mul_inv, mul_comm] using hdiv
    linarith

/-- The literal inverse power is locally Bochner integrable, including at
the origin with Lean's convention for a negative real power of zero. -/
theorem integrableOn_norm_neg_rpow_closedBall {k : ℝ}
    (hk : 0 < k) (hkn : k < (finrank ℝ E : ℝ)) (R : ℝ) :
    IntegrableOn (fun x : E => ‖x‖ ^ (-k)) (Metric.closedBall 0 R) μ := by
  refine ⟨(by fun_prop : Measurable (fun x : E => ‖x‖ ^ (-k))).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun x : E => Real.rpow_nonneg (norm_nonneg x) (-k)))).mpr
  exact finite_lintegral_norm_neg_rpow_closedBall hk hkn R

/-- Exact scaling for an actual restricted power integral. The formula is
proved from Haar change of variables and applies to every real exponent. -/
theorem integral_norm_rpow_closedBall_scale (p : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ x in Metric.closedBall (0 : E) R, ‖x‖ ^ p ∂μ) =
      R ^ ((finrank ℝ E : ℝ) + p) *
        ∫ x in Metric.closedBall (0 : E) 1, ‖x‖ ^ p ∂μ := by
  have hind (x : E) :
      (Metric.closedBall (0 : E) R).indicator (fun y => ‖y‖ ^ p) (R • x) =
        R ^ p * (Metric.closedBall (0 : E) 1).indicator (fun y => ‖y‖ ^ p) x := by
    have hm : R • x ∈ Metric.closedBall (0 : E) R ↔ x ∈ Metric.closedBall (0 : E) 1 := by
      simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      constructor <;> intro h <;> nlinarith
    by_cases hx : x ∈ Metric.closedBall (0 : E) 1
    · rw [indicator_of_mem (hm.mpr hx), indicator_of_mem hx,
        norm_smul, Real.norm_eq_abs, abs_of_pos hR, Real.mul_rpow hR.le (norm_nonneg x)]
    · rw [indicator_of_notMem (fun h => hx (hm.mp h)), indicator_of_notMem hx, mul_zero]
  have he := μ.integral_comp_smul_of_nonneg
    ((Metric.closedBall (0 : E) R).indicator (fun y => ‖y‖ ^ p)) R (hR := hR.le)
  simp_rw [hind] at he
  rw [integral_const_mul, integral_indicator measurableSet_closedBall,
    integral_indicator measurableSet_closedBall] at he
  simp only [smul_eq_mul] at he
  have hm := congrArg (fun t : ℝ => R ^ finrank ℝ E * t) he
  dsimp only at hm
  simp only [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hR.ne'), one_mul] at hm
  rw [← hm, ← Real.rpow_natCast R (finrank ℝ E), ← Real.rpow_add hR]

/-- The singular Hölder kernel has the precise expected scale on balls.
The constant is its actual finite integral over the unit ball. -/
theorem holderKernel_integrable_and_scale {α : ℝ}
    (hα : 0 < α) (hαn : α < (finrank ℝ E : ℝ)) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : E => ‖x‖ ^ (α - (finrank ℝ E : ℝ))) (Metric.closedBall 0 R) μ ∧
      (∫ x in Metric.closedBall (0 : E) R, ‖x‖ ^ (α - (finrank ℝ E : ℝ)) ∂μ) =
        R ^ α * ∫ x in Metric.closedBall (0 : E) 1, ‖x‖ ^ (α - (finrank ℝ E : ℝ)) ∂μ := by
  constructor
  · have hi := integrableOn_norm_neg_rpow_closedBall (μ := μ) (sub_pos.mpr hαn)
      (show (finrank ℝ E : ℝ) - α < (finrank ℝ E : ℝ) by linarith) R
    simpa only [neg_sub] using hi
  · simpa only [add_sub_cancel] using
      integral_norm_rpow_closedBall_scale (μ := μ) (α - (finrank ℝ E : ℝ)) hR

/-- A positive, radius-independent upper constant for the Hölder singular
integral. Integrability is proved at every radius as part of the conclusion. -/
theorem exists_holderKernel_ball_bound {α : ℝ}
    (hα : 0 < α) (hαn : α < (finrank ℝ E : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R →
      IntegrableOn (fun x : E => ‖x‖ ^ (α - (finrank ℝ E : ℝ))) (Metric.closedBall 0 R) μ ∧
      (∫ x in Metric.closedBall (0 : E) R, ‖x‖ ^ (α - (finrank ℝ E : ℝ)) ∂μ) ≤ C * R ^ α := by
  let I : ℝ := ∫ x in Metric.closedBall (0 : E) 1, ‖x‖ ^ (α - (finrank ℝ E : ℝ)) ∂μ
  refine ⟨max I 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro R hR
  obtain ⟨hi, he⟩ := holderKernel_integrable_and_scale (μ := μ) hα hαn hR
  refine ⟨hi, ?_⟩
  rw [he, mul_comm]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hR.le α)

lemma abs_log_le_self_add_inv {t : ℝ} (ht : 0 ≤ t) : |Real.log t| ≤ t + t⁻¹ := by
  rcases ht.eq_or_lt with ht0 | ht0
  · simp [← ht0]
  · have h₁ := Real.log_le_sub_one_of_pos ht0
    have h₂ := Real.log_le_sub_one_of_pos (inv_pos.mpr ht0)
    rw [Real.log_inv] at h₂
    apply abs_le.mpr
    constructor <;> linarith [inv_nonneg.mpr ht]

/-- Local integrability of the logarithmic Newtonian kernel in every
dimension greater than one, proved by domination with norm plus inverse norm. -/
theorem integrableOn_log_norm_closedBall (hdim : 1 < finrank ℝ E) (R : ℝ) :
    IntegrableOn (fun x : E => Real.log ‖x‖) (Metric.closedBall 0 R) μ := by
  have hi : IntegrableOn (fun x : E => ‖x‖⁻¹) (Metric.closedBall 0 R) μ := by
    simpa only [Real.rpow_neg_one] using integrableOn_norm_neg_rpow_closedBall (μ := μ)
      (k := 1) zero_lt_one (by exact_mod_cast hdim) R
  have hn : IntegrableOn (fun x : E => ‖x‖) (Metric.closedBall 0 R) μ :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall _ _) continuous_norm.continuousOn
  apply (hn.add hi).mono' (Real.measurable_log.comp measurable_norm).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using abs_log_le_self_add_inv (norm_nonneg x))

/-- The log of the squared norm is the literal profile used in the
regularized two-dimensional fundamental solution. -/
theorem integrableOn_log_norm_sq_closedBall (hdim : 1 < finrank ℝ E) (R : ℝ) :
    IntegrableOn (fun x : E => Real.log (‖x‖ ^ 2)) (Metric.closedBall 0 R) μ := by
  simpa only [Real.log_pow, Nat.cast_ofNat] using
    (integrableOn_log_norm_closedBall (μ := μ) hdim R).const_mul 2

end GaussianTilt.MomentMapSchauder
