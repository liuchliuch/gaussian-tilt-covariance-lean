import GaussianTilt.MomentMapSchauderRadialIntegrals

/-!
# Far-field power integrals for Hölder singular-integral estimates

Subcritical local singularities are paired with supercritical inverse-power
tails. The latter are dominated by the integrable Japanese-bracket profile,
then scaled by the actual Haar change-of-variables theorem.
-/
noncomputable section
open MeasureTheory Set Filter Module
open scoped ENNReal Topology
namespace GaussianTilt.MomentMapSchauder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma inversePower_le_japaneseBracket {k : ℝ} (hk : 0 ≤ k) {x : E} (hx : 1 ≤ ‖x‖) :
    ‖x‖ ^ (-k) ≤ (2 : ℝ) ^ k * (1 + ‖x‖) ^ (-k) := by
  have h := Real.rpow_le_rpow_of_nonpos
    (show (0 : ℝ) < (1 + ‖x‖) / 2 by positivity)
    (show (1 + ‖x‖) / 2 ≤ ‖x‖ by linarith) (neg_nonpos.mpr hk)
  rw [Real.div_rpow (by positivity) (by norm_num),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm] at h
  exact h

lemma integrableOn_norm_neg_rpow_outside_unitBall {k : ℝ}
    (hnk : (finrank ℝ E : ℝ) < k) :
    IntegrableOn (fun x : E => ‖x‖ ^ (-k)) (Metric.closedBall (0 : E) 1)ᶜ μ := by
  have hk : 0 < k := (Nat.cast_nonneg _).trans_lt hnk
  apply (((integrable_one_add_norm (μ := μ) hnk).const_mul ((2 : ℝ) ^ k)).integrableOn).mono'
    (by fun_prop : Measurable (fun x : E => ‖x‖ ^ (-k))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with x hx
  have hx' : (1 : ℝ) ≤ ‖x‖ := by
    have hn : ¬‖x‖ ≤ 1 := by simpa only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right] using hx
    exact (lt_of_not_ge hn).le
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) (-k))] using
    inversePower_le_japaneseBracket hk.le hx'

lemma indicator_outsideBall_comp_smul (p : ℝ) {R : ℝ} (hR : 0 < R) (x : E) :
    (Metric.closedBall (0 : E) R)ᶜ.indicator (fun y => ‖y‖ ^ p) (R • x) =
      R ^ p * (Metric.closedBall (0 : E) 1)ᶜ.indicator (fun y => ‖y‖ ^ p) x := by
  have hm : R • x ∈ (Metric.closedBall (0 : E) R)ᶜ ↔ x ∈ (Metric.closedBall (0 : E) 1)ᶜ := by
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hR, not_le]
    constructor <;> intro h <;> nlinarith
  by_cases hx : x ∈ (Metric.closedBall (0 : E) 1)ᶜ
  · rw [indicator_of_mem (hm.mpr hx), indicator_of_mem hx, norm_smul,
      Real.norm_eq_abs, abs_of_pos hR, Real.mul_rpow hR.le (norm_nonneg x)]
  · rw [indicator_of_notMem (fun h => hx (hm.mp h)), indicator_of_notMem hx, mul_zero]

/-- Actual tail integrability for every positive inner radius. -/
theorem integrableOn_norm_neg_rpow_outside_closedBall {k : ℝ}
    (hnk : (finrank ℝ E : ℝ) < k) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : E => ‖x‖ ^ (-k)) (Metric.closedBall (0 : E) R)ᶜ μ := by
  have hu : Integrable ((Metric.closedBall (0 : E) 1)ᶜ.indicator (fun x => ‖x‖ ^ (-k))) μ :=
    (integrable_indicator_iff measurableSet_closedBall.compl).mpr
      (integrableOn_norm_neg_rpow_outside_unitBall (μ := μ) hnk)
  have hscale : Integrable
      (fun x => (Metric.closedBall (0 : E) R)ᶜ.indicator (fun y => ‖y‖ ^ (-k)) (R • x)) μ := by
    simpa only [indicator_outsideBall_comp_smul (-k) hR] using hu.const_mul (R ^ (-k))
  exact (integrable_indicator_iff measurableSet_closedBall.compl).mp
    ((integrable_comp_smul_iff μ _ hR.ne').mp hscale)

/-- Exact radius scaling of the far-field integral. -/
theorem integral_norm_rpow_outside_closedBall_scale (p : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ x in (Metric.closedBall (0 : E) R)ᶜ, ‖x‖ ^ p ∂μ) =
      R ^ ((finrank ℝ E : ℝ) + p) *
        ∫ x in (Metric.closedBall (0 : E) 1)ᶜ, ‖x‖ ^ p ∂μ := by
  have he := μ.integral_comp_smul_of_nonneg
    ((Metric.closedBall (0 : E) R)ᶜ.indicator (fun y => ‖y‖ ^ p)) R (hR := hR.le)
  simp_rw [indicator_outsideBall_comp_smul p hR] at he
  rw [integral_const_mul, integral_indicator measurableSet_closedBall.compl,
    integral_indicator measurableSet_closedBall.compl] at he
  simp only [smul_eq_mul] at he
  have hm := congrArg (fun t : ℝ => R ^ finrank ℝ E * t) he
  dsimp only at hm
  simp only [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hR.ne'), one_mul] at hm
  rw [← hm, ← Real.rpow_natCast R (finrank ℝ E), ← Real.rpow_add hR]

/-- The far-field kernel in the Hessian Hölder estimate has the precise
`R^(α-1)` decay, with a finite radius-independent positive constant. -/
theorem exists_holderKernel_tail_bound {α : ℝ} (hα : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R →
      IntegrableOn (fun x : E => ‖x‖ ^ (α - (finrank ℝ E : ℝ) - 1))
        (Metric.closedBall 0 R)ᶜ μ ∧
      (∫ x in (Metric.closedBall (0 : E) R)ᶜ, ‖x‖ ^ (α - (finrank ℝ E : ℝ) - 1) ∂μ) ≤
        C * R ^ (α - 1) := by
  let I : ℝ := ∫ x in (Metric.closedBall (0 : E) 1)ᶜ, ‖x‖ ^ (α - (finrank ℝ E : ℝ) - 1) ∂μ
  refine ⟨max I 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro R hR
  have hk : (finrank ℝ E : ℝ) < (finrank ℝ E : ℝ) + 1 - α := by linarith
  have hexp : -((finrank ℝ E : ℝ) + 1 - α) = α - (finrank ℝ E : ℝ) - 1 := by ring
  refine ⟨?_, ?_⟩
  · simpa only [hexp] using integrableOn_norm_neg_rpow_outside_closedBall (μ := μ) hk hR
  · have he := integral_norm_rpow_outside_closedBall_scale (μ := μ)
      (α - (finrank ℝ E : ℝ) - 1) hR
    have hsum : (finrank ℝ E : ℝ) + (α - (finrank ℝ E : ℝ) - 1) = α - 1 := by ring
    rw [hsum, mul_comm] at he
    rw [he]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hR.le _)

end GaussianTilt.MomentMapSchauder
