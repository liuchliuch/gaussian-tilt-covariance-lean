import GaussianTilt.IsotropicIntegrability
import GaussianTilt.PaourisSymmetrization
import GaussianTilt.WhiteningTruncation

/-! # Passing genuine compact-law tail bounds to noncompact laws

Conditioning on expanding closed balls converges on every measurable event.
The affine estimate below compares the original samples to their actual
whitened samples, and therefore transfers probability tails without assuming
any higher moments or any convergence of those moments.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal Matrix.Norms.L2Operator

namespace GaussianTilt.Paouris

variable {n : ℕ}

lemma eventually_mem_closedBall (x : Reference.Space n) :
    ∀ᶠ k : ℕ in atTop, x ∈ Metric.closedBall 0 (k : ℝ) := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖x‖)] with k hk
  simpa only [Metric.mem_closedBall, dist_zero_right] using hk

theorem tendsto_real_inter_closedBall (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] {s : Set (Reference.Space n)} (hs : MeasurableSet s) :
    Tendsto (fun k : ℕ ↦ μ.real (Metric.closedBall 0 (k : ℝ) ∩ s))
      atTop (𝓝 (μ.real s)) := by
  have ht := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun k : ℕ ↦ (Metric.closedBall 0 (k : ℝ) ∩ s).indicator (fun _ ↦ (1 : ℝ)))
    (f := s.indicator (fun _ ↦ (1 : ℝ))) (fun _ ↦ (1 : ℝ))
    (fun k ↦ (measurable_const.indicator (measurableSet_closedBall.inter hs)).aestronglyMeasurable)
    (integrable_const 1)
    (fun k ↦ ae_of_all _ (fun x ↦ by
      by_cases hx : x ∈ Metric.closedBall 0 (k : ℝ) ∩ s <;> simp [hx]))
    (ae_of_all _ (fun x ↦ by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_mem_closedBall x] with k hk
      by_cases hx : x ∈ s <;> simp [hx, hk]))
  simpa only [integral_indicator_const _ (measurableSet_closedBall.inter hs),
    integral_indicator_const _ hs, smul_eq_mul, mul_one] using ht

theorem tendsto_cond_closedBall_real (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] {s : Set (Reference.Space n)} (hs : MeasurableSet s) :
    Tendsto (fun k : ℕ ↦ (cond μ (Metric.closedBall 0 (k : ℝ))).real s)
      atTop (𝓝 (μ.real s)) := by
  have hm : Tendsto (fun k : ℕ ↦ μ.real (Metric.closedBall 0 (k : ℝ))) atTop (𝓝 1) := by
    simpa only [inter_univ, measureReal_univ_eq_one] using
      tendsto_real_inter_closedBall μ MeasurableSet.univ
  have ht := (tendsto_real_inter_closedBall μ hs).div hm (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun k : ℕ ↦ μ.real (Metric.closedBall 0 (k : ℝ) ∩ s) /
    μ.real (Metric.closedBall 0 (k : ℝ))) atTop (𝓝 (μ.real s / 1)) at ht
  simpa [measureReal_def, cond_apply measurableSet_closedBall,
    ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply, mul_comm] using ht

theorem norm_le_whitening (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hC : (Whitening.covariance μ).PosDef) (x : Reference.Space n) :
    ‖x‖ ≤ ‖Whitening.root (Whitening.covariance μ)‖ * ‖Whitening.whitenMap μ x‖ +
      ‖Whitening.center μ‖ := by
  calc
    ‖x‖ = ‖(x - Whitening.center μ) + Whitening.center μ‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - Whitening.center μ‖ + ‖Whitening.center μ‖ := norm_add_le _ _
    _ ≤ _ := by
      apply add_le_add_right
      rw [← Whitening.root_whitenMap hC x]
      exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)
        (Whitening.root (Whitening.covariance μ))).le_opNorm _

theorem norm_tail_le_whitened_tail (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hC : (Whitening.covariance μ).PosDef)
    (hroot : ‖Whitening.root (Whitening.covariance μ)‖ ≤ 2)
    (hcenter : ‖Whitening.center μ‖ ≤ 1) {C r : ℝ} (hr : 1 ≤ r) :
    μ.real {x | (2 * C + 1) * r ≤ ‖x‖} ≤
      (Whitening.law μ).real {y | C * r ≤ ‖y‖} := by
  have hevent : {x : Reference.Space n | (2 * C + 1) * r ≤ ‖x‖} ⊆
      Whitening.whitenMap μ ⁻¹' {y | C * r ≤ ‖y‖} := by
    intro x hx
    change C * r ≤ ‖Whitening.whitenMap μ x‖
    have hb := norm_le_whitening μ hC x
    have hb' := mul_le_mul_of_nonneg_right hroot (norm_nonneg (Whitening.whitenMap μ x))
    change (2 * C + 1) * r ≤ ‖x‖ at hx
    nlinarith
  have hm : MeasurableSet {y : Reference.Space n | C * r ≤ ‖y‖} :=
    measurableSet_le measurable_const continuous_norm.measurable
  change μ.real _ ≤ (μ.map (Whitening.whitenMap μ)).real _
  simp only [measureReal_def]
  rw [Measure.map_apply (Whitening.continuous_whitenMap μ).measurable hm]
  exact measureReal_mono hevent

/-- Universal threshold for all isotropic logconcave laws. -/
def generalPaourisTailConstant : ℝ := 2 * generalCompactPaourisTailConstant + 1

lemma generalPaourisTailConstant_pos : 0 < generalPaourisTailConstant := by
  unfold generalPaourisTailConstant
  linarith [generalCompactPaourisTailConstant_pos]

/-- The original Paouris tail theorem, without a compact-support assumption.
The higher moments of the original law are not assumed in this passage. -/
theorem isotropic_norm_tail (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hl : Reference.logconcave μ) (hi : Reference.isotropic μ)
    {t : ℝ} (ht : 1 ≤ t) :
    μ.real {x | generalPaourisTailConstant * t * Real.sqrt (n : ℝ) ≤ ‖x‖} ≤
      Real.exp (-t * Real.sqrt (n : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, neg_zero, Real.exp_zero]
    simpa using (measureReal_mono (μ := μ)
      (show {x : Reference.Space 0 | (0 : ℝ) ≤ ‖x‖} ⊆ univ from subset_univ _))
  · letI : NeZero n := ⟨hn⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hr : 1 ≤ t * Real.sqrt (n : ℝ) :=
      one_le_mul_of_one_le_of_one_le ht (Real.one_le_sqrt.mpr hn1)
    have hI := Reference.isotropic_norm_sq_integrable hi
    have hevent : MeasurableSet {x : Reference.Space n |
        generalPaourisTailConstant * t * Real.sqrt (n : ℝ) ≤ ‖x‖} :=
      measurableSet_le measurable_const continuous_norm.measurable
    apply le_of_tendsto (tendsto_cond_closedBall_real μ hevent)
    filter_upwards [Whitening.eventually_ballRestriction_probability μ,
      Whitening.eventually_ballRestriction_covariance_posDef μ hI hi,
      Whitening.eventually_ballRestriction_root_norm_le_two μ hI hi,
      Whitening.eventually_ballRestriction_center_norm_le_one μ hI hi,
      Whitening.eventually_ballRestriction_logconcave hl] with k hp hC hR hm hlog
    let ρ := Whitening.ballRestriction μ k
    letI : IsProbabilityMeasure ρ := hp
    have hc : Reference.compactlySupported ρ := Whitening.ballRestriction_compactlySupported μ k
    have hX := Whitening.compact_coordinates_memLp hc
    have heq : Reference.covariance ρ = Whitening.covariance ρ :=
      Reference.covariance_eq_covarianceMatrix hX
    change (Reference.covariance ρ).PosDef at hC
    change ‖Whitening.root (Reference.covariance ρ)‖ ≤ 2 at hR
    rw [heq] at hC hR
    have htail := compact_isotropic_norm_tail (Whitening.law ρ)
      (Whitening.law_compactlySupported hc) (Whitening.law_logconcave hlog hC)
      (Whitening.law_isotropic hX hC) ht
    have htransfer := norm_tail_le_whitened_tail ρ hC hR hm
      (C := generalCompactPaourisTailConstant) hr
    have hthreshold : (2 * generalCompactPaourisTailConstant + 1) *
        (t * Real.sqrt (n : ℝ)) = generalPaourisTailConstant * t * Real.sqrt (n : ℝ) := by
      unfold generalPaourisTailConstant
      ring
    rw [hthreshold] at htransfer
    exact htransfer.trans (by simpa only [mul_assoc] using htail)

end GaussianTilt.Paouris
