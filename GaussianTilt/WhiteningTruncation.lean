import GaussianTilt.WhiteningLimits
import GaussianTilt.ScalarLogConcaveMoments

/-! # Pure normalized compact restrictions of finite-second-moment laws

No smoothing or noise is added. The actual closed-ball restrictions converge
in every integrable scalar observable; their means and covariances converge,
and their covariance square roots are eventually uniformly bounded.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped BigOperators Matrix.Norms.L2Operator Topology ENNReal
namespace GaussianTilt.Whitening
variable {n : ℕ}

/-- Exactly the normalized restriction to the closed ball of radius `k`. -/
def ballRestriction (μ : Measure (Reference.Space n)) (k : ℕ) : Measure (Reference.Space n) :=
  ProbabilityTheory.cond μ (Metric.closedBall 0 (k : ℝ))

lemma eventually_mem_closedBall (x : Reference.Space n) :
    ∀ᶠ k : ℕ in atTop, x ∈ Metric.closedBall 0 (k : ℝ) := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖x‖)] with k hk
  simpa using hk

lemma integral_ballIndicator_tendsto {μ : Measure (Reference.Space n)}
    {f : Reference.Space n → ℝ} (hf : Integrable f μ) :
    Tendsto (fun k : ℕ ↦ ∫ x, (Metric.closedBall 0 (k : ℝ)).indicator f x ∂μ)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
    (fun k ↦ hf.aestronglyMeasurable.indicator Metric.isClosed_closedBall.measurableSet)
    hf.norm
  · intro k
    exact ae_of_all _ (fun x ↦ by
      by_cases hx : x ∈ Metric.closedBall 0 (k : ℝ) <;> simp [hx])
  · exact ae_of_all _ (fun x ↦ by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_mem_closedBall x] with k hk
      simp [hk])

lemma ballRestriction_mass_tendsto_one (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ] :
    Tendsto (fun k : ℕ ↦ (μ (Metric.closedBall 0 (k : ℝ))).toReal) atTop (𝓝 1) := by
  have h := integral_ballIndicator_tendsto (μ := μ) (integrable_const (1 : ℝ))
  simpa only [integral_indicator_const _ Metric.isClosed_closedBall.measurableSet,
    smul_eq_mul, mul_one, integral_const, measureReal_univ_eq_one, one_smul,
    measureReal_def, measure_univ, ENNReal.toReal_one] using h

lemma integral_ballRestriction (μ : Measure (Reference.Space n)) (k : ℕ)
    (f : Reference.Space n → ℝ) :
    (∫ x, f x ∂ballRestriction μ k) =
      (∫ x, (Metric.closedBall 0 (k : ℝ)).indicator f x ∂μ) /
        (μ (Metric.closedBall 0 (k : ℝ))).toReal := by
  rw [ballRestriction, ProbabilityTheory.cond, integral_smul_measure,
    ENNReal.toReal_inv, smul_eq_mul,
    integral_indicator Metric.isClosed_closedBall.measurableSet]
  ring

lemma integral_ballRestriction_tendsto {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    {f : Reference.Space n → ℝ} (hf : Integrable f μ) :
    Tendsto (fun k ↦ ∫ x, f x ∂ballRestriction μ k) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have h := (integral_ballIndicator_tendsto hf).div (ballRestriction_mass_tendsto_one μ)
    (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun k : ℕ ↦
    (∫ x, (Metric.closedBall 0 (k : ℝ)).indicator f x ∂μ) /
      (μ (Metric.closedBall 0 (k : ℝ))).toReal) atTop (𝓝 ((∫ x, f x ∂μ) / 1)) at h
  simpa only [← integral_ballRestriction, div_one] using h

lemma eventually_ballRestriction_probability (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ] :
    ∀ᶠ k in atTop, IsProbabilityMeasure (ballRestriction μ k) := by
  filter_upwards [(ballRestriction_mass_tendsto_one μ).eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))] with k hk
  have hm : μ (Metric.closedBall 0 (k : ℝ)) ≠ 0 := by
    intro hz
    simp [hz] at hk
  exact cond_isProbabilityMeasure hm

lemma ballRestriction_compactlySupported (μ : Measure (Reference.Space n)) (k : ℕ) :
    Reference.compactlySupported (ballRestriction μ k) := by
  refine ⟨Metric.closedBall 0 (k : ℝ), isCompact_closedBall _ _, ?_⟩
  rw [ballRestriction, ProbabilityTheory.cond, Measure.smul_apply,
    Measure.restrict_apply Metric.isClosed_closedBall.measurableSet.compl,
    compl_inter_self, measure_empty, smul_zero]

lemma ballRestriction_logconcave {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hl : Reference.logconcave μ) (k : ℕ)
    (hmass : μ (Metric.closedBall 0 (k : ℝ)) ≠ 0) :
    Reference.logconcave (ballRestriction μ k) := by
  obtain ⟨f, hf, hμ⟩ := hl
  let S := Metric.closedBall (0 : Reference.Space n) (k : ℝ)
  let c : ℝ := (μ S)⁻¹.toReal
  have hS : MeasurableSet S := Metric.isClosed_closedBall.measurableSet
  have hct : (μ S)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hmass
  have hc : 0 < c := ENNReal.toReal_pos
    (ENNReal.inv_ne_zero.mpr (measure_ne_top μ S)) hct
  have hg : LogConcaveMarginal.IsLogConcave (S.indicator f) :=
    ScalarLogConcaveMoments.logconcave_indicator ⟨hf.1, hf.2.2⟩ (convex_closedBall _ _)
  have hmg := hf.2.1.indicator hS
  have hlc := LinearImageDensity.logconcave_const_mul hg hc
  refine ⟨fun x ↦ c * S.indicator f x, ⟨hlc.1, measurable_const.mul hmg, hlc.2⟩, ?_⟩
  have hres : μ.restrict S = volume.withDensity (fun x ↦ ENNReal.ofReal (S.indicator f x)) := by
    have hid : (fun x ↦ ENNReal.ofReal (S.indicator f x)) =
        S.indicator (fun x ↦ ENNReal.ofReal (f x)) := by
      funext x
      by_cases hx : x ∈ S <;> simp [hx]
    rw [hid, withDensity_indicator hS, ← restrict_withDensity hS, ← hμ]
  change (μ S)⁻¹ • μ.restrict S = _
  rw [hres, ← withDensity_smul (μ S)⁻¹ hmg.ennreal_ofReal]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul hc.le]
  rw [show ENNReal.ofReal c = (μ S)⁻¹ from ENNReal.ofReal_toReal hct]

lemma eventually_ballRestriction_logconcave {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hl : Reference.logconcave μ) :
    ∀ᶠ k in atTop, Reference.logconcave (ballRestriction μ k) := by
  filter_upwards [(ballRestriction_mass_tendsto_one μ).eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))] with k hk
  apply ballRestriction_logconcave hl k
  intro hz
  simp [hz] at hk

lemma coordinates_integrable_of_norm_sq {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ) (i : Fin n) :
    Integrable (fun x : Reference.Space n ↦ x i) μ := by
  apply ((integrable_const (1 : ℝ)).add hμ).mono'
    (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i).aestronglyMeasurable
  exact ae_of_all _ (fun x ↦ by simpa only [one_mul] using coordinate_second_growth i x)

lemma coordinate_product_integrable_of_norm_sq {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ) (i j : Fin n) :
    Integrable (fun x : Reference.Space n ↦ x i * x j) μ := by
  apply ((integrable_const (1 : ℝ)).add hμ).mono' (by fun_prop)
  exact ae_of_all _ (fun x ↦ by simpa only [one_mul] using coordinate_product_second_growth i j x)

lemma meanVector_ballRestriction_tendsto (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ) :
    Tendsto (fun k ↦ meanVector (ballRestriction μ k) coordinates)
      atTop (𝓝 (meanVector μ coordinates)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact integral_ballRestriction_tendsto (coordinates_integrable_of_norm_sq hμ i)

lemma center_ballRestriction_tendsto (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ) :
    Tendsto (fun k ↦ center (ballRestriction μ k)) atTop (𝓝 (center μ)) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.continuous.tendsto _ |>.comp
    (meanVector_ballRestriction_tendsto μ hμ)

lemma reference_covariance_ballRestriction_tendsto (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ) :
    Tendsto (fun k ↦ Reference.covariance (ballRestriction μ k))
      atTop (𝓝 (Reference.covariance μ)) := by
  have hm := meanVector_ballRestriction_tendsto μ hμ
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact (integral_ballRestriction_tendsto (coordinate_product_integrable_of_norm_sq hμ i j)).sub
    ((tendsto_pi_nhds.mp hm i).mul (tendsto_pi_nhds.mp hm j))

lemma eventually_ballRestriction_covariance_posSemidef
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ] :
    ∀ᶠ k in atTop, (Reference.covariance (ballRestriction μ k)).PosSemidef := by
  filter_upwards [eventually_ballRestriction_probability μ] with k hk
  letI := hk
  exact Reference.covariance_posSemidef (compact_coordinates_memLp (ballRestriction_compactlySupported μ k))

lemma eventually_ballRestriction_covariance_posDef
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ) (hiso : Reference.isotropic μ) :
    ∀ᶠ k in atTop, (Reference.covariance (ballRestriction μ k)).PosDef := by
  apply eventually_posDef_of_tendsto_one _ (eventually_ballRestriction_covariance_posSemidef μ)
  rw [← hiso.2]
  exact reference_covariance_ballRestriction_tendsto μ hμ

lemma eventually_ballRestriction_root_norm_le_two [Nonempty (Fin n)]
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ) (hiso : Reference.isotropic μ) :
    ∀ᶠ k in atTop, ‖root (Reference.covariance (ballRestriction μ k))‖ ≤ 2 := by
  apply eventually_root_norm_le_two _ (eventually_ballRestriction_covariance_posSemidef μ)
  rw [← hiso.2]
  exact reference_covariance_ballRestriction_tendsto μ hμ

lemma eventually_ballRestriction_center_norm_le_one
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ) (hiso : Reference.isotropic μ) :
    ∀ᶠ k in atTop, ‖center (ballRestriction μ k)‖ ≤ 1 := by
  have hcenter : center μ = 0 := (center_eq_mean (coordinates_integrable_of_norm_sq hμ)).trans hiso.1
  have hm := (center_ballRestriction_tendsto μ hμ).norm
  rw [hcenter, norm_zero] at hm
  exact (hm.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono
    (fun _ h ↦ h.le)

end GaussianTilt.Whitening
