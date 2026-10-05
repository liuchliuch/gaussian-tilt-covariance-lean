import GaussianTilt.MomentMapRegularTargets

/-! # Genuine compact exhaustion of logconcave probability laws

Normalized restrictions to increasing balls converge for every integrable
observable. Logconcavity and compact support of the actual restricted
measures are proved, providing the first step for noncompact A1 reduction.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GaussianTilt.MomentMapApproximation
open LogConcaveMarginal
variable {n : ℕ}

def ballTruncation (μ : Measure (Reference.Space n)) (k : ℕ) : Measure (Reference.Space n) :=
  cond μ (Metric.ball 0 ((k : ℝ) + 1))

lemma monotone_expandingBall : Monotone (fun k : ℕ => Metric.ball (0 : Reference.Space n) ((k : ℝ) + 1)) := by
  intro i j hij
  apply Metric.ball_subset_ball
  exact_mod_cast Nat.add_le_add_right hij 1

lemma iUnion_expandingBall : (⋃ k : ℕ, Metric.ball (0 : Reference.Space n) ((k : ℝ) + 1)) = univ := by
  apply eq_univ_iff_forall.mpr
  intro x
  obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
  apply mem_iUnion.mpr
  refine ⟨k, ?_⟩
  simp only [Metric.mem_ball, dist_zero_right]
  linarith

lemma tendsto_integral_expandingBall {μ : Measure (Reference.Space n)}
    {f : Reference.Space n → ℝ} (hf : Integrable f μ) :
    Tendsto (fun k : ℕ => ∫ x in Metric.ball 0 ((k : ℝ) + 1), f x ∂μ)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hi : IntegrableOn f (⋃ k : ℕ, Metric.ball 0 ((k : ℝ) + 1)) μ := by
    rw [iUnion_expandingBall]
    exact hf.integrableOn
  have h := tendsto_setIntegral_of_monotone (fun _ => Metric.isOpen_ball.measurableSet)
    monotone_expandingBall hi
  simpa only [iUnion_expandingBall, Measure.restrict_univ] using h

theorem ballTruncation_mass_tendsto (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ] :
    Tendsto (fun k : ℕ => (μ (Metric.ball 0 ((k : ℝ) + 1))).toReal) atTop (𝓝 1) := by
  simpa [measureReal_def] using
    (tendsto_integral_expandingBall (μ := μ) (integrable_const (1 : ℝ)))

theorem eventually_ballTruncation_probability (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] : ∀ᶠ k in atTop, IsProbabilityMeasure (ballTruncation μ k) := by
  filter_upwards [(ballTruncation_mass_tendsto μ).eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))]
    with k hk
  apply cond_isProbabilityMeasure
  intro hz
  simpa [hz] using hk

lemma integral_ballTruncation (μ : Measure (Reference.Space n)) (k : ℕ)
    (f : Reference.Space n → ℝ) :
    (∫ x, f x ∂ballTruncation μ k) =
      (∫ x in Metric.ball 0 ((k : ℝ) + 1), f x ∂μ) /
        (μ (Metric.ball 0 ((k : ℝ) + 1))).toReal := by
  rw [ballTruncation, ProbabilityTheory.cond, integral_smul_measure,
    ENNReal.toReal_inv, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem tendsto_integral_ballTruncation {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    {f : Reference.Space n → ℝ} (hf : Integrable f μ) :
    Tendsto (fun k => ∫ x, f x ∂ballTruncation μ k) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have h := (tendsto_integral_expandingBall hf).div (ballTruncation_mass_tendsto μ) (by norm_num)
  simpa only [integral_ballTruncation, div_one] using h

theorem ballTruncation_compactlySupported (μ : Measure (Reference.Space n)) (k : ℕ) :
    Reference.compactlySupported (ballTruncation μ k) := by
  refine ⟨Metric.closedBall 0 ((k : ℝ) + 1), isCompact_closedBall _ _, ?_⟩
  rw [ballTruncation, ProbabilityTheory.cond, Measure.smul_apply,
    Measure.restrict_apply Metric.isClosed_closedBall.measurableSet.compl]
  have he : (Metric.closedBall (0 : Reference.Space n) ((k : ℝ) + 1))ᶜ ∩
      Metric.ball 0 ((k : ℝ) + 1) = ∅ :=
    disjoint_iff_inter_eq_empty.mp (Set.disjoint_compl_left_iff_subset.mpr Metric.ball_subset_closedBall)
  rw [he, measure_empty, smul_zero]

theorem ballTruncation_logconcave {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hl : Reference.logconcave μ) (k : ℕ) (hp : 0 < μ (Metric.ball 0 ((k : ℝ) + 1))) :
    Reference.logconcave (ballTruncation μ k) := by
  obtain ⟨f, hf, hμ⟩ := hl
  let S := Metric.ball (0 : Reference.Space n) ((k : ℝ) + 1)
  let m := (μ S).toReal
  have hmp : 0 < m := ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  let g := S.indicator (fun x => f x / m)
  have hdiv : IsLogConcave (fun x => f x / m) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      LinearImageDensity.logconcave_const_mul ⟨hf.1, hf.2.2⟩ (inv_pos.mpr hmp)
  have hg : IsLogConcave g := ScalarLogConcaveMoments.logconcave_indicator hdiv (convex_ball 0 _)
  have hgm : Measurable g := (hf.2.1.div_const m).indicator Metric.isOpen_ball.measurableSet
  refine ⟨g, ⟨hg.1, hgm, hg.2⟩, ?_⟩
  unfold ballTruncation
  rw [hμ]
  simpa only [g, m, S, hμ] using cond_withDensity_eq_indicator_div hf.1 hf.2.1
    Metric.isOpen_ball.measurableSet (hμ ▸ hp) (hμ ▸ measure_ne_top μ S)

theorem eventually_ballTruncation_logconcave {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hl : Reference.logconcave μ) : ∀ᶠ k in atTop, Reference.logconcave (ballTruncation μ k) := by
  filter_upwards [(ballTruncation_mass_tendsto μ).eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))]
    with k hk
  apply ballTruncation_logconcave hl k
  exact (ENNReal.toReal_pos_iff.mp hk).1

theorem integrable_ballTruncation {μ : Measure (Reference.Space n)} [IsFiniteMeasure μ]
    {f : Reference.Space n → ℝ} (hf : Integrable f μ) (k : ℕ)
    (hp : 0 < μ (Metric.ball 0 ((k : ℝ) + 1))) : Integrable f (ballTruncation μ k) :=
  hf.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr hp.ne')

end GaussianTilt.MomentMapApproximation
