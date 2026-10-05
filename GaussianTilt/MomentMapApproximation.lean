import Mathlib
import GaussianTilt.Reference.PaperStatements

/-!
# Constructed perturbation and truncation for moment-map approximation

These are actual probability laws, defined by adding an independent random
vector of size `1 / (k + 1)` and conditioning on the ball of radius `k + 1`.
Their normalization and convergence of polynomial-growth observables are
proved by dominated convergence. In particular, no moment-convergence or
approximation assertion is assumed.

This supplies the probabilistic truncation step of Letwin A1. Construction of
the moment potential, its Monge--Ampère regularity, smooth logconcavity of the
convolution, and affine isotropization are separate obligations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace GaussianTilt.MomentMapApproximation

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The genuine independent additive perturbation used below. -/
def perturb (k : ℕ) (p : E × E) : E := p.1 + ((k : ℝ) + 1)⁻¹ • p.2

/-- The truncation event is measured on the original product probability
space, so both the perturbation and the normalization remain explicit. -/
def truncationEvent (k : ℕ) : Set (E × E) :=
  {p | ‖perturb k p‖ < (k : ℝ) + 1}

/-- Add an independent small perturbation, restrict to an expanding ball,
normalize, and take the actual law of the resulting random vector. -/
def perturbedTruncation (μ ν : Measure E) (k : ℕ) : Measure E :=
  (cond (μ.prod ν) (truncationEvent k)).map (perturb k)

lemma continuous_perturb (k : ℕ) : Continuous (perturb (E := E) k) := by
  unfold perturb
  fun_prop

lemma measurableSet_truncationEvent (k : ℕ) : MeasurableSet (truncationEvent (E := E) k) :=
  measurableSet_lt (continuous_perturb k).norm.measurable measurable_const

lemma perturb_norm_le (k : ℕ) (p : E × E) : ‖perturb k p‖ ≤ ‖p.1‖ + ‖p.2‖ := by
  have hpos : 0 < (k : ℝ) + 1 := by positivity
  have hinv : ((k : ℝ) + 1)⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
  calc
    _ ≤ ‖p.1‖ + ‖((k : ℝ) + 1)⁻¹ • p.2‖ := norm_add_le _ _
    _ = ‖p.1‖ + ((k : ℝ) + 1)⁻¹ * ‖p.2‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    _ ≤ _ := add_le_add_left (by simpa using mul_le_mul_of_nonneg_right hinv (norm_nonneg p.2)) _

lemma tendsto_perturb (p : E × E) :
    Tendsto (fun k => perturb k p) atTop (𝓝 p.1) := by
  have hi : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  simpa only [perturb, zero_smul, add_zero] using
    (tendsto_const_nhds (x := p.1)).add (hi.smul (tendsto_const_nhds (x := p.2)))

lemma eventually_mem_truncationEvent (p : E × E) :
    ∀ᶠ k : ℕ in atTop, p ∈ truncationEvent k := by
  have ht : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_gt_atTop (‖p.1‖ + ‖p.2‖))] with k hk
  exact (perturb_norm_le k p).trans_lt hk

lemma tendsto_truncation_indicator {f : E → ℝ} (hf : Continuous f) (p : E × E) :
    Tendsto (fun k => (truncationEvent k).indicator (fun q => f (perturb k q)) p)
      atTop (𝓝 (f p.1)) := by
  apply (hf.continuousAt.tendsto.comp (tendsto_perturb p)).congr'
  filter_upwards [eventually_mem_truncationEvent p] with k hk
  simp only [indicator_of_mem hk, Function.comp_apply]

lemma integral_perturbedTruncation (μ ν : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (k : ℕ) {f : E → ℝ} (hf : Measurable f) :
    (∫ x, f x ∂perturbedTruncation μ ν k) =
      (∫ p, (truncationEvent k).indicator (fun q => f (perturb k q)) p ∂μ.prod ν) /
      (μ.prod ν (truncationEvent k)).toReal := by
  rw [perturbedTruncation, integral_map (continuous_perturb k).measurable.aemeasurable
    hf.aestronglyMeasurable, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
    smul_eq_mul, div_eq_mul_inv, mul_comm, integral_indicator (measurableSet_truncationEvent k)]

lemma tendsto_truncation_mass (μ ν : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    Tendsto (fun k => (μ.prod ν (truncationEvent k)).toReal) atTop (𝓝 1) := by
  have ht := tendsto_integral_of_dominated_convergence (μ := μ.prod ν)
    (F := fun k => (truncationEvent k).indicator (fun _ => (1 : ℝ)))
    (f := fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
    (fun k => (measurable_const.indicator (measurableSet_truncationEvent k)).aestronglyMeasurable)
    (integrable_const 1) (fun k => ae_of_all _ (fun p => by
      by_cases hp : p ∈ truncationEvent k <;> simp [hp]))
    (ae_of_all _ (fun p => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_mem_truncationEvent p] with k hk
      simp [hk]))
  simp only [integral_indicator_const _ (measurableSet_truncationEvent _), smul_eq_mul,
    mul_one, integral_const, measureReal_def] at ht
  simpa using ht

theorem eventually_perturbedTruncation_probability (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∀ᶠ k in atTop, IsProbabilityMeasure (perturbedTruncation μ ν k) := by
  filter_upwards [(tendsto_truncation_mass μ ν).eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))]
    with k hk
  have hmass : μ.prod ν (truncationEvent k) ≠ 0 := by
    intro hz
    simp [hz] at hk
  letI := cond_isProbabilityMeasure hmass
  exact Measure.isProbabilityMeasure_map (continuous_perturb k).measurable.aemeasurable

/-- Full support of the noise makes every normalization strictly positive,
not merely eventually positive. -/
theorem truncation_mass_pos (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure] (k : ℕ) :
    0 < μ.prod ν (truncationEvent k) := by
  have hslice (x : E) : 0 < ν (Prod.mk x ⁻¹' truncationEvent k) := by
    have ho : IsOpen (Prod.mk x ⁻¹' truncationEvent k) :=
      isOpen_lt ((continuous_perturb k).comp (continuous_const.prodMk continuous_id)).norm continuous_const
    apply ho.measure_pos ν
    refine ⟨(-((k : ℝ) + 1)) • x, ?_⟩
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    change ‖x + ((k : ℝ) + 1)⁻¹ • (-((k : ℝ) + 1)) • x‖ < (k : ℝ) + 1
    rw [smul_smul, mul_neg, inv_mul_cancel₀ hk, neg_one_smul, add_neg_cancel, norm_zero]
    positivity
  rw [Measure.prod_apply (measurableSet_truncationEvent k)]
  apply (lintegral_pos_iff_support
    (measurable_measure_prodMk_left (measurableSet_truncationEvent k))).mpr
  have he : Function.support (fun x => ν (Prod.mk x ⁻¹' truncationEvent k)) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hslice x).ne'
  rw [he, measure_univ]
  norm_num

theorem perturbedTruncation_probability (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure] (k : ℕ) :
    IsProbabilityMeasure (perturbedTruncation μ ν k) := by
  letI := cond_isProbabilityMeasure (truncation_mass_pos μ ν k).ne'
  exact Measure.isProbabilityMeasure_map (continuous_perturb k).measurable.aemeasurable

/-- A single, explicit integrable majorant for all perturbations and
truncations. -/
lemma truncation_indicator_bound {f : E → ℝ} {C : ℝ} {d : ℕ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ d)) (k : ℕ) (p : E × E) :
    ‖(truncationEvent k).indicator (fun q => f (perturb k q)) p‖ ≤
      C * (1 + 2 ^ (d - 1) * (‖p.1‖ ^ d + ‖p.2‖ ^ d)) := by
  by_cases hp : p ∈ truncationEvent k
  · rw [indicator_of_mem hp]
    apply (hf _).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply add_le_add_left
    exact (pow_le_pow_left₀ (norm_nonneg _) (perturb_norm_le k p) d).trans
      (add_pow_le (norm_nonneg _) (norm_nonneg _) d)
  · rw [indicator_of_notMem hp, norm_zero]
    positivity

/-- Adding independent noise tending to zero and conditioning on the
expanding balls preserves every integrable polynomial-growth observable.
The convergence is derived for the actual normalized laws defined above. -/
theorem tendsto_integral_perturbedTruncation (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {d : ℕ} (hμ : Integrable (fun x : E => ‖x‖ ^ d) μ)
    (hν : Integrable (fun x : E => ‖x‖ ^ d) ν)
    {f : E → ℝ} (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ d)) :
    Tendsto (fun k => ∫ x, f x ∂perturbedTruncation μ ν k) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hmajor : Integrable (fun p : E × E =>
      C * (1 + 2 ^ (d - 1) * (‖p.1‖ ^ d + ‖p.2‖ ^ d))) (μ.prod ν) :=
    ((integrable_const 1).add (((hμ.comp_fst ν).add (hν.comp_snd μ)).const_mul _)).const_mul C
  have ht := tendsto_integral_of_dominated_convergence
    (μ := μ.prod ν) (F := fun k => (truncationEvent k).indicator (fun p => f (perturb k p)))
    (f := fun p => f p.1)
    (fun p => C * (1 + 2 ^ (d - 1) * (‖p.1‖ ^ d + ‖p.2‖ ^ d)))
    (fun k => ((hf.comp (continuous_perturb k)).measurable.indicator
      (measurableSet_truncationEvent k)).aestronglyMeasurable)
    hmajor (fun k => ae_of_all _ (truncation_indicator_bound hC hbound k))
    (ae_of_all _ (tendsto_truncation_indicator hf))
  have hi : Integrable f μ := Integrable.mono'
    (((integrable_const 1).add hμ).const_mul C) hf.aestronglyMeasurable (ae_of_all _ hbound)
  have hfprod : (∫ p : E × E, f p.1 ∂μ.prod ν) = ∫ x, f x ∂μ := by
    rw [integral_prod _ (hi.comp_fst ν)]
    simp
  rw [hfprod] at ht
  have hd := ht.div (tendsto_truncation_mass μ ν) (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (fun k => (∫ p : E × E,
      (truncationEvent k).indicator (fun q => f (perturb k q)) p ∂μ.prod ν) /
      (μ.prod ν (truncationEvent k)).toReal) =
      (fun k => ∫ x, f x ∂perturbedTruncation μ ν k) := by
    funext k
    exact (integral_perturbedTruncation μ ν k hf.measurable).symm
  change Tendsto (fun k => (∫ p : E × E,
    (truncationEvent k).indicator (fun q => f (perturb k q)) p ∂μ.prod ν) /
    (μ.prod ν (truncationEvent k)).toReal) atTop (𝓝 ((∫ x, f x ∂μ) / 1)) at hd
  rw [heq, div_one] at hd
  exact hd

theorem perturbedTruncation_outside_closedBall (μ ν : Measure E) (k : ℕ) :
    perturbedTruncation μ ν k (Metric.closedBall 0 ((k : ℝ) + 1))ᶜ = 0 := by
  rw [perturbedTruncation, Measure.map_apply (continuous_perturb k).measurable
    Metric.isClosed_closedBall.measurableSet.compl, ProbabilityTheory.cond,
    Measure.smul_apply, Measure.restrict_apply
      ((continuous_perturb k).measurable Metric.isClosed_closedBall.measurableSet.compl)]
  have he : (perturb k ⁻¹' (Metric.closedBall (0 : E) ((k : ℝ) + 1))ᶜ) ∩
      truncationEvent k = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hnot : ¬ ‖perturb k p‖ ≤ (k : ℝ) + 1 := by simpa using hp.1
    exact hnot hp.2.le
  rw [he, measure_empty, smul_zero]

theorem perturbedTruncation_compactlySupported {n : ℕ}
    (μ ν : Measure (Reference.Space n)) (k : ℕ) :
    Reference.compactlySupported (perturbedTruncation μ ν k) :=
  ⟨Metric.closedBall 0 ((k : ℝ) + 1), isCompact_closedBall _ _,
    perturbedTruncation_outside_closedBall μ ν k⟩

end GaussianTilt.MomentMapApproximation
