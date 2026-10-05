import GaussianTilt.LogConcavity
import GaussianTilt.Spectral
import GaussianTilt.Energy

/-!
# Closed original paper results, stated for unbundled measures

These results refer to the independent reference definitions. They do not
assert the unproved main upper/lower bounds.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GaussianTilt.Reference

variable {n : ℕ} (μ : Measure (Space n)) [IsProbabilityMeasure μ]
  (hcompact : compactlySupported μ)
include hcompact

/-- Positivity of the normalization in equation (5), including negative times. -/
theorem partition_positive (t : ℝ) : 0 < partition μ t := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  exact P.partition_pos t

theorem gaussianTilt_probability (t : ℝ) : IsProbabilityMeasure (gaussianTilt μ t) := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  exact P.tilt_probability t

theorem gaussianTilt_compactlySupported (t : ℝ) : compactlySupported (gaussianTilt μ t) := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  exact P.reference_tilt_compactlySupported t

theorem gaussianTilt_logconcave {t : ℝ} (ht : 0 ≤ t) (hlog : logconcave μ) :
    logconcave (gaussianTilt μ t) := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  exact P.logconcave_tilt ht hlog

/-- Lemma 2.1, equation (6), with the original integrability hypothesis. -/
theorem expectation_hasDerivAt {f : Space n → ℝ} (hf : Integrable f μ) (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ x, f x ∂(gaussianTilt μ s))
      (-observableCovariance (gaussianTilt μ t) f (fun x ↦ ‖x‖ ^ 2)) t := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  simpa only [P.reference_gaussianTilt, P.integral_tilt, observableCovariance,
    CompactProbability.covariance, energy] using P.hasDerivAt_expectation hf t

/-- Lemma 2.1, first identity in equation (7). -/
theorem logPartition_hasDerivAt (t : ℝ) :
    HasDerivAt (logPartition μ) (-(∫ x, ‖x‖ ^ 2 ∂(gaussianTilt μ t))) t := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  simpa only [logPartition, P.reference_partition, P.reference_gaussianTilt, P.integral_tilt,
    energy] using P.hasDerivAt_logPartition t

/-- Lemma 2.1, second identity in equation (7). -/
theorem logPartition_second_derivative (t : ℝ) :
    deriv (deriv (logPartition μ)) t =
      observableVariance (gaussianTilt μ t) (fun x ↦ ‖x‖ ^ 2) := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  simpa only [logPartition, P.reference_partition, P.reference_gaussianTilt, P.integral_tilt,
    observableVariance, observableCovariance, CompactProbability.variance,
    CompactProbability.covariance, energy] using P.deriv2_logPartition t

/-- Lemma 2.1, the entrywise mean derivative in equation (8). -/
theorem coordinate_mean_hasDerivAt (t : ℝ) (i : Fin n) :
    HasDerivAt (fun s ↦ ∫ x, x i ∂(gaussianTilt μ s))
      (-observableCovariance (gaussianTilt μ t) (fun x ↦ x i) (fun x ↦ ‖x‖ ^ 2)) t := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  simpa only [P.reference_gaussianTilt, P.integral_tilt, observableCovariance,
    CompactProbability.covariance, energy] using P.hasDerivAt_coordinate_mean t i

/-- Lemma 2.1, the entrywise second-moment derivative in equation (8). -/
theorem secondMoment_hasDerivAt (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s ↦ ∫ x, x i * x j ∂(gaussianTilt μ s))
      (-observableCovariance (gaussianTilt μ t) (fun x ↦ x i * x j) (fun x ↦ ‖x‖ ^ 2)) t := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  simpa only [P.reference_gaussianTilt, P.integral_tilt, observableCovariance,
    CompactProbability.covariance, energy] using P.hasDerivAt_secondMoment_entry t i j

/-- Lemma 2.1, equation (9), for actual Radon–Nikodym divergence. -/
theorem renyi_identity {r : ℝ} (_hr : 1 < r) (s t : ℝ) :
    renyi r (gaussianTilt μ s) (gaussianTilt μ t) =
      (logPartition μ (t + r * (s - t)) - r * logPartition μ s +
        (r - 1) * logPartition μ t) / (r - 1) := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  exact P.renyi_eq r s t

/-- Equation (10), actual relative entropy. -/
theorem entropy_identity (t : ℝ) :
    entropy (gaussianTilt μ t) μ = t * deriv (logPartition μ) t - logPartition μ t := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  exact P.entropy_eq_logPartition t

/-- Equation (11), relative-entropy derivative along the actual tilt path. -/
theorem entropy_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s ↦ entropy (gaussianTilt μ s) μ)
      (t * observableVariance (gaussianTilt μ t) (fun x ↦ ‖x‖ ^ 2)) t := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  simpa only [observableVariance, observableCovariance, P.reference_gaussianTilt,
    P.integral_tilt, CompactProbability.variance, CompactProbability.covariance, energy]
    using P.hasDerivAt_entropy t

/-- Lemma 3.4, the exact earlier-time Rényi comparison. -/
theorem renyi_comparison {T r : ℝ} (hT : 0 < T) (hr : 1 < r) :
    renyi r (gaussianTilt μ (T / r)) μ ≤ entropy (gaussianTilt μ T) μ := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  have h := GaussianTilt.gaussianTilt_renyi_le_entropy P hT hr
  simpa only [CompactProbability.renyi, P.tilt_zero] using h

lemma mean_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s ↦ mean (gaussianTilt μ s))
      (WithLp.toLp 2 (fun i ↦ -observableCovariance (gaussianTilt μ t)
        (fun x ↦ x i) (fun x ↦ ‖x‖ ^ 2))) t := by
  have h := hasDerivAt_pi.mpr (fun i ↦ coordinate_mean_hasDerivAt μ hcompact t i)
  have h' := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (fun i ↦ ∫ x, x i ∂gaussianTilt μ t)).comp_hasDerivAt t h
  convert h' using 1
  funext s
  ext i
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  change (∫ x, x ∂P.tilt s) i = ∫ x, x i ∂P.tilt s
  symm
  apply (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).integral_comp_comm
  obtain ⟨Q, hQ⟩ := exists_compactProbability_of_compactlySupported (P.tilt s) (P.reference_tilt_compactlySupported s)
  simpa only [hQ] using Q.integrable_id

/-- Lemma 2.1, the full second-moment matrix derivative. -/
theorem secondMomentMatrix_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s ↦ GaussianTilt.secondMomentMatrix (gaussianTilt μ s)
      (fun x : Space n ↦ fun i ↦ x i))
      (fun i j ↦ -observableCovariance (gaussianTilt μ t)
        (fun x ↦ x i * x j) (fun x ↦ ‖x‖ ^ 2)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact secondMoment_hasDerivAt μ hcompact t i j

/-- Lemma 3.4, including the exact equality and the paper's conjugate order. -/
theorem renyi_comparison_conjugate {T q : ℝ} (hT : 0 < T) (hq : 1 < q) :
    let r := q / (q - 1)
    renyi r (gaussianTilt μ (T / r)) μ =
      (logPartition μ T - r * logPartition μ (T / r)) / (r - 1) ∧
    renyi r (gaussianTilt μ (T / r)) μ ≤ entropy (gaussianTilt μ T) μ := by
  dsimp only
  have hr := GaussianTilt.conjugateOrder_gt_one hq
  refine ⟨?_, renyi_comparison μ hcompact hT hr⟩
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  have h := P.renyi_eq (q / (q - 1)) (T / (q / (q - 1))) 0
  simp only [sub_zero, zero_add, P.logPartition_zero, mul_zero, add_zero,
    mul_div_cancel₀ T (ne_of_gt (lt_trans zero_lt_one hr))] at h
  simpa only [CompactProbability.renyi, P.tilt_zero] using h

end GaussianTilt.Reference
