import GaussianTilt.Calculus
import GaussianTilt.Reference.PaperStatements

/-!
# Bridges from genuine Gaussian-tilt calculus to the paper's definitions

The reference specification is independent of the solution. This file proves
its agreement with the compact-probability representation, rather than treating
that agreement as an assumption.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Matrix.Norms.L2Operator

namespace GaussianTilt.CompactProbability

variable {n : ℕ} (P : CompactProbability n)

lemma ae_norm_le : ∀ᵐ x ∂P.measure, ‖x‖ ≤ P.bound + 1 := by
  filter_upwards [P.ae_energy_le] with x hx
  dsimp [energy] at hx
  nlinarith [P.bound_nonneg, norm_nonneg x]

lemma reference_compactlySupported : Reference.compactlySupported P.measure := by
  refine ⟨Metric.closedBall 0 (P.bound + 1), isCompact_closedBall _ _, ?_⟩
  apply ae_iff.mp
  filter_upwards [P.ae_norm_le] with x hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using hx

/-- Compact support supplies every continuous scalar moment needed below. -/
lemma integrable_continuous {f : Point n → ℝ} (hf : Continuous f) :
    Integrable f P.measure := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Point n) (P.bound + 1)).exists_bound_of_continuousOn hf.continuousOn
  apply (MemLp.of_bound hf.aestronglyMeasurable C (p := (1 : ENNReal)) ?_).integrable le_rfl
  filter_upwards [P.ae_norm_le] with x hx
  exact hC x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)

/-- Compact support is preserved by every real Gaussian tilt. -/
lemma reference_tilt_compactlySupported (t : ℝ) :
    Reference.compactlySupported (P.tilt t) := by
  obtain ⟨K, hK, hμK⟩ := P.reference_compactlySupported
  exact ⟨K, hK, P.tilt_absolutelyContinuous t hμK⟩

/-- Every continuous scalar observable has every finite or infinite Lp moment
under a compactly supported Gaussian tilt. -/
lemma memLp_continuous_tilt {f : Point n → ℝ} (hf : Continuous f) (t : ℝ) (p : ℝ≥0∞) :
    MemLp f p (P.tilt t) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Point n) (P.bound + 1)).exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [(P.tilt_absolutelyContinuous t).ae_le P.ae_norm_le] with x hx
  exact hC x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)

lemma reference_partition (t : ℝ) : Reference.partition P.measure t = P.partition t := rfl

lemma reference_gaussianTilt (t : ℝ) : Reference.gaussianTilt P.measure t = P.tilt t := rfl

/-- The real covariance integral in the reference equals the tilt calculus entry. -/
lemma reference_covariance_entry (t : ℝ) (i j : Fin n) :
    Reference.covariance (Reference.gaussianTilt P.measure t) i j =
      P.covariance t (fun x ↦ x i) (fun x ↦ x j) := by
  simp only [Reference.covariance, P.reference_gaussianTilt, P.integral_tilt, covariance]

lemma hasDerivAt_coordinate_mean (t : ℝ) (i : Fin n) :
    HasDerivAt (fun s ↦ ∫ x, x i ∂(Reference.gaussianTilt P.measure s))
      (-P.covariance t (fun x ↦ x i) energy) t := by
  simp_rw [P.reference_gaussianTilt, P.integral_tilt]
  exact P.hasDerivAt_expectation (P.integrable_continuous (by fun_prop)) t

lemma hasDerivAt_secondMoment_entry (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s ↦ ∫ x, x i * x j ∂(Reference.gaussianTilt P.measure s))
      (-P.covariance t (fun x ↦ x i * x j) energy) t := by
  simp_rw [P.reference_gaussianTilt, P.integral_tilt]
  exact P.hasDerivAt_expectation (P.integrable_continuous (by fun_prop)) t

end GaussianTilt.CompactProbability

namespace GaussianTilt

/-- The bounded-energy representation does not narrow compactly supported
probabilities: every such measure admits it. -/
theorem exists_compactProbability_of_compactlySupported {n : ℕ}
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) :
    ∃ P : CompactProbability n, P.measure = μ := by
  obtain ⟨K, hK, hμK⟩ := hc
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hae : ∀ᵐ x ∂μ, x ∈ K := ae_iff.mpr hμK
  refine ⟨⟨μ, inferInstance, (max R 0) ^ 2, sq_nonneg _, ?_⟩, rfl⟩
  filter_upwards [hae] with x hx
  dsimp [energy]
  exact pow_le_pow_left₀ (norm_nonneg x) ((hR x hx).trans (le_max_left _ _)) 2

end GaussianTilt
