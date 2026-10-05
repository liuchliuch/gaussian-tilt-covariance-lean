import GaussianTilt.PaourisApproximation
import GaussianTilt.PaourisTailMoments
import GaussianTilt.PaourisProjectionGeneral
import GaussianTilt.WhiteningProjectedTruncation

/-! # The original projected Paouris bound at noncompact scope

Truncation occurs in the source space and whitening in the intrinsic target
space. This preserves the true projection rank and requires no unproved
noncompact marginal-density regularity assertion.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Matrix.Norms.L2Operator

namespace GaussianTilt.Paouris

variable {n k : ℕ}

theorem linearImage_norm_tail (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hl : Reference.logconcave μ) (L : Reference.Space n →L[ℝ] Reference.Space k)
    (hL : Function.Surjective L) (hi : Reference.isotropic (μ.map L))
    {t : ℝ} (ht : 1 ≤ t) :
    (μ.map L).real {y | generalPaourisTailConstant * t * Real.sqrt (k : ℝ) ≤ ‖y‖} ≤
      Real.exp (-t * Real.sqrt (k : ℝ)) := by
  letI : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map L.measurable.aemeasurable
  have hX := Reference.isotropic_coordinate_memLp hi
  have hXi := fun i ↦ (hX i).integrable (by norm_num)
  have hm : Whitening.center (μ.map L) = 0 := (Whitening.center_eq_mean hXi).trans hi.1
  apply norm_tail_of_compact_approximation (μ.map L) (Whitening.projectedRestriction μ L)
    (Whitening.eventually_projectedRestriction_probability μ L)
    (Eventually.of_forall (Whitening.projectedRestriction_compactlySupported μ L))
    (Whitening.eventually_projectedRestriction_logconcave hl L hL)
    (by simpa only [hm] using Whitening.center_projectedRestriction_tendsto μ L hXi)
    (by simpa only [hi.2] using Whitening.reference_covariance_projectedRestriction_tendsto μ L hX)
    _ ht
  intro s hs
  exact tendsto_mapped_cond_closedBall_real μ L.measurable hs

theorem linearImage_norm_moment_le (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hl : Reference.logconcave μ) (L : Reference.Space n →L[ℝ] Reference.Space k)
    (hL : Function.Surjective L) (hi : Reference.isotropic (μ.map L))
    {p : ℝ} (hp : 2 ≤ p) :
    Integrable (fun y : Reference.Space k ↦ ‖y‖ ^ p) (μ.map L) ∧
      (∫ y : Reference.Space k, ‖y‖ ^ p ∂μ.map L) ^ (1 / p) ≤
        generalPaourisMomentConstant * (Real.sqrt (k : ℝ) + p) := by
  letI : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map L.measurable.aemeasurable
  by_cases hk : k = 0
  · subst k
    have hz (x : Reference.Space 0) : x = 0 := Subsingleton.elim _ _
    have hp0 : p ≠ 0 := by linarith
    simp only [hz, norm_zero, Real.zero_rpow hp0, integrable_zero, integral_zero,
      Real.zero_rpow (one_div_ne_zero hp0), Nat.cast_zero, Real.sqrt_zero, zero_add, true_and]
    exact mul_nonneg generalPaourisMomentConstant_pos.le (by linarith)
  · have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    exact moment_of_scaled_tail (μ.map L) continuous_norm.measurable (fun y ↦ norm_nonneg y)
      (Real.sqrt_pos.mpr hkpos) generalPaourisTailConstant_pos
      (fun t ht ↦ linearImage_norm_tail μ hl L hL hi ht) hp

theorem subspace_moment_le (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hl : Reference.logconcave μ) (hi : Reference.isotropic μ)
    (F : Submodule ℝ (Reference.Space n)) {p : ℝ} (hp : 2 ≤ p) :
    Integrable (fun x ↦ ‖F.starProjection x‖ ^ p) μ ∧
      (∫ x, ‖F.starProjection x‖ ^ p ∂μ) ^ (1 / p) ≤
        generalPaourisMomentConstant * (Real.sqrt (Module.finrank ℝ F : ℝ) + p) := by
  let L := projectionCoordinates F
  have hf : Measurable (fun y : Reference.Space (Module.finrank ℝ F) ↦ ‖y‖ ^ p) := by fun_prop
  obtain ⟨hI, hM⟩ := linearImage_norm_moment_le μ hl L (projectionCoordinates_surjective F)
    (projectionCoordinatesLaw_isotropic_general μ hi F) hp
  have hI' := (integrable_map_measure hf.aestronglyMeasurable L.measurable.aemeasurable).mp hI
  rw [integral_map L.measurable.aemeasurable hf.aestronglyMeasurable] at hM
  simpa only [Function.comp_def, L, projectionCoordinates_norm] using And.intro hI' hM

/-- Original theorem 2.4: every orthogonal projection, its exact algebraic
rank, and every real moment order at least two. No compactness is assumed. -/
theorem projected_moment_le (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hl : Reference.logconcave μ) (hi : Reference.isotropic μ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hH : P.IsHermitian) (hP : P * P = P)
    {p : ℝ} (hp : 2 ≤ p) :
    Integrable (fun x ↦ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ p) μ ∧
      (∫ x, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ p ∂μ) ^ (1 / p) ≤
        generalPaourisMomentConstant * (Real.sqrt (P.rank : ℝ) + p) := by
  simpa only [matrixRange_starProjection P hH hP, matrixRange_finrank] using
    subspace_moment_le μ hl hi (matrixRange P) hp

end GaussianTilt.Paouris
