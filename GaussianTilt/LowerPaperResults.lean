import GaussianTilt.Isotropization
import GaussianTilt.LowerProbability

/-!
# Original lower-bound statements with their original parameters

These declarations use the actual body and normalized Lebesgue cube law. They
introduce no auxiliary analytic hypotheses or substituted exponents.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace GaussianTilt

/-- Original Lemma 4.2: the explicit raw body is a full-dimensional,
unconditional compact convex body, and its true uniform law is centered with
positive covariance of the stated two-block diagonal form. -/
theorem original4_2 : ∀ᶠ d : ℕ in atTop,
    IsCompact (rawBody d) ∧ Convex ℝ (rawBody d) ∧
    (interior (rawBody d)).Nonempty ∧
    (∀ (p : RawPoint d) (s : Fin d → Bool) (axial : Bool),
      signChange s axial p ∈ rawBody d ↔ p ∈ rawBody d) ∧
    IsProbabilityMeasure (rawUniform d (deviationScale d)) ∧
    (∀ i, ∫ p, rawCoordinate i p ∂rawUniform d (deviationScale d) = 0) ∧
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ rawCovarianceMatrix d (deviationScale d) =
      Matrix.diagonal (fun i => match i with | none => b | some _ => a)) := by
  filter_upwards [eventually_rawBody_full_geometry] with d hd
  exact ⟨hd.1, hd.2.1, ⟨0, hd.2.2.1⟩,
    fun p s axial ↦ signChange_mem_rawBodyWith_iff _ s axial p,
    hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2⟩

/-- The paper's moderate-deviation rate, with the exact power identity. -/
lemma deviationScale_sq_div {d : ℕ} (hd : 0 < d) :
    deviationScale d ^ 2 / (d : ℝ) = (d : ℝ) ^ (1 / 5 : ℝ) := by
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  rw [deviationScale, ← Real.rpow_mul_natCast hp.le]
  rw [show (3 / 5 : ℝ) * (2 : ℕ) = (6 / 5 : ℝ) by norm_num]
  conv_lhs => rhs; rw [← Real.rpow_one (d : ℝ)]
  rw [← Real.rpow_sub hp]
  norm_num

/-- Original Lemma 4.5: the global slice bound for the genuine uniform cube,
at exactly the paper's deviation and rate scales. -/
theorem original4_5 {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s) :
    LowerProbability.cubeSlice d (deviationScale d) s ≤
      Real.exp (-(8 / 9 : ℝ) * (d : ℝ) ^ (1 / 5 : ℝ) * (1 + s) ^ 2) := by
  have h := LowerProbability.cubeSlice_global_tail d (deviationScale_pos hd).le hs
  rwa [deviationScale_sq_div hd] at h

end GaussianTilt
