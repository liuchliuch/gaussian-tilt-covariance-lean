import GaussianTilt.FunctionalPrekopa
import GaussianTilt.LetwinIntegration

/-!
# Removing compact cutoffs in the functional Brascamp–Lieb proof

All normalized restricted expectations converge to the original Gibbs
expectations. This includes the actual probability variance and the finite
inverse-Hessian energy. A positive Schur-complement buffer is then sent to zero.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace GaussianTilt.FunctionalBrascampLieb
open GaussianTilt.Letwin

variable {n : ℕ}

def cutoffBall (m : ℕ) : Set (Coordinate n) := Metric.closedBall 0 ((m : ℝ) + 1)

lemma cutoffBall_compact (m : ℕ) : IsCompact (cutoffBall (n := n) m) := isCompact_closedBall _ _

lemma cutoffBall_volume_pos (m : ℕ) : 0 < volume (cutoffBall (n := n) m) := by
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hball : 0 < volume (Metric.ball (0 : Coordinate n) ((m : ℝ) + 1)) :=
    Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr hpos)
  exact hball.trans_le (measure_mono Metric.ball_subset_closedBall)

lemma integral_cutoffBall_tendsto {g : Coordinate n → ℝ} (hg : Integrable g) :
    Tendsto (fun m ↦ ∫ x in cutoffBall m, g x) atTop (𝓝 (∫ x, g x)) := by
  have h := (BrascampLieb.integral_truncate_tendsto hg).comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun m ↦ ∫ x, BrascampLieb.truncate g (m + 1) x) atTop (𝓝 (∫ x, g x)) at h
  simpa only [BrascampLieb.truncate, integral_indicator Metric.isClosed_closedBall.measurableSet,
    Nat.cast_add, Nat.cast_one, cutoffBall] using h

lemma weighted_cutoffBall_tendsto {φ g : Coordinate n → ℝ} (hφ : Continuous φ)
    (hg : Integrable g (potentialMeasure φ)) :
    Tendsto (fun m ↦ ∫ x in cutoffBall m, g x * Real.exp (-φ x)) atTop
      (𝓝 (∫ x, g x ∂potentialMeasure φ)) := by
  have hgi := (integrable_potentialMeasure_iff hφ g).mp hg
  have hlim := integral_cutoffBall_tendsto hgi
  rw [integral_potentialMeasure hφ g]
  simpa only [mul_comm] using hlim

lemma integral_restrictedGibbs_tendsto {φ g : Coordinate n → ℝ} (hφ : Continuous φ)
    [IsProbabilityMeasure (potentialMeasure φ)] (hg : Integrable g (potentialMeasure φ)) :
    Tendsto (fun m ↦ ∫ x, g x ∂restrictedGibbs φ (cutoffBall m)) atTop
      (𝓝 (∫ x, g x ∂potentialMeasure φ)) := by
  have hnum := weighted_cutoffBall_tendsto hφ hg
  have hden := weighted_cutoffBall_tendsto hφ (integrable_const (1 : ℝ) : Integrable (fun _ : Coordinate n ↦ (1 : ℝ)) (potentialMeasure φ))
  simp only [one_mul, integral_const, measureReal_univ_eq_one, smul_eq_mul] at hden
  have h := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  convert h using 1
  funext m
  exact integral_restrictedGibbs hφ (cutoffBall_compact m) (cutoffBall_volume_pos m) g

lemma memLp_two_of_bounded {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} {B : ℝ} (hX : Measurable X) (hB : 0 ≤ B) (hb : ∀ x, |X x| ≤ B) : MemLp X 2 μ := by
  apply (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mpr
  apply (integrable_const (B ^ 2)).mono' (hX.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x ↦ by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := mul_le_mul (hb x) (hb x) (abs_nonneg _) hB
    nlinarith [sq_abs (X x)])

/-- Exhaustion preserves a functional variance estimate, with the actual
normalized Gibbs measures and finite-energy expectation on both sides. -/
theorem variance_le_of_restrictedGibbs_bounds {φ X A : Coordinate n → ℝ} (hφ : Continuous φ)
    [IsProbabilityMeasure (potentialMeasure φ)] (hX : Measurable X)
    (hb : ∃ B : ℝ, ∀ x, |X x| ≤ B) (hA : Integrable A (potentialMeasure φ))
    (hbound : ∀ m : ℕ, variance X (restrictedGibbs φ (cutoffBall m)) ≤
      ∫ x, A x ∂restrictedGibbs φ (cutoffBall m)) :
    variance X (potentialMeasure φ) ≤ ∫ x, A x ∂potentialMeasure φ := by
  obtain ⟨B, hB⟩ := hb
  have hB0 : 0 ≤ B := (abs_nonneg (X 0)).trans (hB 0)
  have hLp := memLp_two_of_bounded hX hB0 hB (μ := potentialMeasure φ)
  have hXi := hLp.integrable (by norm_num)
  have hX₂ := (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mp hLp
  have hlim := (integral_restrictedGibbs_tendsto hφ hX₂).sub
    ((integral_restrictedGibbs_tendsto hφ hXi).pow 2)
  rw [variance_eq_sub hLp]
  apply le_of_tendsto_of_tendsto hlim (integral_restrictedGibbs_tendsto hφ hA)
  filter_upwards [] with m
  letI : IsProbabilityMeasure (restrictedGibbs φ (cutoffBall m)) :=
    restrictedGibbs_probability hφ (cutoffBall_compact m) (cutoffBall_volume_pos m)
  have hLpm := memLp_two_of_bounded hX hB0 hB (μ := restrictedGibbs φ (cutoffBall m))
  simpa only [variance_eq_sub hLpm, Pi.pow_apply] using hbound m

/-- The complete analytic passage from local joint convexity with arbitrarily
small positive Schur buffers to the full finite-energy functional bound. -/
theorem variance_le_of_local_jointConvex_exhaustion {φ X A : Coordinate n → ℝ}
    (hφ : Continuous φ) [IsProbabilityMeasure (potentialMeasure φ)]
    (hX : Continuous X) (hA : Continuous A) (hb : ∃ B : ℝ, ∀ x, |X x| ≤ B)
    (hAi : Integrable A (potentialMeasure φ))
    (hjoint : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ConvexOn ℝ (Ioo (-δ) δ ×ˢ cutoffBall m) (jointPotential φ X (fun x ↦ A x + ε))) :
    variance X (potentialMeasure φ) ≤ ∫ x, A x ∂potentialMeasure φ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hi : Integrable (fun x ↦ A x + ε) (potentialMeasure φ) := hAi.add (integrable_const ε)
  have h := variance_le_of_restrictedGibbs_bounds hφ hX.measurable hb hi ?_
  · simpa only [integral_add hAi (integrable_const ε), integral_const, measureReal_univ_eq_one,
      smul_eq_mul, one_mul] using h
  · intro m
    obtain ⟨δ, hδ, hc⟩ := hjoint m ε hε
    exact variance_restrictedGibbs_le_of_jointConvex hφ hX (hA.add continuous_const)
      (cutoffBall_compact m) (cutoffBall_volume_pos m) hδ hc

end GaussianTilt.FunctionalBrascampLieb
