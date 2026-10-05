import GaussianTilt.MomentMapStrongApproximationWhitening

/-! # Positive strong convexity and the actual centered ball density -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped Topology ENNReal BigOperators Matrix.Norms.L2Operator ContDiff
namespace GaussianTilt.MomentMapApproximation
open Paouris Whitening
variable {n : ℕ}

lemma strongConvexOn_add_const {V : Reference.Space n → ℝ} {κ : ℝ}
    (hV : StrongConvexOn univ κ V) (c : ℝ) :
    StrongConvexOn univ κ (fun x => V x + c) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hV.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have habc := congrArg (fun r : ℝ => r * c) hab
  nlinarith

lemma strongConvexOn_translate {V : Reference.Space n → ℝ} {κ : ℝ}
    (hV : StrongConvexOn univ κ V) (m : Reference.Space n) :
    StrongConvexOn univ κ (fun x => V (x + m)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hV.2 (mem_univ (x + m)) (mem_univ (y + m)) ha hb hab
  have heq : a • (x + m) + b • (y + m) = (a • x + b • y) + m := by
    rw [smul_add, smul_add]
    rw [show a • x + a • m + (b • y + b • m) =
      (a • x + b • y) + (a + b) • m by rw [add_smul]; abel, hab, one_smul]
  simpa only [heq, add_sub_add_right_eq_sub] using h

lemma strongConvexOn_quadratic_tilt {V : Reference.Space n → ℝ}
    (hV : ConvexOn ℝ univ V) (δ c : ℝ) :
    StrongConvexOn univ (2 * δ) (fun x => V x + δ * ‖x‖ ^ 2 + c) := by
  apply strongConvexOn_iff_convex.mpr
  convert hV.add_const c using 1
  ext x
  simp only [Pi.add_apply]
  ring

lemma convexOn_of_strong {V : Reference.Space n → ℝ} {κ : ℝ}
    (hV : StrongConvexOn univ κ V) (hκ : 0 ≤ κ) : ConvexOn ℝ univ V :=
  hV.convexOn (fun r => by positivity)

/-- The normalized quadratic tilt has exactly the advertised potential. -/
lemma gaussianTilt_density_indicator {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) {D : Set (Reference.Space n)} (hD : MeasurableSet D)
    {V : Reference.Space n → ℝ} (hV : Continuous V)
    (hμ : μ = volume.withDensity
      (fun x => ENNReal.ofReal (D.indicator (fun y => Real.exp (-V y)) x))) (δ : ℝ) :
    Reference.gaussianTilt μ δ = volume.withDensity (fun x => ENNReal.ofReal
      (D.indicator (fun y => Real.exp (-(V y + δ * ‖y‖ ^ 2 + Real.log (Reference.partition μ δ)))) x)) := by
  have hZ := Reference.partition_positive μ hc δ
  have hweight : Measurable (fun x : Reference.Space n =>
      ENNReal.ofReal (Real.exp (-δ * ‖x‖ ^ 2) / Reference.partition μ δ)) := by fun_prop
  rw [Reference.gaussianTilt]
  nth_rw 1 [hμ]
  rw [← withDensity_mul volume
    ((hV.neg.rexp.measurable.indicator hD).ennreal_ofReal) hweight]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  by_cases hx : x ∈ D
  · simp only [indicator_of_mem hx]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    rw [show -(V x + δ * ‖x‖ ^ 2 + Real.log (Reference.partition μ δ)) =
      -V x + (-δ * ‖x‖ ^ 2) - Real.log (Reference.partition μ δ) by ring,
      Real.exp_sub, Real.exp_add, Real.exp_log hZ]
    ring
  · simp only [indicator_of_notMem hx, ENNReal.ofReal_zero, zero_mul]

/-- Every actual tilted regularization is globally smooth and has strictly
positive strong convexity, without imposing this on the original target. -/
theorem exists_strong_potential_strongTruncation
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hl : Reference.logconcave μ) (k : ℕ) :
    ∃ V : Reference.Space n → ℝ, ContDiff ℝ ∞ V ∧
      StrongConvexOn univ (2 * tiltScale k) V ∧
      strongTruncation μ k = volume.withDensity (fun x => ENNReal.ofReal
        ((Metric.ball 0 ((k : ℝ) + 1)).indicator (fun y => Real.exp (-V y)) x)) := by
  obtain ⟨V, hVs, hVc, hVlaw⟩ := exists_smooth_convex_potential_perturbedTruncation μ hc hl k
  refine ⟨fun x => V x + tiltScale k * ‖x‖ ^ 2 +
    Real.log (Reference.partition (perturbedTruncation μ (standardGaussian n) k) (tiltScale k)),
    (hVs.add (contDiff_const.mul (contDiff_norm_sq ℝ))).add contDiff_const,
    strongConvexOn_quadratic_tilt hVc _ _, ?_⟩
  exact gaussianTilt_density_indicator
    (perturbedTruncation_compactlySupported μ (standardGaussian n) k)
    Metric.isOpen_ball.measurableSet hVs.continuous hVlaw (tiltScale k)

def centeredStrongTruncation (μ : Measure (Reference.Space n)) (k : ℕ) : Measure (Reference.Space n) :=
  (strongTruncation μ k).map (fun x => x - center (strongTruncation μ k))

instance centeredStrongTruncation_probability (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (k : ℕ) : IsProbabilityMeasure (centeredStrongTruncation μ k) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

lemma centeredStrongTruncation_compactlySupported (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (k : ℕ) : Reference.compactlySupported (centeredStrongTruncation μ k) :=
  Reference.compactlySupported_map_continuous (strongTruncation_compactlySupported μ k) (by fun_prop)

lemma centeredStrongTruncation_mean (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (k : ℕ) : Reference.mean (centeredStrongTruncation μ k) = 0 := by
  have hX := compact_coordinates_memLp (strongTruncation_compactlySupported μ k)
  have hi := integrable_id_of_coordinates (fun i => (hX i).integrable (by norm_num))
  rw [Reference.mean, centeredStrongTruncation,
    integral_map (by fun_prop) (by fun_prop), integral_sub hi (integrable_const _)]
  rw [integral_const, measureReal_univ_eq_one, one_smul,
    center_eq_mean (fun i => (hX i).integrable (by norm_num))]
  exact sub_self _

/-- Centering is performed before constructing a moment source. It changes
only the center of the support ball and translates the strongly convex potential. -/
theorem exists_strong_potential_centeredStrongTruncation
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hl : Reference.logconcave μ) (k : ℕ) :
    ∃ V : Reference.Space n → ℝ, ContDiff ℝ ∞ V ∧
      StrongConvexOn univ (2 * tiltScale k) V ∧
      centeredStrongTruncation μ k = volume.withDensity (fun x => ENNReal.ofReal
        ((Metric.ball (-center (strongTruncation μ k)) ((k : ℝ) + 1)).indicator
          (fun y => Real.exp (-V y)) x)) := by
  obtain ⟨V, hVs, hVc, hVlaw⟩ := exists_strong_potential_strongTruncation μ hc hl k
  refine ⟨fun x => V (x + center (strongTruncation μ k)),
    hVs.comp (contDiff_id.add contDiff_const), strongConvexOn_translate hVc _, ?_⟩
  rw [centeredStrongTruncation]
  conv_lhs => arg 2; rw [hVlaw]
  rw [AffineDensityTransport.map_sub_withDensity]
  congr 1
  funext x
  have he : x + center (strongTruncation μ k) ∈ Metric.ball 0 ((k : ℝ) + 1) ↔
      x ∈ Metric.ball (-center (strongTruncation μ k)) ((k : ℝ) + 1) := by
    simp [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add]
  by_cases hx : x ∈ Metric.ball (-center (strongTruncation μ k)) ((k : ℝ) + 1)
  · simp only [indicator_of_mem hx, indicator_of_mem (he.mpr hx)]
  · simp only [indicator_of_notMem hx, indicator_of_notMem (mt he.mp hx)]

lemma law_strongTruncation_eq_linear_centered (μ : Measure (Reference.Space n)) (k : ℕ) :
    law (strongTruncation μ k) = (centeredStrongTruncation μ k).map
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (inverseRoot (covariance (strongTruncation μ k)))) := by
  rw [centeredStrongTruncation, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end GaussianTilt.MomentMapApproximation
