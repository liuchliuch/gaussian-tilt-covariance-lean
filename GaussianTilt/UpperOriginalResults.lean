import GaussianTilt.ActualUpperFlowVariance
import GaussianTilt.ActualUpperFlowDini
import GaussianTilt.ActualUpperFlowEndpoint
import GaussianTilt.MainAssembly
import GaussianTilt.LowerOriginalResults

/-!
# Original-scope upper-bound assembly, with its sole analytic gap exposed

The implications below have the exact measure, covariance, entropy, time,
and dimension quantifiers used in the paper. Their hypothesis is only the
isotropic quadratic-variance theorem. Until that hypothesis is discharged,
these are conditional assembly results and must not be counted as closed
original numbered upper results.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator

namespace GaussianTilt.CompactProbability

/-- Universal constants in 3.9 and 3.10, simultaneously for every actual law. -/
theorem eventually_small_precision_of_isotropic_bound
    (hL : Reference.IsotropicQuadraticVarianceBound) :
    ∃ c C κ : ℝ, 0 < c ∧ 1 ≤ C ∧ 0 < κ ∧
      ∀ᶠ n : ℕ in atTop, ∀ P : CompactProbability n,
        Reference.logconcave P.measure → Reference.isotropic P.measure →
        ∀ t ∈ Icc 0 (c * (n : ℝ) ^ (-(3 / 8 : ℝ))),
          P.entropy t ≤ κ * (n : ℝ) * t ^ 2 ∧
          ‖Reference.covariance (P.tilt t)‖ ≤ ‖P.momentMatrix t‖ ∧
          ‖P.momentMatrix t‖ ≤ C * (1 + (n : ℝ) ^ 2 * t ^ 4) := by
  obtain ⟨c, C, κ, hc, hC, hκ, hs⟩ :=
    UpperDynamics.eventually_small_precision (B := 2) Paouris.spectralTiltConstant_pos
  refine ⟨c, C, κ, hc, hC, hκ, ?_⟩
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually hs, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  intro P hl hi t ht
  have h := hn (fun s ↦ ‖P.momentMatrix s‖) P.momentHS P.entropy
    (fun s ↦ P.variance s energy) (P.scalarFlowInputs_of_isotropic_bound hL hl hi hn0) t ht
  exact ⟨h.1, P.covariance_opNorm_le_momentMatrix t, h.2⟩

end GaussianTilt.CompactProbability

namespace GaussianTilt.Reference

/-- The actual uncentered tilted second-moment matrix. -/
def tiltedSecondMoment {n : ℕ} (μ : Measure (Space n)) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  secondMomentMatrix (gaussianTilt μ t) (fun x : Space n ↦ fun i ↦ x i)

/-- The actual Hilbert–Schmidt norm, expressed spectrally by trace of the square. -/
def tiltedMomentHS {n : ℕ} (μ : Measure (Space n)) (t : ℝ) : ℝ :=
  Real.sqrt (Matrix.trace (tiltedSecondMoment μ t ^ 2))

lemma tiltedSecondMoment_compact {n : ℕ} (P : CompactProbability n) (t : ℝ) :
    tiltedSecondMoment P.measure t = P.momentMatrix t := rfl

lemma tiltedMomentHS_compact {n : ℕ} (P : CompactProbability n) (t : ℝ) :
    tiltedMomentHS P.measure t = P.momentHS t := by
  unfold tiltedMomentHS CompactProbability.momentHS
  rw [tiltedSecondMoment_compact, P.momentHSSquare_eq_trace_square]

/-- Original Lemma 3.2, conditional only on isotropic Letwin. -/
theorem original3_2_of_isotropic_bound
    (hL : IsotropicQuadraticVarianceBound) {n : ℕ} (hn : 0 < n)
    (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hc : compactlySupported μ) (hl : logconcave μ) (hi : isotropic μ)
    {t : ℝ} (ht : 0 ≤ t) :
    observableVariance (gaussianTilt μ t) (fun x ↦ ‖x‖ ^ 2) ≤ 10 * tiltedMomentHS μ t ^ 2 ∧
    |deriv (fun s ↦ Real.log (tiltedMomentHS μ s)) t| ≤ 10 * ‖tiltedSecondMoment μ t‖ ∧
    UpperDynamics.UpperRightDiniLE (fun s ↦ Real.log ‖tiltedSecondMoment μ s‖) t
      (10 * tiltedMomentHS μ t) := by
  obtain ⟨P, rfl⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported μ hc
  have h := P.differential_estimates_of_quadratic_variance hi hn
    (P.quadraticVarianceAlongTilt_of_isotropic_bound hL hl hi) ht
  simpa only [tiltedMomentHS_compact, tiltedSecondMoment_compact, P.reference_gaussianTilt,
    observableVariance, observableCovariance, P.integral_tilt, energy,
    CompactProbability.variance, CompactProbability.covariance] using h

/-- Original Corollary 3.3, conditional only on isotropic Letwin. -/
theorem original3_3_of_isotropic_bound
    (hL : IsotropicQuadraticVarianceBound) {n : ℕ} (hn : 0 < n)
    (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hc : compactlySupported μ) (hl : logconcave μ) (hi : isotropic μ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    tiltedMomentHS μ b ≤ tiltedMomentHS μ a *
      Real.exp (10 * ∫ s in a..b, ‖tiltedSecondMoment μ s‖) ∧
    ‖tiltedSecondMoment μ b‖ ≤ ‖tiltedSecondMoment μ a‖ *
      Real.exp (10 * ∫ s in a..b, tiltedMomentHS μ s) := by
  obtain ⟨P, rfl⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported μ hc
  have h := P.integrated_moments_of_quadratic_bound hi hn hab
    (fun t ht ↦ P.quadraticVarianceAlongTilt_of_isotropic_bound hL hl hi t (ha.trans ht.1))
  simpa only [tiltedMomentHS_compact, tiltedSecondMoment_compact] using h

/-- Original Lemma 3.7, conditional only on isotropic Letwin. -/
theorem original3_7_of_isotropic_bound
    (hL : IsotropicQuadraticVarianceBound) {n : ℕ} (hn : 0 < n)
    (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hc : compactlySupported μ) (hl : logconcave μ) (hi : isotropic μ)
    {a b α β : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hα : 0 < α) (hβ : 0 < β)
    (hua : ‖tiltedSecondMoment μ a‖ ≤ α) (hSa : tiltedMomentHS μ a ≤ β)
    (hαtime : 20 * α * (b - a) < Real.log 2)
    (hβtime : 20 * β * (b - a) < Real.log 2) :
    ∀ t ∈ Icc a b, ‖tiltedSecondMoment μ t‖ ≤ 2 * α ∧ tiltedMomentHS μ t ≤ 2 * β := by
  obtain ⟨P, rfl⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported μ hc
  have hSa' : P.momentHS a ≤ β := by
    simpa only [tiltedMomentHS_compact, tiltedSecondMoment_compact] using hSa
  have h := P.short_time_stability_of_quadratic_variance hi hn
    (P.quadraticVarianceAlongTilt_of_isotropic_bound hL hl hi) ha hab hα hβ hua hSa' hαtime hβtime
  simpa only [tiltedMomentHS_compact, tiltedSecondMoment_compact] using h

/-- Original Lemma 3.8, conditional only on isotropic Letwin. -/
theorem original3_8_of_isotropic_bound
    (hL : IsotropicQuadraticVarianceBound) :
    ∃ ε Cstar Csp : ℝ, 0 < ε ∧ 0 < Cstar ∧ 0 < Csp ∧
      ∀ (n : ℕ) (μ : Measure (Space n)), IsProbabilityMeasure μ →
        compactlySupported μ → logconcave μ → isotropic μ →
        ∀ T q : ℝ, 0 < T →
          Csp * max 1 (max (entropy (gaussianTilt μ T) μ) (T * Real.sqrt (n : ℝ))) ≤ q →
          q ^ 4 ≤ (n : ℝ) → T * q ≤ ε →
          ‖tiltedSecondMoment μ T‖ ≤ Cstar * q ^ 2 ∧
          tiltedMomentHS μ T ≤ Cstar * Real.sqrt (n : ℝ) := by
  obtain ⟨ε, Cstar, Csp, hε, hstar, hsp, he⟩ :=
    CompactProbability.endpoint_constants_of_isotropic_bound hL
  refine ⟨ε, Cstar, Csp, hε, hstar, hsp, ?_⟩
  intro n μ hμ hc hl hi T q hT hreq hqn hTq
  letI := hμ
  obtain ⟨P, rfl⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported μ hc
  simpa only [tiltedSecondMoment_compact, tiltedMomentHS_compact] using
    he n P hl hi T q hT hreq hqn hTq

/-- Original 3.9 and 3.10 with universal constants and all measure quantifiers. -/
theorem original3_9_and_3_10_of_isotropic_bound
    (hL : IsotropicQuadraticVarianceBound) :
    ∃ c C κ : ℝ, 0 < c ∧ 1 ≤ C ∧ 0 < κ ∧
      ∀ᶠ n : ℕ in atTop, ∀ μ : Measure (Space n), IsProbabilityMeasure μ →
        compactlySupported μ → logconcave μ → isotropic μ →
        ∀ t ∈ Icc 0 (c * (n : ℝ) ^ (-(3 / 8 : ℝ))),
          entropy (gaussianTilt μ t) μ ≤ κ * (n : ℝ) * t ^ 2 ∧
          ‖covariance (gaussianTilt μ t)‖ ≤ ‖tiltedSecondMoment μ t‖ ∧
          ‖tiltedSecondMoment μ t‖ ≤ C * (1 + (n : ℝ) ^ 2 * t ^ 4) := by
  obtain ⟨c, C, κ, hc, hC, hκ, hs⟩ :=
    CompactProbability.eventually_small_precision_of_isotropic_bound hL
  refine ⟨c, C, κ, hc, hC, hκ, ?_⟩
  filter_upwards [hs] with n hn
  intro μ hμ hcomp hl hi t ht
  letI := hμ
  obtain ⟨P, rfl⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported μ hcomp
  exact hn P hl hi t ht

/-- The exact independent upper statement follows once isotropic Letwin is proved.
All constants are uniform over both dimension and the probability law, including n=0. -/
theorem upperBound_of_isotropic_bound (hL : IsotropicQuadraticVarianceBound) : UpperBound := by
  obtain ⟨c, C, κ, hc, hC, hκ, hs⟩ :=
    CompactProbability.eventually_small_precision_of_isotropic_bound hL
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in atTop, ∀ P : CompactProbability n,
      logconcave P.measure → isotropic P.measure → ∀ t ≥ 0,
      ‖covariance (P.tilt t)‖ ≤ (2 * C) * (n : ℝ) ^ (2 / 5 : ℝ) := by
    filter_upwards [hs, hcast.eventually (UpperDynamics.eventually_optimal_scale_in_window hc),
      eventually_ge_atTop (1 : ℕ)] with n hsn hnwindow hn1
    intro P hl hi
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    exact UpperDynamics.optimize_precision hn1' hC hnwindow
      (fun t ht ↦ (hsn P hl hi t ht).2.1.trans (hsn P hl hi t ht).2.2)
      (fun t ht ↦ P.gaussianTilt_covariance_opNorm_le_inv ht hl)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  let D := max (2 * C) (max 1 (N : ℝ))
  have hD1 : 1 ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hD0 : 0 < D := by linarith
  refine ⟨D, hD0, ?_⟩
  intro n μ hμ hcomp hi hl t ht
  letI := hμ
  obtain ⟨P, rfl⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported μ hcomp
  by_cases hn0 : n = 0
  · subst n
    simpa only [Nat.cast_zero, Real.zero_rpow (by norm_num : (2 / 5 : ℝ) ≠ 0), mul_zero]
      using P.covariance_opNorm_le_dimension hi ht
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnp : 1 ≤ (n : ℝ) ^ (2 / 5 : ℝ) := Real.one_le_rpow hn1' (by norm_num)
  by_cases hnN : N ≤ n
  · exact (hN n hnN P hl hi t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hnN' : (n : ℝ) ≤ N := by exact_mod_cast (lt_of_not_ge hnN).le
    have hND : (N : ℝ) ≤ D := (le_max_right _ _).trans (le_max_right _ _)
    have hm := mul_le_mul_of_nonneg_left hnp hD0.le
    have hcrude := P.covariance_opNorm_le_dimension hi ht
    change ‖covariance (P.tilt t)‖ ≤ _
    nlinarith

/-- Both clauses of Theorem 1.1, with the remaining upper analytic input explicit. -/
theorem mainBounds_of_isotropic_bound (hL : IsotropicQuadraticVarianceBound) :
    UpperBound ∧ LowerBound :=
  ⟨upperBound_of_isotropic_bound hL, GaussianTilt.original4_1⟩

/-- The exact original supremum conclusion, conditional only on isotropic Letwin. -/
theorem sharpScale_of_isotropic_bound (hL : IsotropicQuadraticVarianceBound) : SharpScale :=
  sharpScale_of_upper_lower (upperBound_of_isotropic_bound hL) GaussianTilt.original4_1

end GaussianTilt.Reference
