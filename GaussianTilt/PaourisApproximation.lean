import GaussianTilt.PaourisTruncation

/-! # Stability of the proved compact Paouris tail under actual approximation

The approximating laws need not themselves be isotropic. Their genuine
first and second moments converge, and covariance whitening is performed
inside the proof. Eventwise convergence is sufficient, with no high moments.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Matrix.Norms.L2Operator

namespace GaussianTilt.Paouris

variable {n k : ℕ}

theorem tendsto_mapped_cond_closedBall_real (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] {f : Reference.Space n → Reference.Space k} (hf : Measurable f)
    {s : Set (Reference.Space k)} (hs : MeasurableSet s) :
    Tendsto (fun j : ℕ ↦ ((cond μ (Metric.closedBall 0 (j : ℝ))).map f).real s)
      atTop (𝓝 ((μ.map f).real s)) := by
  simpa only [measureReal_def, Measure.map_apply hf hs] using
    tendsto_cond_closedBall_real μ (hs.preimage hf)

theorem norm_tail_of_compact_approximation
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (ρ : ℕ → Measure (Reference.Space n))
    (hprob : ∀ᶠ j in atTop, IsProbabilityMeasure (ρ j))
    (hc : ∀ᶠ j in atTop, Reference.compactlySupported (ρ j))
    (hl : ∀ᶠ j in atTop, Reference.logconcave (ρ j))
    (hm : Tendsto (fun j ↦ Whitening.center (ρ j)) atTop (𝓝 0))
    (hcov : Tendsto (fun j ↦ Reference.covariance (ρ j)) atTop (𝓝 1))
    (hevents : ∀ s, MeasurableSet s →
      Tendsto (fun j ↦ (ρ j).real s) atTop (𝓝 (μ.real s)))
    {t : ℝ} (ht : 1 ≤ t) :
    μ.real {x | generalPaourisTailConstant * t * Real.sqrt (n : ℝ) ≤ ‖x‖} ≤
      Real.exp (-t * Real.sqrt (n : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, Real.exp_zero]
    simpa using (measureReal_mono (μ := μ)
      (show {x : Reference.Space 0 | (0 : ℝ) ≤ ‖x‖} ⊆ univ from subset_univ _))
  · letI : NeZero n := ⟨hn⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hr : 1 ≤ t * Real.sqrt (n : ℝ) :=
      one_le_mul_of_one_le_of_one_le ht (Real.one_le_sqrt.mpr hn1)
    have hpsd : ∀ᶠ j in atTop, (Reference.covariance (ρ j)).PosSemidef := by
      filter_upwards [hprob, hc] with j hp hcompact
      letI := hp
      exact Reference.covariance_posSemidef (Whitening.compact_coordinates_memLp hcompact)
    have hpd := Whitening.eventually_posDef_of_tendsto_one hcov hpsd
    have hroot := Whitening.eventually_root_norm_le_two hcov hpsd
    have hcenter : ∀ᶠ j in atTop, ‖Whitening.center (ρ j)‖ ≤ 1 := by
      have hmn : Tendsto (fun j ↦ ‖Whitening.center (ρ j)‖) atTop (𝓝 (0 : ℝ)) := by
        simpa only [norm_zero] using hm.norm
      exact (hmn.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono
        (fun _ hj ↦ hj.le)
    apply le_of_tendsto (hevents _ (measurableSet_le measurable_const continuous_norm.measurable))
    filter_upwards [hprob, hc, hl, hpd, hroot, hcenter] with j hp hcompact hlog hC hR hm'
    letI := hp
    have hX := Whitening.compact_coordinates_memLp hcompact
    have heq : Reference.covariance (ρ j) = Whitening.covariance (ρ j) :=
      Reference.covariance_eq_covarianceMatrix hX
    rw [heq] at hC hR
    have htail := compact_isotropic_norm_tail (Whitening.law (ρ j))
      (Whitening.law_compactlySupported hcompact) (Whitening.law_logconcave hlog hC)
      (Whitening.law_isotropic hX hC) ht
    have htransfer := norm_tail_le_whitened_tail (ρ j) hC hR hm'
      (C := generalCompactPaourisTailConstant) hr
    have hthreshold : (2 * generalCompactPaourisTailConstant + 1) *
        (t * Real.sqrt (n : ℝ)) = generalPaourisTailConstant * t * Real.sqrt (n : ℝ) := by
      unfold generalPaourisTailConstant
      ring
    rw [hthreshold] at htransfer
    exact htransfer.trans (by simpa only [mul_assoc] using htail)

end GaussianTilt.Paouris
