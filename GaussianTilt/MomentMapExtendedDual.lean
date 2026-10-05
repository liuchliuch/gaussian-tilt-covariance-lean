import GaussianTilt.MomentMapDualRecovery

/-! # A finite target-integrable extended dual at the source limit

The increasing compact-ball conjugates define the full nonnegative extended
dual. Monotone convergence identifies its actual target integral with the
limit of the recovered budgets; hence it is finite almost everywhere.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

def extendedDual (ψ : E n → ℝ) (y : E n) : ℝ≥0∞ :=
  ⨆ k : ℕ, ENNReal.ofReal (recoveredDual ψ k y)

lemma recoveredDual_continuous {ψ : E n → ℝ} (hψ : ∀ x, 0 ≤ ψ x) (k : ℕ) :
    Continuous (recoveredDual ψ k) :=
  (fenchel_lipschitz ⟨0, zero_mem_sourceBall k⟩ (sourceBall_norm_bound k) (fun x _ => hψ x)).continuous

lemma extendedDual_measurable {ψ : E n → ℝ} (hψ : ∀ x, 0 ≤ ψ x) : Measurable (extendedDual ψ) :=
  Measurable.iSup (fun k => (recoveredDual_continuous hψ k).measurable.ennreal_ofReal)

theorem lintegral_extendedDual_eq_budget_limit
    {K : Set (E n)} {q ψ : E n → ℝ} {R I : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqm : Measurable q) (hqi : Integrable q)
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hqs : ∀ y ∉ K, q y = 0)
    (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x)
    (hbud : Tendsto (fun k => dualBudget q (recoveredDual ψ k)) atTop (𝓝 I)) :
    (∫⁻ y, extendedDual ψ y ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) = ENNReal.ofReal I := by
  have hv (k : ℕ) := recoveredDual_admissible hq0 hqi hK hqs hψ0 hψ k
  have hm (k : ℕ) : Measurable (fun y => ENNReal.ofReal (recoveredDual ψ k y)) :=
    (recoveredDual_continuous hψ k).measurable.ennreal_ofReal
  have hmono : Monotone (fun k y => ENNReal.ofReal (recoveredDual ψ k y)) := by
    intro i j hij y
    exact ENNReal.ofReal_mono (recoveredDual_monotone hψ y hij)
  have heq (k : ℕ) : (∫⁻ y, ENNReal.ofReal (recoveredDual ψ k y)
      ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) =
      ENNReal.ofReal (dualBudget q (recoveredDual ψ k)) := by
    rw [lintegral_withDensity_eq_lintegral_mul volume hqm.ennreal_ofReal (hm k)]
    simp only [Pi.mul_apply]
    simp_rw [← ENNReal.ofReal_mul (hq0 _)]
    exact (ofReal_integral_eq_lintegral_ofReal (hv k).2.2.2.2
      (ae_of_all _ (fun y => mul_nonneg (hq0 y) ((hv k).2.2.1 y)))).symm
  change (∫⁻ y, ⨆ k : ℕ, ENNReal.ofReal (recoveredDual ψ k y)
    ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) = ENNReal.ofReal I
  rw [lintegral_iSup hm hmono]
  simp_rw [heq]
  have hmono' : Monotone (fun k => ENNReal.ofReal (dualBudget q (recoveredDual ψ k))) := by
    intro i j hij
    apply ENNReal.ofReal_mono
    exact integral_mono (hv i).2.2.2.2 (hv j).2.2.2.2 (fun y =>
      mul_le_mul_of_nonneg_left (recoveredDual_monotone hψ y hij) (hq0 y))
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono')
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hbud)

theorem extendedDual_ae_finite_of_budget_limit
    {K : Set (E n)} {q ψ : E n → ℝ} {R I : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqm : Measurable q) (hqi : Integrable q)
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hqs : ∀ y ∉ K, q y = 0)
    (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x)
    (hbud : Tendsto (fun k => dualBudget q (recoveredDual ψ k)) atTop (𝓝 I)) :
    ∀ᵐ y ∂volume.withDensity (fun y => ENNReal.ofReal (q y)), extendedDual ψ y < ⊤ := by
  apply ae_lt_top (extendedDual_measurable hψ)
  rw [lintegral_extendedDual_eq_budget_limit hq0 hqm hqi hK hqs hψ0 hψ hbud]
  exact ENNReal.ofReal_ne_top

theorem extendedDual_integral_eq_budget_limit
    {K : Set (E n)} {q ψ : E n → ℝ} {R I : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqm : Measurable q) (hqi : Integrable q)
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hqs : ∀ y ∉ K, q y = 0)
    (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x)
    (hbud : Tendsto (fun k => dualBudget q (recoveredDual ψ k)) atTop (𝓝 I)) :
    Integrable (fun y => (extendedDual ψ y).toReal)
      (volume.withDensity (fun y => ENNReal.ofReal (q y))) ∧
      (∫ y, (extendedDual ψ y).toReal
        ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) = I := by
  have hl := lintegral_extendedDual_eq_budget_limit hq0 hqm hqi hK hqs hψ0 hψ hbud
  have hfin : (∫⁻ y, extendedDual ψ y ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) ≠ ⊤ := by
    rw [hl]
    exact ENNReal.ofReal_ne_top
  have hI : 0 ≤ I := ge_of_tendsto' hbud (fun k => integral_nonneg (fun y =>
    mul_nonneg (hq0 y) ((recoveredDual_admissible hq0 hqi hK hqs hψ0 hψ k).2.2.1 y)))
  refine ⟨integrable_toReal_of_lintegral_ne_top (extendedDual_measurable hψ).aemeasurable hfin, ?_⟩
  rw [integral_toReal (extendedDual_measurable hψ).aemeasurable
    (ae_lt_top (extendedDual_measurable hψ) hfin), hl, ENNReal.toReal_ofReal hI]

/-- The direct method attains the original dual supremum at a genuine
finite convex source potential and its target-integrable extended conjugate.
No variational compactness, maximizing-sequence, or semicontinuity input is
left as a theorem parameter. -/
theorem exists_variational_source_maximizer
    {K : Set (E n)} {q : E n → ℝ} {R r c : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hqm : Measurable q) (hqi : Integrable q) (hqmass : (∫ y, q y) = 1)
    (hqs : ∀ y ∉ K, q y = 0) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y) :
    ∃ ψ : E n → ℝ, LipschitzWith R.toNNReal ψ ∧ ConvexOn ℝ univ ψ ∧ ψ 0 = 0 ∧
      (∀ x, 0 ≤ ψ x) ∧ Integrable (fun x => Real.exp (-ψ x)) ∧
      Integrable (fun y => (extendedDual ψ y).toReal)
        (volume.withDensity (fun y => ENNReal.ofReal (q y))) ∧
      Real.log (∫ x, Real.exp (-ψ x)) -
        (∫ y, (extendedDual ψ y).toReal ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) =
        sSup (dualValues K q) := by
  obtain ⟨u, ψ, M, hM, hu, hbudget, hobj, hψ, hψ0, hψc, hloc, hpoint⟩ :=
    exists_maximizing_sequence_with_source_limit hK hball hq0 hc hr hqlower
  obtain ⟨hi, hp, hZ⟩ := source_partition_tendsto_of_bounded_budget
    hK hball hq0 hc hr hM hqlower hu hbudget hψ.continuous hpoint
  have hψnonneg (x : E n) : 0 ≤ ψ x := ge_of_tendsto' (hpoint x)
    (fun k => fenchel_nonneg hK (fun y _ => (hu k).2.2.1 y)
      (hball (Metric.mem_closedBall_self hr.le)) (hu k).2.2.2.1 x)
  have hrec := recoveredDual_budget_tendsto hK hball hq0 hqi hqmass hqs hc hr hqlower
    hu hψ0 hψnonneg hi hloc hZ hobj
  obtain ⟨hdi, hdeq⟩ := extendedDual_integral_eq_budget_limit hq0 hqm hqi hK hqs hψ0 hψnonneg hrec
  refine ⟨ψ, hψ, hψc, hψ0, hψnonneg, hi, hdi, ?_⟩
  rw [hdeq]
  ring

end GaussianTilt.MomentMapCoercivity
