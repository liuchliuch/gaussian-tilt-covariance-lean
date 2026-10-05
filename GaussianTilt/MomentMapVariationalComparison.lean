import GaussianTilt.MomentMapExtendedDual
import GaussianTilt.ConvexIntegrability

/-! # Comparison with arbitrary feasible source-dual pairs

Compact-ball conjugates recover the original dual supremum as an upper
bound for every integrable Young-feasible pair. Translation to a source
minimum removes the normalization restriction when the target is centered.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

lemma comparison_integral_density {q : E n → ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqm : Measurable q) (f : E n → ℝ) :
    (∫ y, f y ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) =
      ∫ y, q y * f y := by
  rw [integral_withDensity_eq_integral_toReal_smul hqm.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hq0 _), smul_eq_mul]

lemma comparison_integrable_density {q f : E n → ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqm : Measurable q) :
    Integrable f (volume.withDensity (fun y => ENNReal.ofReal (q y))) ↔
      Integrable (fun y => q y * f y) := by
  rw [integrable_withDensity_iff_integrable_smul' hqm.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hq0 _), smul_eq_mul]

lemma recoveredDual_budget_le_feasible {q ψ w : E n → ℝ} {K : Set (E n)} {R : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqm : Measurable q) (hqi : Integrable q)
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hqs : ∀ y ∉ K, q y = 0)
    (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x)
    (hw : Integrable w (volume.withDensity (fun y => ENNReal.ofReal (q y))))
    (hYoung : ∀ᵐ y ∂volume.withDensity (fun y => ENNReal.ofReal (q y)),
      ∀ x, ⟪x, y⟫_ℝ ≤ ψ x + w y) (k : ℕ) :
    dualBudget q (recoveredDual ψ k) ≤
      ∫ y, w y ∂volume.withDensity (fun y => ENNReal.ofReal (q y)) := by
  have hv := recoveredDual_admissible hq0 hqi hK hqs hψ0 hψ k
  rw [dualBudget, ← comparison_integral_density hq0 hqm]
  apply integral_mono_ae ((comparison_integrable_density hq0 hqm).mpr hv.2.2.2.2) hw
  filter_upwards [hYoung] with y hy
  apply csSup_le (fenchelValues_nonempty ⟨0, zero_mem_sourceBall k⟩ _ _)
  rintro a ⟨x, hx, rfl⟩
  have h := hy x
  rw [real_inner_comm] at h
  linarith

/-- Normalized finite source potentials already admit comparison with every
integrable feasible dual, with no continuity or convexity required of that dual. -/
theorem normalized_feasible_pair_le_dual_supremum
    {K : Set (E n)} {q ψ w : E n → ℝ} {R r c : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hqm : Measurable q) (hqi : Integrable q)
    (hqs : ∀ y ∉ K, q y = 0) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y)
    (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x)
    (hψi : Integrable (fun x => Real.exp (-ψ x)))
    (hw : Integrable w (volume.withDensity (fun y => ENNReal.ofReal (q y))))
    (hYoung : ∀ᵐ y ∂volume.withDensity (fun y => ENNReal.ofReal (q y)),
      ∀ x, ⟪x, y⟫_ℝ ≤ ψ x + w y) :
    Real.log (∫ x, Real.exp (-ψ x)) -
      (∫ y, w y ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) ≤
      sSup (dualValues K q) := by
  let W := ∫ y, w y ∂volume.withDensity (fun y => ENNReal.ofReal (q y))
  let S := sSup (dualValues K q)
  have hKn : K.Nonempty := ⟨0, hball (Metric.mem_closedBall_self hr.le)⟩
  have hv (k : ℕ) := recoveredDual_admissible hq0 hqi hK hqs hψ0 hψ k
  have hp (k : ℕ) := (dualPartition_polynomial_bound hK hball (hv k).1 (hv k).2.1
    (hv k).2.2.1 (hv k).2.2.2.1 hq0 (hv k).2.2.2.2 hc hr hqlower).1
  have hb (k : ℕ) : dualBudget q (recoveredDual ψ k) ≤ W :=
    recoveredDual_budget_le_feasible hq0 hqm hqi hK hqs hψ0 hψ hw hYoung k
  have hu (k : ℕ) : dualPartition K (recoveredDual ψ k) ≤ Real.exp (S + W) := by
    have h := le_csSup (dualValues_bddAbove hK hball hq0 hc hr hqlower)
      (show dualObjective K q (recoveredDual ψ k) ∈ dualValues K q from ⟨_, hv k, rfl⟩)
    have hl : Real.log (dualPartition K (recoveredDual ψ k)) ≤ S + W := by
      dsimp [dualObjective] at h
      change Real.log (dualPartition K (recoveredDual ψ k)) -
        dualBudget q (recoveredDual ψ k) ≤ S at h
      linarith [hb k]
    simpa only [Real.exp_log (hp k)] using Real.exp_le_exp.mpr hl
  have hlo (k : ℕ) : (∫ x in sourceBall k, Real.exp (-ψ x)) ≤
      dualPartition K (recoveredDual ψ k) := by
    have hiφ : Integrable (fun x => Real.exp (-fenchel K (recoveredDual ψ k) x)) := by
      by_contra hn
      have h := hp k
      rw [dualPartition, integral_undef hn] at h
      exact lt_irrefl _ h
    have hSmeas : MeasurableSet (sourceBall (n := n) k) := Metric.isClosed_closedBall.measurableSet
    rw [← integral_indicator hSmeas]
    apply integral_mono (hψi.indicator hSmeas) hiφ
    intro x
    by_cases hx : x ∈ sourceBall k
    · rw [indicator_of_mem hx]
      exact Real.exp_le_exp.mpr (neg_le_neg (fenchel_recoveredDual_le_source hKn hψ k hx))
    · rw [indicator_of_notMem hx]
      exact (Real.exp_pos _).le
  have hlowlim := tendsto_setIntegral_of_monotone
    (fun k => (show MeasurableSet (sourceBall (n := n) k) from Metric.isClosed_closedBall.measurableSet))
    sourceBall_monotone hψi.integrableOn
  simp only [iUnion_sourceBall, Measure.restrict_univ] at hlowlim
  have hlim : (∫ x, Real.exp (-ψ x)) ≤ Real.exp (S + W) :=
    le_of_tendsto' hlowlim (fun k => (hlo k).trans (hu k))
  have hlog := Real.log_le_log (integral_exp_pos hψi) hlim
  rw [Real.log_exp] at hlog
  change Real.log (∫ x, Real.exp (-ψ x)) - W ≤ S
  linarith

/-- Compact support of an integrable density supplies the first target moment. -/
lemma comparison_integrable_target_id {K : Set (E n)} {q : E n → ℝ} {R : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqm : Measurable q) (hqi : Integrable q)
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hqs : ∀ y ∉ K, q y = 0) :
    Integrable (fun y : E n => y) (volume.withDensity (fun y => ENNReal.ofReal (q y))) := by
  rw [integrable_withDensity_iff_integrable_smul' hqm.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hq0 _)]
  apply Integrable.mono' (hqi.mul_const (max R 0)) (hqm.smul measurable_id).aestronglyMeasurable
  apply ae_of_all
  intro y
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hq0 y)]
  by_cases hy : y ∈ K
  · exact mul_le_mul_of_nonneg_left ((hK y hy).trans (le_max_left R 0)) (hq0 y)
  · rw [hqs y hy]
    simp

/-- Every finite continuous convex Young-feasible source-dual pair is bounded
by the actual dual supremum. Centering makes source translations cost-free. -/
theorem feasible_pair_le_dual_supremum
    {K : Set (E n)} {q χ w : E n → ℝ} {R r c : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hqm : Measurable q) (hqi : Integrable q)
    (hqs : ∀ y ∉ K, q y = 0) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y)
    [IsProbabilityMeasure (volume.withDensity (fun y => ENNReal.ofReal (q y)))]
    (hmean : (∫ y : E n, y ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) = 0)
    (hχ : Continuous χ) (hχc : ConvexOn ℝ univ χ)
    (hχi : Integrable (fun x => Real.exp (-χ x)))
    (hw : Integrable w (volume.withDensity (fun y => ENNReal.ofReal (q y))))
    (hYoung : ∀ᵐ y ∂volume.withDensity (fun y => ENNReal.ofReal (q y)),
      ∀ x, ⟪x, y⟫_ℝ ≤ χ x + w y) :
    Real.log (∫ x, Real.exp (-χ x)) -
      (∫ y, w y ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) ≤
      sSup (dualValues K q) := by
  obtain ⟨x₀, hmin⟩ := ConvexIntegrability.convexPotential_attains_minimum hχ hχc hχi
  let m := χ x₀
  let ψ := fun x => χ (x + x₀) - m
  let v := fun y => w y + m - ⟪x₀, y⟫_ℝ
  have hψ0 : ψ 0 = 0 := by simp [ψ, m]
  have hψ : ∀ x, 0 ≤ ψ x := fun x => sub_nonneg.mpr (hmin (x + x₀))
  have hexp (x : E n) : Real.exp (-ψ x) = Real.exp m * Real.exp (-χ (x + x₀)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [ψ]
    ring
  have hψi : Integrable (fun x => Real.exp (-ψ x)) := by
    simp_rw [hexp]
    exact (hχi.comp_add_right x₀).const_mul (Real.exp m)
  have hid := comparison_integrable_target_id hq0 hqm hqi hK hqs
  have hinner : Integrable (fun y => ⟪x₀, y⟫_ℝ)
      (volume.withDensity (fun y => ENNReal.ofReal (q y))) := hid.const_inner x₀
  have hv : Integrable v (volume.withDensity (fun y => ENNReal.ofReal (q y))) :=
    (hw.add (integrable_const m)).sub hinner
  have hYoung' : ∀ᵐ y ∂volume.withDensity (fun y => ENNReal.ofReal (q y)),
      ∀ x, ⟪x, y⟫_ℝ ≤ ψ x + v y := by
    filter_upwards [hYoung] with y hy
    intro x
    have h := hy (x + x₀)
    rw [inner_add_left] at h
    dsimp [ψ, v]
    linarith
  have hcomp := normalized_feasible_pair_le_dual_supremum hK hball hq0 hqm hqi hqs hc hr
    hqlower hψ0 hψ hψi hv hYoung'
  have hpart : (∫ x, Real.exp (-ψ x)) = Real.exp m * (∫ x, Real.exp (-χ x)) := by
    simp_rw [hexp]
    rw [integral_const_mul, integral_add_right_eq_self (fun x => Real.exp (-χ x)) x₀]
  have hbudget : (∫ y, v y ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) =
      (∫ y, w y ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) + m := by
    change (∫ y, (w y + m) - ⟪x₀, y⟫_ℝ
      ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) = _
    have hadd : Integrable (fun y => w y + m)
        (volume.withDensity (fun y => ENNReal.ofReal (q y))) := hw.add (integrable_const m)
    rw [integral_sub hadd hinner, integral_add hw (integrable_const m),
      integral_inner hid x₀, hmean]
    simp
  rw [hpart, hbudget, Real.log_mul (Real.exp_pos m).ne' (integral_exp_pos hχi).ne',
    Real.log_exp] at hcomp
  linarith

end GaussianTilt.MomentMapCoercivity
