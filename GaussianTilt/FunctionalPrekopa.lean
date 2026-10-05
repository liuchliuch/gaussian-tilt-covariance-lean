import GaussianTilt.FunctionalBrascampCalculus
import GaussianTilt.ExtendedPotential
import GaussianTilt.BlockPrekopa

/-!
# Compact Gibbs perturbations for functional Brascamp–Lieb

This module translates convexity of an actual joint potential into the
log-partition criterion, using the constructed Prékopa marginal theorem.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace GaussianTilt.FunctionalBrascampLieb
open GaussianTilt.LogConcaveMarginal

lemma logconcave_exp_neg_indicator {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {φ : E → ℝ} {S : Set E} (hc : ConvexOn ℝ S φ) :
    IsLogConcave (S.indicator (fun x ↦ Real.exp (-φ x))) := by
  classical
  have hn : ∀ x, 0 ≤ S.indicator (fun x ↦ Real.exp (-φ x)) x := by
    intro x
    by_cases hx : x ∈ S <;> simp [hx, Real.exp_nonneg]
  refine ⟨hn, ?_⟩
  intro x y α β hα hβ hαβ
  by_cases hα0 : α = 0
  · have hβ1 : β = 1 := by linarith
    simp [hα0, hβ1]
  by_cases hβ0 : β = 0
  · have hα1 : α = 1 := by linarith
    simp [hβ0, hα1]
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · rw [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem (hc.1 hx hy hα hβ hαβ),
        ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := hc.2 hx hy hα hβ hαβ
      simp only [smul_eq_mul] at h
      nlinarith
    · simpa only [indicator_of_notMem hy, Real.zero_rpow hβ0, mul_zero] using hn (α • x + β • y)
  · simpa only [indicator_of_notMem hx, Real.zero_rpow hα0, zero_mul] using hn (α • x + β • y)

/-- The joint potential used by the infinitesimal Prékopa proof. -/
def jointPotential {E : Type*} (φ X A : E → ℝ) (p : ℝ × E) : ℝ :=
  φ p.2 - p.1 * X p.2 + p.1 ^ 2 / 2 * A p.2

def jointDensity {E : Type*} (φ X A : E → ℝ) (K : Set E) (δ : ℝ) : ℝ × E → ℝ :=
  (Ioo (-δ) δ ×ˢ K).indicator (fun p ↦ Real.exp (-jointPotential φ X A p))

lemma jointDensity_slice {E : Type*} (φ X A : E → ℝ) (K : Set E) {δ t : ℝ}
    (ht : t ∈ Ioo (-δ) δ) :
    (fun x ↦ jointDensity φ X A K δ (t, x)) =
      K.indicator (fun x ↦ Real.exp (-φ x) * perturbWeight X A t x) := by
  funext x
  by_cases hx : x ∈ K
  · simp only [jointDensity, mem_prod, ht, hx, and_self, indicator_of_mem, jointPotential,
      perturbWeight]
    rw [← Real.exp_add]
    congr 1
    ring
  · simp [jointDensity, hx]

lemma jointDensity_logconcave {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {φ X A : E → ℝ} {K : Set E} {δ : ℝ}
    (hc : ConvexOn ℝ (Ioo (-δ) δ ×ˢ K) (jointPotential φ X A)) :
    IsLogConcave (jointDensity φ X A K δ) := logconcave_exp_neg_indicator hc

section Coordinate
variable {n : ℕ}
abbrev Coordinate (n : ℕ) := Fin n → ℝ

def restrictedGibbs (φ : (Coordinate n) → ℝ) (K : Set (Coordinate n)) : Measure (Coordinate n) :=
  ExtendedPotential.normalizedLaw (fun x ↦ (φ x : EReal)) (volume.restrict K)

def restrictedMass (φ : (Coordinate n) → ℝ) (K : Set (Coordinate n)) : ℝ :=
  ∫ x in K, Real.exp (-φ x)

lemma finite_density_eq (φ : (Coordinate n) → ℝ) :
    ExtendedPotential.density (fun x ↦ (φ x : EReal)) = fun x ↦ Real.exp (-φ x) := by
  funext x
  exact ExtendedPotential.density_of_coe rfl

lemma restrictedMass_pos {φ : (Coordinate n) → ℝ} (hφ : Continuous φ) {K : Set (Coordinate n)}
    (hK : IsCompact K) (hKpos : 0 < volume K) : 0 < restrictedMass φ K := by
  have hne : volume.restrict K ≠ (0 : Measure (Coordinate n)) := by
    intro he
    have h := congrArg (fun μ : Measure (Coordinate n) ↦ μ univ) he
    simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter, Measure.coe_zero, Pi.zero_apply] at h
    exact hKpos.ne' h
  letI : NeZero (volume.restrict K) := ⟨hne⟩
  exact integral_exp_pos (ContinuousOn.integrableOn_compact hK (Real.continuous_exp.comp hφ.neg).continuousOn)

lemma restrictedGibbs_probability {φ : (Coordinate n) → ℝ} (hφ : Continuous φ) {K : Set (Coordinate n)}
    (hK : IsCompact K) (hKpos : 0 < volume K) : IsProbabilityMeasure (restrictedGibbs φ K) := by
  apply ExtendedPotential.normalizedLaw_probability
  · rw [finite_density_eq]
    fun_prop
  · rw [finite_density_eq]
    exact ContinuousOn.integrableOn_compact hK (Real.continuous_exp.comp hφ.neg).continuousOn
  · rw [finite_density_eq]
    exact restrictedMass_pos hφ hK hKpos

lemma integral_restrictedGibbs {φ : (Coordinate n) → ℝ} (hφ : Continuous φ) {K : Set (Coordinate n)}
    (hK : IsCompact K) (hKpos : 0 < volume K) (g : (Coordinate n) → ℝ) :
    (∫ x, g x ∂restrictedGibbs φ K) = (∫ x in K, g x * Real.exp (-φ x)) / restrictedMass φ K := by
  have hm : Measurable (ExtendedPotential.density (fun x ↦ (φ x : EReal))) := by rw [finite_density_eq]; fun_prop
  have hZ : 0 < ∫ x in K, ExtendedPotential.density (fun x ↦ (φ x : EReal)) x := by
    rw [finite_density_eq]
    exact restrictedMass_pos hφ hK hKpos
  have he := ExtendedPotential.integral_normalizedLaw hm hZ g
  simpa only [finite_density_eq] using he

lemma restrictedGibbs_ae_mem {φ : (Coordinate n) → ℝ} {K : Set (Coordinate n)} (hK : MeasurableSet K) :
    ∀ᵐ x ∂restrictedGibbs φ K, x ∈ K :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hK)

lemma restrictedGibbs_observables_bounded {φ X A : (Coordinate n) → ℝ}
    {K : Set (Coordinate n)} (hK : IsCompact K) (hX : Continuous X) (hA : Continuous A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂restrictedGibbs φ K, |X x| ≤ B ∧ |A x| ≤ B := by
  obtain ⟨B₁, h₁⟩ := hK.exists_bound_of_continuousOn hX.continuousOn
  obtain ⟨B₂, h₂⟩ := hK.exists_bound_of_continuousOn hA.continuousOn
  refine ⟨max 0 (max B₁ B₂), le_max_left _ _, ?_⟩
  filter_upwards [restrictedGibbs_ae_mem (φ := φ) hK.measurableSet] with x hx
  constructor
  · exact (h₁ x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h₂ x hx).trans ((le_max_right _ _).trans (le_max_right _ _))

lemma jointDensity_integral {φ X A : (Coordinate n) → ℝ} {K : Set (Coordinate n)} {δ t : ℝ}
    (hK : MeasurableSet K) (ht : t ∈ Ioo (-δ) δ) :
    (∫ x : (Coordinate n), jointDensity φ X A K δ (t, x)) =
      ∫ x in K, Real.exp (-φ x) * perturbWeight X A t x := by
  rw [jointDensity_slice φ X A K ht, integral_indicator hK]

lemma jointDensity_integral_eq_partition {φ X A : (Coordinate n) → ℝ}
    (hφ : Continuous φ) {K : Set (Coordinate n)} (hK : IsCompact K) (hKpos : 0 < volume K)
    {δ t : ℝ} (ht : t ∈ Ioo (-δ) δ) :
    (∫ x : (Coordinate n), jointDensity φ X A K δ (t, x)) =
      restrictedMass φ K * partition (μ := restrictedGibbs φ K) X A t := by
  rw [jointDensity_integral hK.measurableSet ht, partition, integral_restrictedGibbs hφ hK hKpos]
  rw [mul_div_cancel₀ _ (restrictedMass_pos hφ hK hKpos).ne']
  congr 1
  funext x
  ring


/-- Infinitesimal Prékopa on an actual compact Gibbs law. The joint convexity
hypothesis is the one discharged by the Hessian Schur-complement argument. -/
theorem variance_restrictedGibbs_le_of_jointConvex {φ X A : Coordinate n → ℝ}
    (hφ : Continuous φ) (hX : Continuous X) (hA : Continuous A)
    {K : Set (Coordinate n)} (hK : IsCompact K) (hKpos : 0 < volume K)
    {δ : ℝ} (hδ : 0 < δ)
    (hc : ConvexOn ℝ (Ioo (-δ) δ ×ˢ K) (jointPotential φ X A)) :
    variance X (restrictedGibbs φ K) ≤ ∫ x, A x ∂restrictedGibbs φ K := by
  letI : IsProbabilityMeasure (restrictedGibbs φ K) := restrictedGibbs_probability hφ hK hKpos
  obtain ⟨B, hB, hb⟩ := restrictedGibbs_observables_bounded (φ := φ) hK hX hA
  have hjm : Measurable (jointDensity φ X A K δ) := by
    apply Measurable.indicator ?_ (measurableSet_Ioo.prod hK.measurableSet)
    have hcont : Continuous (fun p : ℝ × Coordinate n ↦ Real.exp (-jointPotential φ X A p)) := by
      unfold jointPotential
      fun_prop
    exact hcont.measurable
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn : ContinuousOn (fun x : Coordinate n ↦ x) K)
  have hsupport : ∀ t x, R < ‖x‖ → jointDensity φ X A K δ (t, x) = 0 := by
    intro t x hx
    have hxK : x ∉ K := fun h ↦ (not_lt_of_ge (hR x h)) hx
    simp [jointDensity, hxK]
  have hMarginal := (BlockPrekopa.logconcave_marginal_and_fibres (jointDensity_logconcave hc) hjm hsupport).1
  have hZ := restrictedMass_pos hφ hK hKpos
  have hP : ∀ t, 0 < partition (μ := restrictedGibbs φ K) X A t :=
    partition_pos hX.measurable hA.measurable hB hb
  have hMpos : ∀ t ∈ Ioo (-δ) δ, 0 < ∫ x : Coordinate n, jointDensity φ X A K δ (t, x) := by
    intro t ht
    rw [jointDensity_integral_eq_partition hφ hK hKpos ht]
    exact mul_pos hZ (hP t)
  have hcM := convexOn_neg_log hMarginal (convex_Ioo (-δ) δ) hMpos
  have hcP : ConvexOn ℝ (Ioo (-δ) δ) (fun t ↦ -Real.log (partition (μ := restrictedGibbs φ K) X A t)) := by
    apply (hcM.add_const (Real.log (restrictedMass φ K))).congr
    intro t ht
    change -Real.log (∫ x : Coordinate n, jointDensity φ X A K δ (t, x)) + Real.log (restrictedMass φ K) = _
    rw [jointDensity_integral_eq_partition hφ hK hKpos ht, Real.log_mul hZ.ne' (hP t).ne']
    ring
  exact variance_le_of_convex_negLogPartition hX.measurable hA.measurable hB hb hδ hcP

end Coordinate
end GaussianTilt.FunctionalBrascampLieb
