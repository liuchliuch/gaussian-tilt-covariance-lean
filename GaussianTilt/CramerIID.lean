import GaussianTilt.CramerFinite

/-! # Cramér–Petrov normalization and arbitrary iid sequences

This module transfers the proved finite relative estimate from standardized
convolution laws to the original iid sequence, its actual variance and the
left-tail orientation of Theorem 4.3.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal Topology
namespace GaussianTilt.CramerIID
open CramerAnalytic StandardizedTilt SmoothComparison GaussianLaplace CramerFinite TiltedCubeComparison

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The left-tail normalization of one real random variable. -/
def normalizedLaw (μ : Measure Ω) (Y : Ω → ℝ) (σ : ℝ) : Measure ℝ :=
  μ.map (fun ω ↦ -Y ω / σ)

lemma normalized_probability {Y : Ω → ℝ} (hY : Measurable Y) (σ : ℝ) :
    IsProbabilityMeasure (normalizedLaw μ Y σ) :=
  Measure.isProbabilityMeasure_map (hY.neg.div_const σ).aemeasurable

lemma normalized_cramer {Y : Ω → ℝ} (hY : Measurable Y)
    (hC : 0 ∈ interior (integrableExpSet Y μ)) (σ : ℝ) :
    0 ∈ interior (integrableExpSet id (normalizedLaw μ Y σ)) := by
  haveI := normalized_probability (μ := μ) hY σ
  have hM : mgf id (normalizedLaw μ Y σ) = mgf (fun ω ↦ -Y ω / σ) μ :=
    mgf_id_map (hY.neg.div_const σ).aemeasurable
  rw [integrableExpSet_eq_of_mgf hM]
  have h := cramer_affine hC (-σ⁻¹) 0
  convert h using 1
  congr 2
  funext ω
  ring

lemma normalized_standard {Y : Ω → ℝ} (hY : Measurable Y)
    (hmean : ∫ ω, Y ω ∂μ = 0) {σ : ℝ} (hσ : 0 < σ)
    (hvar : variance Y μ = σ ^ 2) (hC : 0 ∈ interior (integrableExpSet Y μ)) :
    StandardCramer (normalizedLaw μ Y σ) := by
  haveI := normalized_probability (μ := μ) hY σ
  constructor
  · rw [normalizedLaw, integral_map (hY.neg.div_const σ).aemeasurable (by fun_prop),
      integral_div, integral_neg, hmean]
    simp
  · rw [normalizedLaw, variance_id_map (hY.neg.div_const σ).aemeasurable]
    have heq : (fun ω ↦ -Y ω / σ) = fun ω ↦ (-σ⁻¹) * Y ω := by funext ω; ring
    rw [heq, variance_mul, hvar]
    field_simp
  · exact normalized_cramer hY hC σ

/-- The normalized iid sum has exactly the convolution law used in the
finite theorem. Independence and identical distribution are both discharged. -/
theorem normalized_sum_map (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hInd : iIndepFun Y μ) (hIdent : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hC : 0 ∈ interior (integrableExpSet (Y 0) μ)) (σ : ℝ) (n : ℕ) :
    μ.map (fun ω ↦ ∑ i ∈ Finset.range n, -Y i ω / σ) =
      sumLaw (normalizedLaw μ (Y 0) σ) n := by
  haveI := normalized_probability (μ := μ) (hY 0) σ
  let Z : ℕ → Ω → ℝ := fun i ω ↦ -Y i ω / σ
  let S : Ω → ℝ := fun ω ↦ ∑ i ∈ Finset.range n, Z i ω
  have hZ (i : ℕ) : Measurable (Z i) := (hY i).neg.div_const σ
  have hS : Measurable S := Finset.measurable_sum _ (fun i _ ↦ hZ i)
  have hZi : iIndepFun Z μ := hInd.comp (fun _ x ↦ -x / σ) (fun _ ↦ by fun_prop)
  have hident (i : ℕ) : IdentDistrib (Z i) (Z 0) μ μ :=
    (hIdent i).comp (show Measurable (fun x : ℝ ↦ -x / σ) by fun_prop)
  have hM : mgf S μ = mgf id (sumLaw (normalizedLaw μ (Y 0) σ) n) := by
    funext u
    have heq : S = ∑ i ∈ Finset.range n, Z i := by funext ω; simp [S]
    rw [heq, hZi.mgf_sum hZ, mgf_sumLaw]
    have he (i : ℕ) : mgf (Z i) μ u = mgf (Z 0) μ u :=
      congrFun (mgf_congr_identDistrib (hident i)) u
    simp_rw [he]
    simp only [Finset.prod_const, Finset.card_range]
    rw [normalizedLaw, mgf_id_map (hZ 0).aemeasurable]
  have h0 : 0 ∈ interior (integrableExpSet S μ) := by
    rw [integrableExpSet_eq_of_mgf hM]
    exact interior_integrableExpSet_sumLaw (normalized_cramer (hY 0) hC σ) n
  have hh := map_eq_of_mgf hS.aemeasurable aemeasurable_id h0 hM
  simpa only [Measure.map_id] using hh

lemma iid_left_tail_eq (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hInd : iIndepFun Y μ) (hIdent : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hC : 0 ∈ interior (integrableExpSet (Y 0) μ)) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) (z : ℝ) :
    μ.real {ω | (∑ i ∈ Finset.range n, Y i ω) ≤ -σ * Real.sqrt n * z} =
      (sumLaw (normalizedLaw μ (Y 0) σ) n).real {x | Real.sqrt n * z ≤ x} := by
  rw [← normalized_sum_map Y hY hInd hIdent hC σ n,
    map_measureReal_apply
      (show Measurable (fun ω ↦ ∑ i ∈ Finset.range n, -Y i ω / σ) from
        Finset.measurable_sum _ (fun i _ ↦ (hY i).neg.div_const σ))
      (show MeasurableSet {x : ℝ | Real.sqrt n * z ≤ x} from measurableSet_Ici)]
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage, ← Finset.sum_div, Finset.sum_neg_distrib]
  rw [le_div_iff₀ hσ]
  constructor <;> intro h <;> nlinarith

/-- General finite iid Cramér–Petrov estimate, at the exact normalization and
left-tail orientation stated in the paper. -/
theorem iid_cramer_finite_relative_bound (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hInd : iIndepFun Y μ) (hIdent : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hmean : ∫ ω, Y 0 ω ∂μ = 0) {σ : ℝ} (hσ : 0 < σ)
    (hvar : variance (Y 0) μ = σ ^ 2) (hC : 0 ∈ interior (integrableExpSet (Y 0) μ)) :
    ∃ A κ : ℝ, 0 < A ∧ 0 < κ ∧ ∀ (n : ℕ) (z : ℝ), 0 < n → 0 ≤ z → z / Real.sqrt n ≤ κ →
      |μ.real {ω | (∑ i ∈ Finset.range n, Y i ω) ≤ -σ * Real.sqrt n * z} / normalTail z - 1| ≤
        Real.exp (A * z ^ 3 / Real.sqrt n) *
          (1 + A * (1 + z) * (z ^ 2 / Real.sqrt n + (n : ℝ) ^ (-(1 / 5 : ℝ)))) - 1 := by
  haveI := normalized_probability (μ := μ) (hY 0) σ
  obtain ⟨A, κ, hA, hκ, hb⟩ := cramer_finite_relative_bound (normalized_standard (hY 0) hmean hσ hvar hC)
  refine ⟨A, κ, hA, hκ, ?_⟩
  intro n z hn hz hsmall
  rw [iid_left_tail_eq Y hY hInd hIdent hC hσ n z]
  exact hb n z hn hz hsmall

end GaussianTilt.CramerIID
