import GaussianTilt.PaourisGaussianImages

/-!
# The genuine weak-moment norm

The moment norm is constructed through the actual `Lp` space of a compact
probability law. Its triangle inequality, homogeneity, continuity, and
nondegeneracy are proved, with the integral formula supplied as a bridge.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris

variable {n : ℕ}

lemma compact_memLp_continuous (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) {f : Reference.Space n → ℝ} (hf : Continuous f)
    (p : ℝ≥0∞) : MemLp f p μ := by
  obtain ⟨K, hK, hμK⟩ := hc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  have hae : ∀ᵐ x ∂μ, x ∈ K := ae_iff.mpr hμK
  exact hae.mono fun x hx ↦ hC x hx

lemma compact_inner_memLp (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (p : ℝ≥0∞) (a : Reference.Space n) :
    MemLp (fun x ↦ ⟪a, x⟫_ℝ) p μ :=
  compact_memLp_continuous μ hc (continuous_const.inner continuous_id) p

section MomentSpace

variable (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
  (hc : Reference.compactlySupported μ) (p : ℝ) [hp : Fact (1 ≤ p)]

local instance momentExponentFact : Fact (1 ≤ ENNReal.ofReal p) :=
  ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.out⟩

include hp hc

/-- The actual linear map sending a coefficient vector to its linear
observable as an element of `Lp(μ)`. -/
def momentLinearMap : Reference.Space n →ₗ[ℝ] Lp ℝ (ENNReal.ofReal p) μ where
  toFun a := (compact_inner_memLp μ hc (ENNReal.ofReal p) a).toLp (fun x ↦ ⟪a, x⟫_ℝ)
  map_add' a b := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (compact_inner_memLp μ hc (ENNReal.ofReal p) (a + b)),
      Lp.coeFn_add ((compact_inner_memLp μ hc (ENNReal.ofReal p) a).toLp _) ((compact_inner_memLp μ hc (ENNReal.ofReal p) b).toLp _),
      MemLp.coeFn_toLp (compact_inner_memLp μ hc (ENNReal.ofReal p) a),
      MemLp.coeFn_toLp (compact_inner_memLp μ hc (ENNReal.ofReal p) b)] with x hab hsum ha hb
    simp only [Pi.add_apply] at hsum
    rw [hab, hsum, ha, hb, inner_add_left]
  map_smul' c a := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (compact_inner_memLp μ hc (ENNReal.ofReal p) (c • a)),
      Lp.coeFn_smul c ((compact_inner_memLp μ hc (ENNReal.ofReal p) a).toLp _),
      MemLp.coeFn_toLp (compact_inner_memLp μ hc (ENNReal.ofReal p) a)] with x hca hsmul ha
    simp only [Pi.smul_apply, smul_eq_mul] at hsmul
    simp only [RingHom.id_apply]
    rw [hca, hsmul, ha, real_inner_smul_left]

/-- Finite dimensionality gives continuity of the genuine moment operator. -/
def momentOperator : Reference.Space n →L[ℝ] Lp ℝ (ENNReal.ofReal p) μ :=
  LinearMap.toContinuousLinearMap (momentLinearMap μ hc p)

lemma momentLinearMap_norm_eq (a : Reference.Space n) :
    ‖momentLinearMap μ hc p a‖ = (∫ x, |⟪a, x⟫_ℝ| ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp.out
  change ‖(compact_inner_memLp μ hc (ENNReal.ofReal p) a).toLp (fun x ↦ ⟪a, x⟫_ℝ)‖ = _
  rw [Lp.norm_toLp,
    MemLp.eLpNorm_eq_integral_rpow_norm
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
      (compact_inner_memLp μ hc (ENNReal.ofReal p) a)]
  simp only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs, one_div]
  apply ENNReal.toReal_ofReal
  positivity

lemma momentLinearMap_zero_iff (hμ : μ ≪ volume) (a : Reference.Space n) :
    momentLinearMap μ hc p a = 0 ↔ a = 0 := by
  refine ⟨fun ha ↦ ?_, fun ha ↦ by rw [ha, map_zero]⟩
  by_contra hane
  have hae := MemLp.coeFn_toLp (compact_inner_memLp μ hc (ENNReal.ofReal p) a)
  change (momentLinearMap μ hc p a : Lp ℝ (ENNReal.ofReal p) μ) =ᵐ[μ]
    (fun x ↦ ⟪a, x⟫_ℝ) at hae
  rw [ha] at hae
  have hzero : ∀ᵐ x ∂μ, ⟪a, x⟫_ℝ = 0 :=
    hae.symm.trans (Lp.coeFn_zero ℝ (ENNReal.ofReal p) μ)
  let S : Submodule ℝ (Reference.Space n) := LinearMap.ker ((innerSL ℝ a).toLinearMap)
  have hproper : S ≠ ⊤ := by
    intro hS
    have haa : a ∈ S := hS ▸ Submodule.mem_top
    change ⟪a, a⟫_ℝ = 0 at haa
    exact hane (inner_self_eq_zero.mp haa)
  have hnull : μ {x | ⟪a, x⟫_ℝ = 0} = 0 :=
    hμ (Measure.addHaar_submodule volume S hproper)
  have hne : ∀ᵐ x ∂μ, ⟪a, x⟫_ℝ ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using hnull
  have hfalse : ∀ᵐ x ∂μ, False := by
    filter_upwards [hzero, hne] with x hx hnx
    exact hnx hx
  have hmass := ae_iff.mp hfalse
  simp only [not_false_eq_true, setOf_true, measure_univ, one_ne_zero] at hmass

/-- The weak `p`-th-moment norm, with definiteness justified by absolute
continuity of the probability law. -/
def momentNorm (hμ : μ ≪ volume) : AddGroupNorm (Reference.Space n) where
  toAddGroupSeminorm := (normAddGroupSeminorm (Lp ℝ (ENNReal.ofReal p) μ)).comp
    (momentLinearMap μ hc p).toAddMonoidHom
  eq_zero_of_map_eq_zero' a ha := (momentLinearMap_zero_iff μ hc p hμ a).mp (norm_eq_zero.mp ha)

lemma momentNorm_apply (hμ : μ ≪ volume) (a : Reference.Space n) :
    momentNorm μ hc p hμ a = (∫ x, |⟪a, x⟫_ℝ| ^ p ∂μ) ^ (1 / p) :=
  momentLinearMap_norm_eq μ hc p a

lemma momentNorm_continuous (hμ : μ ≪ volume) : Continuous (momentNorm μ hc p hμ) :=
  (momentOperator μ hc p).continuous.norm

lemma momentNorm_smul (hμ : μ ≪ volume) (c : ℝ) (a : Reference.Space n) :
    momentNorm μ hc p hμ (c • a) = |c| * momentNorm μ hc p hμ a := by
  change ‖momentLinearMap μ hc p (c • a)‖ = |c| * ‖momentLinearMap μ hc p a‖
  rw [map_smul, norm_smul, Real.norm_eq_abs]

lemma momentNorm_pow (hμ : μ ≪ volume) (a : Reference.Space n) :
    momentNorm μ hc p hμ a ^ p = ∫ x, |⟪a, x⟫_ℝ| ^ p ∂μ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp.out
  rw [momentNorm_apply, ← Real.rpow_mul
    (integral_nonneg fun x ↦ Real.rpow_nonneg (abs_nonneg _) _),
    one_div_mul_cancel hp0.ne', Real.rpow_one]

lemma momentNorm_le_mul_norm (hμ : μ ≪ volume) {L : ℝ}
    (_hL : 0 ≤ L)
    (hunit : ∀ a : Reference.Space n, ‖a‖ = 1 →
      (∫ x, |⟪a, x⟫_ℝ| ^ p ∂μ) ^ (1 / p) ≤ L) (a : Reference.Space n) :
    momentNorm μ hc p hμ a ≤ L * ‖a‖ := by
  by_cases ha : a = 0
  · simp [ha]
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hu := hunit (‖a‖⁻¹ • a) (norm_smul_inv_norm (𝕜 := ℝ) ha)
  rw [← momentNorm_apply μ hc p hμ, momentNorm_smul,
    abs_of_nonneg (inv_nonneg.mpr hn.le)] at hu
  have hm := mul_le_mul_of_nonneg_right hu hn.le
  convert hm using 1
  field_simp

lemma momentNorm_lipschitz (hμ : μ ≪ volume) {L : ℝ≥0}
    (hbound : ∀ a : Reference.Space n, momentNorm μ hc p hμ a ≤ (L : ℝ) * ‖a‖) :
    LipschitzWith L (momentNorm μ hc p hμ) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro a b
  change |‖momentLinearMap μ hc p a‖ - ‖momentLinearMap μ hc p b‖| ≤ (L : ℝ) * ‖a - b‖
  have h := abs_norm_sub_norm_le (momentLinearMap μ hc p a) (momentLinearMap μ hc p b)
  rw [← map_sub] at h
  exact h.trans (hbound (a - b))

lemma compact_norm_rpow_integrable : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ p) μ := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp.out
  exact (compact_memLp_continuous μ hc ((Real.continuous_rpow_const hp0).comp continuous_norm) 1).integrable le_rfl

/-- Actual joint integrability needed for the Gaussian/physical-law Fubini
identity; it follows from compact moments and Gaussian concentration. -/
lemma gaussian_inner_joint_rpow_integrable :
    Integrable (fun z : Reference.Space n × Reference.Space n ↦ |⟪z.1, z.2⟫_ℝ| ^ p)
      ((standardGaussian n).prod μ) := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp.out
  have hG : Integrable (fun a : Reference.Space n ↦ ‖a‖ ^ p) (standardGaussian n) := by
    simpa only [abs_norm] using standardGaussian_lipschitz_abs_rpow_integrable
      (lipschitzWith_one_norm : LipschitzWith 1 (fun a : Reference.Space n ↦ ‖a‖)) hp0
  apply (hG.mul_prod (compact_norm_rpow_integrable μ hc p)).mono'
    (((Real.continuous_rpow_const hp0).comp ((continuous_fst.inner continuous_snd).abs)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro z
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact (Real.rpow_le_rpow (abs_nonneg _) (abs_real_inner_le_norm z.1 z.2) hp0).trans_eq
    (Real.mul_rpow (norm_nonneg _) (norm_nonneg _))

/-- Gaussian averaging of the genuine weak-moment norm gives the strong
moment of the original law times the scalar Gaussian moment. -/
theorem momentNorm_gaussian_power_identity (hμ : μ ≪ volume) :
    (∫ a : Reference.Space n, momentNorm μ hc p hμ a ^ p ∂standardGaussian n) =
      (∫ t : Reference.Space 1, ‖t‖ ^ p ∂standardGaussian 1) *
        ∫ x : Reference.Space n, ‖x‖ ^ p ∂μ := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp.out
  simp_rw [momentNorm_pow μ hc p hμ]
  rw [integral_integral_swap (gaussian_inner_joint_rpow_integrable μ hc p)]
  have hi (x : Reference.Space n) :
      (∫ a : Reference.Space n, |⟪a, x⟫_ℝ| ^ p ∂standardGaussian n) =
      ‖x‖ ^ p * ∫ t : Reference.Space 1, ‖t‖ ^ p ∂standardGaussian 1 := by
    convert standardGaussian_inner_abs_moment x hp0 using 1
    congr 1
    funext a
    rw [real_inner_comm]
  simp_rw [hi]
  rw [integral_mul_const, mul_comm]

/-- Root form of the Gaussian strong/weak moment identity. -/
theorem momentNorm_gaussian_moment_identity (hμ : μ ≪ volume) :
    (∫ a : Reference.Space n, momentNorm μ hc p hμ a ^ p ∂standardGaussian n) ^ (1 / p) =
      (∫ t : Reference.Space 1, ‖t‖ ^ p ∂standardGaussian 1) ^ (1 / p) *
        (∫ x : Reference.Space n, ‖x‖ ^ p ∂μ) ^ (1 / p) := by
  rw [momentNorm_gaussian_power_identity]
  exact Real.mul_rpow
    (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
    (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)

end MomentSpace

end GaussianTilt.Paouris
