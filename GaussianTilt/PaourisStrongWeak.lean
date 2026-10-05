import GaussianTilt.PaourisMomentNorm
import GaussianTilt.GaussianLowerMoments

/-!
# Analytic assembly of the Paouris strong/weak moment bound

Gaussian concentration, the proved Gordon theorem, and actual Gaussian
matrix-image/Fubini identities are combined here. The logconcave image step
is exposed separately as a small-direction hypothesis until its density
transport bridge is supplied; no Paouris tail or moment estimate is assumed.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris

variable {n q : ℕ}

lemma gordon_matrix_inf_lipschitz [NeZero q] (P : AddGroupNorm (Reference.Space n))
    (hP : ∀ (c : ℝ) x, P (c • x) = |c| * P x)
    {L : ℝ≥0} (hbound : ∀ x, P x ≤ (L : ℝ) * ‖x‖) :
    LipschitzWith L (fun W : Reference.Space (n * q) ↦ ⨅ t : UnitSphere q, P (gaussianMatrixAction W t)) := by
  letI : Nonempty (normPolar P) := (normPolar_nonempty P).to_subtype
  let a : UnitSphere q → normPolar P → Reference.Space (n * q) := fun t z ↦ tensorVector z t
  have ha : ∀ t z, ‖a t z‖ ≤ L := by
    intro t z
    change ‖tensorVector (z : Reference.Space n) (t : Reference.Space q)‖ ≤ L
    rw [tensorVector_norm, unitSphere_norm, mul_one]
    exact normPolar_norm_le P L.coe_nonneg hbound z.property
  have h := processMinMax_lipschitz a ha
  have heq : processMinMax a = (fun W : Reference.Space (n * q) ↦
      ⨅ t : UnitSphere q, P (gaussianMatrixAction W t)) := by
    funext W
    unfold processMinMax
    simp only [a, tensorVector_inner_matrixAction]
    simp_rw [normPolar_support_eq P hP hbound]
  rwa [heq] at h

lemma gordon_matrix_inf_integrable [NeZero q] (P : AddGroupNorm (Reference.Space n))
    (hP : ∀ (c : ℝ) x, P (c • x) = |c| * P x)
    {L : ℝ≥0} (hbound : ∀ x, P x ≤ (L : ℝ) * ‖x‖) :
    Integrable (fun W : Reference.Space (n * q) ↦ ⨅ t : UnitSphere q, P (gaussianMatrixAction W t))
      (standardGaussian (n * q)) := by
  simpa using gaussian_linear_image_integrable (gordon_matrix_inf_lipschitz P hP hbound)
    (ContinuousLinearMap.id ℝ (Reference.Space (n * q)))

lemma gaussian_matrix_norm_joint_integrable
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) :
    Integrable (fun z : Reference.Space (n * q) × Reference.Space n ↦
      ‖gaussianMatrixTransposeAction z.1 z.2‖) ((standardGaussian (n * q)).prod μ) := by
  have hx : Integrable (fun x : Reference.Space n ↦ ‖x‖) μ :=
    (compact_memLp_continuous μ hc continuous_norm 1).integrable le_rfl
  apply ((standardGaussian_norm_integrable (n * q)).mul_prod hx).mono'
    gaussianMatrixTransposeAction_joint_continuous.norm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z ↦ by
    simpa only [norm_norm] using gaussianMatrixTransposeAction_norm_le z.1 z.2

/-- Averaging the norm of the genuine Gaussian matrix image separates the
original mean norm and the standard Gaussian mean norm. -/
theorem gaussian_matrix_norm_average
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) :
    (∫ W : Reference.Space (n * q), ∫ x, ‖gaussianMatrixTransposeAction W x‖ ∂μ
      ∂standardGaussian (n * q)) =
      (∫ h : Reference.Space q, ‖h‖ ∂standardGaussian q) * ∫ x : Reference.Space n, ‖x‖ ∂μ := by
  rw [integral_integral_swap (gaussian_matrix_norm_joint_integrable μ hc)]
  simp_rw [standardGaussian_transposeAction_norm_integral]
  rw [integral_mul_const, mul_comm]

/-- A fixed universal constant for the strong/weak comparison; no numerical
optimization of the source's constants is attempted. -/
def strongWeakConstant : ℝ := 1000 / scalarGaussianLowerConstant

lemma strongWeakConstant_pos : 0 < strongWeakConstant :=
  div_pos (by norm_num) scalarGaussianLowerConstant_pos

section CompactMoments

variable (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (p : ℝ) [hp : Fact (1 ≤ p)] (hμ : μ ≪ volume)

include hc hp

/-- The complete Gaussian minimax/concentration lemma in the Paouris proof,
for the actual weak-moment norm of the original probability law. -/
theorem strong_moment_gaussian_minimax [NeZero q] {L : ℝ≥0}
    (hbound : ∀ a, momentNorm μ hc p hμ a ≤ (L : ℝ) * ‖a‖) :
    (∫ t : Reference.Space 1, ‖t‖ ^ p ∂standardGaussian 1) ^ (1 / p) *
      (∫ x : Reference.Space n, ‖x‖ ^ p ∂μ) ^ (1 / p) ≤
      (∫ W : Reference.Space (n * q), ⨅ t : UnitSphere q,
        momentNorm μ hc p hμ (gaussianMatrixAction W t) ∂standardGaussian (n * q)) +
      (Real.sqrt (q : ℝ) + 12 * Real.sqrt p) * (L : ℝ) := by
  have hconc := standardGaussian_lipschitz_moment_le
    (momentNorm_lipschitz μ hc p hμ hbound) (fun a ↦ apply_nonneg (momentNorm μ hc p hμ) a) hp.out
  rw [momentNorm_gaussian_moment_identity] at hconc
  have hgordon := norm_gordon_sqrt (q := q) (momentNorm μ hc p hμ)
    (momentNorm_smul μ hc p hμ) hbound
  nlinarith

/-- Once the proved small-direction theorem has been transported to every
linear image of the input law, Gaussian averaging gives the strong moment
bound. This theorem isolates that geometric transport obligation explicitly. -/
theorem strong_moment_bound_of_small_directions [NeZero q] {L : ℝ≥0}
    (hbound : ∀ a, momentNorm μ hc p hμ a ≤ (L : ℝ) * ‖a‖)
    (hsmall : ∀ W : Reference.Space (n * q), ∃ t : Reference.Space q, ‖t‖ = 1 ∧
      momentNorm μ hc p hμ (gaussianMatrixAction W t) ≤
        500 * ∫ x, ‖gaussianMatrixTransposeAction W x‖ ∂μ) :
    (∫ t : Reference.Space 1, ‖t‖ ^ p ∂standardGaussian 1) ^ (1 / p) *
      (∫ x : Reference.Space n, ‖x‖ ^ p ∂μ) ^ (1 / p) ≤
      500 * Real.sqrt (q : ℝ) * (∫ x : Reference.Space n, ‖x‖ ∂μ) +
        (Real.sqrt (q : ℝ) + 12 * Real.sqrt p) * (L : ℝ) := by
  have hmin := gordon_matrix_inf_integrable (q := q) (momentNorm μ hc p hμ)
    (momentNorm_smul μ hc p hμ) hbound
  have hmean := (gaussian_matrix_norm_joint_integrable (q := q) μ hc).integral_prod_left
  have hle := integral_mono hmin (hmean.const_mul 500) (fun W ↦ by
    obtain ⟨t, ht, htm⟩ := hsmall W
    have hbd : BddBelow (range (fun t : UnitSphere q ↦
        momentNorm μ hc p hμ (gaussianMatrixAction W t))) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact apply_nonneg _ _
    have htmem : t ∈ UnitSphere q := by simpa only [UnitSphere, Metric.mem_sphere, dist_zero_right] using ht
    exact (ciInf_le hbd ⟨t, htmem⟩).trans htm)
  rw [integral_const_mul, gaussian_matrix_norm_average μ hc] at hle
  have hnormpos : 0 ≤ ∫ x : Reference.Space n, ‖x‖ ∂μ := integral_nonneg fun x ↦ norm_nonneg _
  have havg := mul_le_mul_of_nonneg_right (standardGaussian_norm_integral_le_sqrt q) hnormpos
  have hmain := strong_moment_gaussian_minimax (q := q) μ hc p hμ hbound
  nlinarith

/-- Cancellation of the scalar Gaussian factor completes the analytic
strong/weak comparison when the image dimension is at most twice `p`. -/
theorem strong_moment_le_mean_add_weak [NeZero q] {L : ℝ≥0}
    (hp2 : 2 ≤ p) (hq : (q : ℝ) ≤ 2 * p)
    (hbound : ∀ a, momentNorm μ hc p hμ a ≤ (L : ℝ) * ‖a‖)
    (hsmall : ∀ W : Reference.Space (n * q), ∃ t : Reference.Space q, ‖t‖ = 1 ∧
      momentNorm μ hc p hμ (gaussianMatrixAction W t) ≤
        500 * ∫ x, ‖gaussianMatrixTransposeAction W x‖ ∂μ) :
    (∫ x : Reference.Space n, ‖x‖ ^ p ∂μ) ^ (1 / p) ≤
      strongWeakConstant * ((∫ x : Reference.Space n, ‖x‖ ∂μ) + (L : ℝ)) := by
  have hp0 : 0 < p := by linarith
  have hpnn := hp0.le
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hqroot : Real.sqrt (q : ℝ) ≤ 2 * Real.sqrt p := by
    have hsp := Real.sq_sqrt hpnn
    have hsq := Real.sq_sqrt (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    nlinarith [Real.sqrt_nonneg (q : ℝ), hsqrt]
  have hS : 0 ≤ (∫ x : Reference.Space n, ‖x‖ ^ p ∂μ) ^ (1 / p) :=
    Real.rpow_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _
  have hmean : 0 ≤ ∫ x : Reference.Space n, ‖x‖ ∂μ := integral_nonneg fun x ↦ norm_nonneg _
  have hlower := mul_le_mul_of_nonneg_right (standardGaussian_scalar_moment_lower hp2) hS
  have hmain := strong_moment_bound_of_small_directions (q := q) μ hc p hμ hbound hsmall
  have h₁ := mul_le_mul_of_nonneg_right hqroot hmean
  have h₂ := mul_le_mul_of_nonneg_right hqroot L.coe_nonneg
  have hc : scalarGaussianLowerConstant *
      (∫ x : Reference.Space n, ‖x‖ ^ p ∂μ) ^ (1 / p) ≤
      1000 * (∫ x : Reference.Space n, ‖x‖ ∂μ) + 14 * (L : ℝ) := by
    apply (mul_le_mul_left hsqrt).mp
    nlinarith
  unfold strongWeakConstant
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ scalarGaussianLowerConstant_pos).mpr
  nlinarith [L.coe_nonneg]

end CompactMoments

end GaussianTilt.Paouris
