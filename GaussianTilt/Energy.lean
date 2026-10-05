import GaussianTilt.MomentBridge
import GaussianTilt.Quadratic
import GaussianTilt.NormTrace

/-!
# Monotone quadratic energy along Gaussian tilts

Compact support supplies all moments. Starting from a genuinely isotropic law,
the total second moment is `n` initially and cannot increase under a radial tilt.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator

namespace GaussianTilt.CompactProbability

variable {n : ℕ} (P : CompactProbability n)

lemma continuous_expectation {f : Point n → ℝ} (hf : Integrable f P.measure) :
    Continuous (fun t ↦ P.expectation t f) :=
  continuous_iff_continuousAt.mpr fun t ↦ (P.hasDerivAt_expectation hf t).continuousAt

lemma continuous_covariance {f g : Point n → ℝ}
    (hf : Integrable f P.measure) (hg : Integrable g P.measure)
    (hfg : Integrable (fun x ↦ f x * g x) P.measure) :
    Continuous (fun t ↦ P.covariance t f g) :=
  (P.continuous_expectation hfg).sub
    ((P.continuous_expectation hf).mul (P.continuous_expectation hg))

lemma continuous_variance_energy : Continuous (fun t ↦ P.variance t energy) :=
  P.continuous_covariance P.integrable_energy P.integrable_energy
    (P.integrable_energy_mul P.integrable_energy)

lemma antitone_expectation_energy : Antitone (fun t ↦ P.expectation t energy) := by
  apply antitone_of_deriv_nonpos (fun t ↦ (P.hasDerivAt_expectation P.integrable_energy t).differentiableAt)
  intro t
  rw [(P.hasDerivAt_expectation P.integrable_energy t).deriv]
  exact neg_nonpos.mpr (P.variance_energy_nonneg t)

lemma expectation_energy_le_initial {t : ℝ} (ht : 0 ≤ t) :
    P.expectation t energy ≤ ∫ x, energy x ∂P.measure := by
  simpa only [P.expectation_zero] using P.antitone_expectation_energy ht

lemma integrable_id : Integrable (fun x : Point n ↦ x) P.measure :=
  (integrable_const (P.bound + 1)).mono' continuous_id.aestronglyMeasurable P.ae_norm_le

lemma integral_coordinate_eq_mean (i : Fin n) :
    (∫ x, x i ∂P.measure) = Reference.mean P.measure i :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).integral_comp_comm P.integrable_id

lemma energy_eq_sum_sq (x : Point n) : energy x = ∑ i : Fin n, (x i) ^ 2 := by
  simp only [energy, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

lemma expectation_energy_eq_sum (t : ℝ) :
    P.expectation t energy = ∑ i : Fin n, P.expectation t (fun x ↦ (x i) ^ 2) := by
  simp only [← P.integral_tilt]
  simp_rw [energy_eq_sum_sq]
  exact integral_finset_sum _ fun i _ ↦
    P.integrable_tilt (P.integrable_continuous (by fun_prop)) t

lemma isotropic_integral_coordinate (hiso : Reference.isotropic P.measure) (i : Fin n) :
    (∫ x, x i ∂P.measure) = 0 := by
  rw [P.integral_coordinate_eq_mean, hiso.1]
  rfl

lemma isotropic_integral_coordinate_sq (hiso : Reference.isotropic P.measure) (i : Fin n) :
    (∫ x, (x i) ^ 2 ∂P.measure) = 1 := by
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A i i) hiso.2
  simpa only [Reference.covariance, P.isotropic_integral_coordinate hiso i,
    zero_mul, sub_zero, Matrix.one_apply_eq, pow_two] using h

lemma isotropic_initial_energy (hiso : Reference.isotropic P.measure) :
    P.expectation 0 energy = n := by
  rw [P.expectation_energy_eq_sum]
  simp only [P.expectation_zero, P.isotropic_integral_coordinate_sq hiso,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma expectation_energy_le_dimension (hiso : Reference.isotropic P.measure)
    {t : ℝ} (ht : 0 ≤ t) : P.expectation t energy ≤ n := by
  calc
    P.expectation t energy ≤ P.expectation 0 energy := P.antitone_expectation_energy ht
    _ = n := P.isotropic_initial_energy hiso

lemma trace_covariance_le_energy (t : ℝ) :
    Matrix.trace (Reference.covariance (P.tilt t)) ≤ P.expectation t energy := by
  rw [P.expectation_energy_eq_sum]
  unfold Matrix.trace
  apply Finset.sum_le_sum
  intro i hi
  simp only [Matrix.diag_apply, Reference.covariance, P.integral_tilt]
  simp only [pow_two]
  nlinarith [sq_nonneg (P.expectation t (fun x ↦ x i))]

lemma trace_covariance_le_dimension (hiso : Reference.isotropic P.measure)
    {t : ℝ} (ht : 0 ≤ t) : Matrix.trace (Reference.covariance (P.tilt t)) ≤ n :=
  (P.trace_covariance_le_energy t).trans (P.expectation_energy_le_dimension hiso ht)

lemma reference_covariance_eq_covarianceMatrix (t : ℝ) :
    Reference.covariance (P.tilt t) =
      GaussianTilt.covarianceMatrix (P.tilt t) (fun x : Point n ↦ fun i : Fin n ↦ x i) := by
  ext i j
  rw [GaussianTilt.covarianceMatrix, ProbabilityTheory.covariance_eq_sub
    (P.memLp_continuous_tilt (by fun_prop) t 2)
    (P.memLp_continuous_tilt (by fun_prop) t 2)]
  rfl

lemma covariance_posSemidef (t : ℝ) : (Reference.covariance (P.tilt t)).PosSemidef := by
  rw [P.reference_covariance_eq_covarianceMatrix]
  exact GaussianTilt.covarianceMatrix_posSemidef
    (fun i ↦ P.memLp_continuous_tilt (by fun_prop) t 2)

lemma covariance_opNorm_le_energy (t : ℝ) :
    ‖Reference.covariance (P.tilt t)‖ ≤ P.expectation t energy :=
  (GaussianTilt.posSemidef_opNorm_le_trace (P.covariance_posSemidef t)).trans
    (P.trace_covariance_le_energy t)

/-- The dimension bound used to handle bounded dimensions is valid even
without logconcavity. -/
lemma covariance_opNorm_le_dimension (hiso : Reference.isotropic P.measure)
    {t : ℝ} (ht : 0 ≤ t) : ‖Reference.covariance (P.tilt t)‖ ≤ n :=
  (P.covariance_opNorm_le_energy t).trans (P.expectation_energy_le_dimension hiso ht)

lemma trace_secondMoment_eq_energy (t : ℝ) :
    Matrix.trace (secondMomentMatrix (P.tilt t) (fun x : Point n ↦ fun i : Fin n ↦ x i)) =
      P.expectation t energy := by
  rw [P.expectation_energy_eq_sum]
  simp only [Matrix.trace, Matrix.diag_apply, secondMomentMatrix, P.integral_tilt, pow_two]

lemma secondMoment_opNorm_le_energy (t : ℝ) :
    ‖secondMomentMatrix (P.tilt t) (fun x : Point n ↦ fun i : Fin n ↦ x i)‖ ≤
      P.expectation t energy := by
  rw [← P.trace_secondMoment_eq_energy]
  exact GaussianTilt.posSemidef_opNorm_le_trace (GaussianTilt.secondMomentMatrix_posSemidef
    (fun i ↦ P.memLp_continuous_tilt (by fun_prop) t 2))

lemma secondMoment_opNorm_le_dimension (hiso : Reference.isotropic P.measure)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖secondMomentMatrix (P.tilt t) (fun x : Point n ↦ fun i : Fin n ↦ x i)‖ ≤ n :=
  (P.secondMoment_opNorm_le_energy t).trans (P.expectation_energy_le_dimension hiso ht)

end GaussianTilt.CompactProbability

namespace GaussianTilt

/-- Directly stated for the paper's measure and Gaussian-tilt definitions. -/
theorem gaussianTilt_covariance_opNorm_le_dimension {n : ℕ}
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hcompact : Reference.compactlySupported μ) (hiso : Reference.isotropic μ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖Reference.covariance (Reference.gaussianTilt μ t)‖ ≤ n := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hcompact
  exact P.covariance_opNorm_le_dimension hiso ht

end GaussianTilt
