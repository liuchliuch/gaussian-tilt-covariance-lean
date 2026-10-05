import GaussianTilt.MomentMapStrongApproximation

/-! # Actual covariance and whitening of strongly regular approximants -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped Topology ENNReal BigOperators Matrix.Norms.L2Operator
namespace GaussianTilt.MomentMapApproximation
open Paouris Whitening
variable {n : ℕ}

lemma coordinate_fourth_growth (i : Fin n) (x : Reference.Space n) :
    ‖x i‖ ≤ 1 * (1 + ‖x‖ ^ 4) := by
  rw [one_mul]
  exact (PiLp.norm_apply_le x i).trans
    (by simpa using pow_le_one_add_fourth (norm_nonneg x) (show 1 ≤ 4 by norm_num))

lemma coordinate_product_fourth_growth (i j : Fin n) (x : Reference.Space n) :
    ‖x i * x j‖ ≤ 1 * (1 + ‖x‖ ^ 4) := by
  rw [one_mul, norm_mul]
  calc
    _ ≤ ‖x‖ * ‖x‖ := mul_le_mul (PiLp.norm_apply_le x i) (PiLp.norm_apply_le x j)
      (norm_nonneg _) (norm_nonneg _)
    _ ≤ _ := by simpa only [← sq] using
      pow_le_one_add_fourth (norm_nonneg x) (show 2 ≤ 4 by norm_num)

lemma meanVector_strongTruncation_tendsto (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hμ : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ) :
    Tendsto (fun k => meanVector (strongTruncation μ k) coordinates)
      atTop (𝓝 (meanVector μ coordinates)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact integral_strongTruncation_tendsto μ hμ
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i) (by norm_num : (0 : ℝ) ≤ 1)
    (coordinate_fourth_growth i)

lemma center_strongTruncation_tendsto (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hμ : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ) :
    Tendsto (fun k => center (strongTruncation μ k)) atTop (𝓝 (center μ)) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.continuous.tendsto _ |>.comp
    (meanVector_strongTruncation_tendsto μ hμ)

lemma reference_covariance_strongTruncation_tendsto (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hμ : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ) :
    Tendsto (fun k => Reference.covariance (strongTruncation μ k))
      atTop (𝓝 (Reference.covariance μ)) := by
  have hm := meanVector_strongTruncation_tendsto μ hμ
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact (integral_strongTruncation_tendsto μ hμ (by fun_prop)
    (by norm_num : (0 : ℝ) ≤ 1) (coordinate_product_fourth_growth i j)).sub
      ((tendsto_pi_nhds.mp hm i).mul (tendsto_pi_nhds.mp hm j))

lemma covariance_strongTruncation_tendsto (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hμ : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ) :
    Tendsto (fun k => covariance (strongTruncation μ k)) atTop (𝓝 (covariance μ)) := by
  rw [covariance_eq_reference (coordinates_memLp_of_norm_sq (norm_sq_integrable_of_fourth hμ))]
  apply (reference_covariance_strongTruncation_tendsto μ hμ).congr'
  exact Eventually.of_forall (fun k =>
    (covariance_eq_reference (compact_coordinates_memLp (strongTruncation_compactlySupported μ k))).symm)

lemma strongTruncation_covariance_posSemidef (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (k : ℕ) : (covariance (strongTruncation μ k)).PosSemidef :=
  covarianceMatrix_posSemidef (compact_coordinates_memLp (strongTruncation_compactlySupported μ k))

lemma eventually_strongTruncation_covariance_posDef (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hμ : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ)
    (hiso : Reference.isotropic μ) :
    ∀ᶠ k in atTop, (covariance (strongTruncation μ k)).PosDef := by
  apply eventually_posDef_of_tendsto_one _
    (Eventually.of_forall (strongTruncation_covariance_posSemidef μ))
  rw [← isotropic_covariance_eq_one hiso]
  exact covariance_strongTruncation_tendsto μ hμ

/-- The actual centered inverse roots converge to the identity and preserve
all continuous fourth-growth observables. -/
theorem integral_whitened_strongTruncation_tendsto
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ)
    (hiso : Reference.isotropic μ)
    {f : Reference.Space n → ℝ} (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ 4)) :
    Tendsto (fun k => ∫ x, f x ∂law (strongTruncation μ k))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hcov := covariance_strongTruncation_tendsto μ hμ
  rw [isotropic_covariance_eq_one hiso] at hcov
  have hA := inverseRoot_tendsto_one hcov
    (Eventually.of_forall (strongTruncation_covariance_posSemidef μ))
  have hm := center_strongTruncation_tendsto μ hμ
  rw [isotropic_center_eq_zero hiso] at hm
  have h := integral_affine_strongTruncation_tendsto μ hμ hA hm hf hC hbound
  simpa only [integral_law _ hf.measurable, whitenMap, affineValue] using h

theorem whitened_strongTruncation_polynomial_moment_tendsto
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ)
    (hiso : Reference.isotropic μ) (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ 4) :
    Tendsto (fun k => ∫ x, MvPolynomial.eval (fun i => x i) p ∂law (strongTruncation μ k))
      atTop (𝓝 (∫ x, MvPolynomial.eval (fun i => x i) p ∂μ)) := by
  apply integral_whitened_strongTruncation_tendsto μ hμ hiso
    (p.continuous_eval.comp (by fun_prop))
    (Finset.sum_nonneg (fun a _ => norm_nonneg (p.coeff a)))
  exact polynomial_fourth_growth p hp

theorem eventually_whitened_strongTruncation_isotropic
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ)
    (hiso : Reference.isotropic μ) :
    ∀ᶠ k in atTop,
      IsProbabilityMeasure (law (strongTruncation μ k)) ∧
      Reference.compactlySupported (law (strongTruncation μ k)) ∧
      Reference.isotropic (law (strongTruncation μ k)) := by
  filter_upwards [eventually_strongTruncation_covariance_posDef μ hμ hiso] with k hk
  have hc := strongTruncation_compactlySupported μ k
  exact ⟨inferInstance, law_compactlySupported hc, law_isotropic (compact_coordinates_memLp hc) hk⟩

end GaussianTilt.MomentMapApproximation
