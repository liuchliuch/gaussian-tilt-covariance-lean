import GaussianTilt.WhiteningApproximation
import GaussianTilt.PaourisTailMoments

/-! # Actual pure-truncation whitening at fourth-moment order

The moments required for general isotropic logconcave laws follow from the
proved Paouris theorem. Dominated convergence below is on the original law,
and the moving affine maps are its genuine covariance whitenings.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped Topology ENNReal Matrix.Norms.L2Operator

namespace GaussianTilt.Whitening
variable {n : ℕ}

lemma affineValue_fourth_bound {A : Matrix (Fin n) (Fin n) ℝ} {m : Reference.Space n}
    (hA : ‖A‖ ≤ 2) (hm : ‖m‖ ≤ 1) (x : Reference.Space n) :
    ‖affineValue A m x‖ ^ 4 ≤ 128 * (‖x‖ ^ 4 + 1) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (affineValue_norm_le hA hm x) 4
  have hsum := add_pow_le (norm_nonneg x) (by norm_num : (0 : ℝ) ≤ 1) 4
  norm_num at hsum
  nlinarith

theorem integral_affine_ballRestriction_tendsto
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 4) μ)
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {m : ℕ → Reference.Space n}
    (hA : Tendsto A atTop (𝓝 1)) (hm : Tendsto m atTop (𝓝 0))
    {f : Reference.Space n → ℝ} (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ 4)) :
    Tendsto (fun k ↦ ∫ x, f (affineValue (A k) (m k) x) ∂ballRestriction μ k)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  let D : Reference.Space n → ℝ := fun x ↦ C * (1 + 128 * (‖x‖ ^ 4 + 1))
  have hD : Integrable D μ :=
    ((integrable_const 1).add ((hμ.add (integrable_const 1)).const_mul 128)).const_mul C
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (F := fun k : ℕ ↦ (Metric.closedBall 0 (k : ℝ)).indicator
      (fun x ↦ f (affineValue (A k) (m k) x))) (f := f) D
    (Eventually.of_forall (fun k ↦
      ((hf.comp (continuous_affineValue (A k) (m k))).measurable.indicator
        measurableSet_closedBall).aestronglyMeasurable))
    (by
      filter_upwards [eventually_affine_bounds hA hm] with k hk
      exact ae_of_all _ (fun x ↦ by
        by_cases hx : x ∈ Metric.closedBall 0 (k : ℝ)
        · rw [indicator_of_mem hx]
          exact (hbound _).trans (mul_le_mul_of_nonneg_left
            (add_le_add_left (affineValue_fourth_bound hk.1 hk.2 x) 1) hC)
        · rw [indicator_of_notMem hx, norm_zero]
          dsimp [D]
          positivity)) hD
    (ae_of_all _ (fun x ↦ by
      apply (hf.continuousAt.tendsto.comp (affineValue_tendsto hA hm tendsto_const_nhds)).congr'
      filter_upwards [eventually_mem_closedBall x] with k hk
      simp only [indicator_of_mem hk, Function.comp_apply]))
  have hd := ht.div (ballRestriction_mass_tendsto_one μ) (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun k : ℕ ↦
    (∫ x, (Metric.closedBall 0 (k : ℝ)).indicator
      (fun x ↦ f (affineValue (A k) (m k) x)) x ∂μ) /
      (μ (Metric.closedBall 0 (k : ℝ))).toReal) atTop (𝓝 ((∫ x, f x ∂μ) / 1)) at hd
  simpa only [← integral_ballRestriction, div_one] using hd

theorem integral_whitened_ballRestriction_tendsto
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 4) μ)
    (hi : Reference.isotropic μ)
    {f : Reference.Space n → ℝ} (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ 4)) :
    Tendsto (fun k ↦ ∫ x, f x ∂law (ballRestriction μ k)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hμ₂ := Reference.isotropic_norm_sq_integrable hi
  have hcov : Tendsto (fun k ↦ covariance (ballRestriction μ k)) atTop (𝓝 1) := by
    have h := reference_covariance_ballRestriction_tendsto μ hμ₂
    rw [hi.2] at h
    apply h.congr'
    filter_upwards [eventually_ballRestriction_probability μ] with k hk
    letI := hk
    exact (covariance_eq_reference (compact_coordinates_memLp (ballRestriction_compactlySupported μ k))).symm
  have hpsd : ∀ᶠ k in atTop, (covariance (ballRestriction μ k)).PosSemidef := by
    filter_upwards [eventually_ballRestriction_probability μ] with k hk
    letI := hk
    exact covarianceMatrix_posSemidef (compact_coordinates_memLp (ballRestriction_compactlySupported μ k))
  have hm := center_ballRestriction_tendsto μ hμ₂
  rw [isotropic_center_eq_zero hi] at hm
  have h := integral_affine_ballRestriction_tendsto μ hμ
    (inverseRoot_tendsto_one hcov hpsd) hm hf hC hbound
  simpa only [integral_law _ hf.measurable, whitenMap, affineValue] using h

lemma isotropic_logconcave_norm_fourth_integrable (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hl : Reference.logconcave μ) (hi : Reference.isotropic μ) :
    Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 4) μ := by
  have h := (Paouris.isotropic_norm_moment_le μ hl hi (p := 4) (by norm_num)).1
  simpa using h

lemma abs_matrixQuadratic_le_opNorm (B : Matrix (Fin n) (Fin n) ℝ) (x : Reference.Space n) :
    |matrixQuadratic B (coordinates x)| ≤ ‖B‖ * ‖x‖ ^ 2 := by
  have heq : matrixQuadratic B (coordinates x) =
      inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B x) := by
    simp [matrixQuadratic, coordinates, EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.ofLp_toEuclideanCLM, star_trivial, dotProduct_comm]
  rw [heq]
  calc
    _ ≤ ‖x‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖B‖ * ‖x‖) := mul_le_mul_of_nonneg_left
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B).le_opNorm x) (norm_nonneg x)
    _ = _ := by ring

lemma quadratic_fourth_growth (B : Matrix (Fin n) (Fin n) ℝ) (x : Reference.Space n) :
    ‖matrixQuadratic B (coordinates x)‖ ≤ ‖B‖ * (1 + ‖x‖ ^ 4) := by
  rw [Real.norm_eq_abs]
  apply (abs_matrixQuadratic_le_opNorm B x).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
  nlinarith [sq_nonneg (‖x‖ ^ 2 - 1)]

lemma quadratic_square_le_fourth (B : Matrix (Fin n) (Fin n) ℝ) (x : Reference.Space n) :
    (matrixQuadratic B (coordinates x)) ^ 2 ≤ ‖B‖ ^ 2 * ‖x‖ ^ 4 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (abs_matrixQuadratic_le_opNorm B x) 2
  simpa only [sq_abs, mul_pow, ← pow_mul] using h

lemma quadratic_square_fourth_growth (B : Matrix (Fin n) (Fin n) ℝ) (x : Reference.Space n) :
    ‖(matrixQuadratic B (coordinates x)) ^ 2‖ ≤ ‖B‖ ^ 2 * (1 + ‖x‖ ^ 4) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (quadratic_square_le_fourth B x).trans
    (mul_le_mul_of_nonneg_left (by linarith : ‖x‖ ^ 4 ≤ 1 + ‖x‖ ^ 4) (sq_nonneg _))

lemma quadratic_memLp_of_fourth {μ : Measure (Reference.Space n)}
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 4) μ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun x : Reference.Space n ↦ matrixQuadratic B (coordinates x)) 2 μ := by
  have hc : Continuous (fun x : Reference.Space n ↦ matrixQuadratic B (coordinates x)) := by
    unfold matrixQuadratic Matrix.mulVec dotProduct coordinates
    fun_prop
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  apply (hμ.const_mul (‖B‖ ^ 2)).mono' (hc.pow 2).aestronglyMeasurable
  exact ae_of_all _ (fun x ↦ by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (matrixQuadratic B (coordinates x)))] using quadratic_square_le_fourth B x)

theorem variance_whitened_ballRestriction_tendsto
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 4) μ)
    (hi : Reference.isotropic μ) (B : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k ↦ variance (fun x : Reference.Space n ↦ matrixQuadratic B (coordinates x))
      (law (ballRestriction μ k))) atTop
      (𝓝 (variance (fun x : Reference.Space n ↦ matrixQuadratic B (coordinates x)) μ)) := by
  have hc : Continuous (fun x : Reference.Space n ↦ matrixQuadratic B (coordinates x)) := by
    unfold matrixQuadratic Matrix.mulVec dotProduct coordinates
    fun_prop
  have h₁ := integral_whitened_ballRestriction_tendsto μ hμ hi hc (norm_nonneg B)
    (quadratic_fourth_growth B)
  have h₂ := integral_whitened_ballRestriction_tendsto μ hμ hi (hc.pow 2) (sq_nonneg ‖B‖)
    (quadratic_square_fourth_growth B)
  rw [variance_eq_sub (quadratic_memLp_of_fourth hμ B)]
  apply (h₂.sub (h₁.pow 2)).congr'
  filter_upwards [eventually_ballRestriction_probability μ] with k hk
  letI := hk
  have hq := Paouris.compact_memLp_continuous (law (ballRestriction μ k))
    (law_compactlySupported (ballRestriction_compactlySupported μ k)) hc 2
  exact (variance_eq_sub hq).symm

/-- Extension from proved compact isotropic laws to the full noncompact
isotropic logconcave scope, with every approximation input constructed. -/
theorem isotropic_quadratic_bound_of_compact {C : ℝ}
    (hbound : ∀ ν : Measure (Reference.Space n), IsProbabilityMeasure ν →
      Reference.compactlySupported ν → Reference.logconcave ν → Reference.isotropic ν →
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        variance (fun x : Reference.Space n ↦ matrixQuadratic B (coordinates x)) ν ≤
          C * Matrix.trace (B ^ 2))
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hl : Reference.logconcave μ) (hi : Reference.isotropic μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    variance (fun x : Reference.Space n ↦ matrixQuadratic B (coordinates x)) μ ≤
      C * Matrix.trace (B ^ 2) := by
  apply le_of_tendsto (variance_whitened_ballRestriction_tendsto μ
    (isotropic_logconcave_norm_fourth_integrable μ hl hi) hi B)
  filter_upwards [eventually_ballRestriction_probability μ,
    eventually_ballRestriction_covariance_posDef μ (Reference.isotropic_norm_sq_integrable hi) hi,
    eventually_ballRestriction_logconcave hl] with k hp hC hlc
  letI := hp
  have hc := ballRestriction_compactlySupported μ k
  have hX := compact_coordinates_memLp hc
  rw [← covariance_eq_reference hX] at hC
  exact hbound (law (ballRestriction μ k)) inferInstance (law_compactlySupported hc)
    (law_logconcave hlc hC) (law_isotropic hX hC) B hB

end GaussianTilt.Whitening
