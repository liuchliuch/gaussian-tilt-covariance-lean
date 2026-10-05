import GaussianTilt.WhiteningRootContinuity
import GaussianTilt.WhiteningTruncation
import GaussianTilt.MomentMapGaussianApproximation
import GaussianTilt.IsotropicIntegrability

/-! # Actual fourth-moment convergence after affine whitening

Dominated convergence is applied on the original product probability space.
The covariance inverse roots and barycenters are actual moments, and the
moving affine map is controlled by its proved convergence to the identity.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped BigOperators Matrix.Norms.L2Operator Topology ENNReal
namespace GaussianTilt.Whitening
open MomentMapApproximation
variable {n : ℕ}

def affineValue (A : Matrix (Fin n) (Fin n) ℝ) (m x : Reference.Space n) : Reference.Space n :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A (x - m)

lemma continuous_affineValue (A : Matrix (Fin n) (Fin n) ℝ) (m : Reference.Space n) :
    Continuous (affineValue A m) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A).continuous.comp (continuous_id.sub continuous_const)

lemma continuous_matrix_apply :
    Continuous (fun z : Matrix (Fin n) (Fin n) ℝ × Reference.Space n ↦
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) z.1 z.2) := by
  have heq : (fun z : Matrix (Fin n) (Fin n) ℝ × Reference.Space n ↦
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) z.1 z.2) =
      fun z ↦ WithLp.toLp 2 (z.1 *ᵥ coordinates z.2) := by
    funext z
    apply WithLp.ofLp_injective
    exact Matrix.ofLp_toEuclideanCLM z.1 z.2
  rw [heq]
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp
  unfold Matrix.mulVec dotProduct coordinates
  fun_prop

lemma affineValue_tendsto {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {m x : ℕ → Reference.Space n}
    {y : Reference.Space n} (hA : Tendsto A atTop (𝓝 1)) (hm : Tendsto m atTop (𝓝 0))
    (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun k ↦ affineValue (A k) (m k) (x k)) atTop (𝓝 y) := by
  have h := continuous_matrix_apply.tendsto (1, y - 0) |>.comp (hA.prodMk_nhds (hx.sub hm))
  simpa only [sub_zero, affineValue, map_one, ContinuousLinearMap.one_apply] using h

lemma matrix_one_norm_le_one : ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1 := by
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
      letI := h
      rw [Subsingleton.elim (1 : Matrix (Fin n) (Fin n) ℝ) 0, norm_zero]
      norm_num
  | inr h => letI := h; simp

lemma eventually_affine_bounds {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {m : ℕ → Reference.Space n}
    (hA : Tendsto A atTop (𝓝 1)) (hm : Tendsto m atTop (𝓝 0)) :
    ∀ᶠ k in atTop, ‖A k‖ ≤ 2 ∧ ‖m k‖ ≤ 1 := by
  have ha := hA.norm.eventually (eventually_lt_nhds
    (lt_of_le_of_lt matrix_one_norm_le_one (by norm_num : (1 : ℝ) < 2)))
  have hm' : Tendsto (fun k ↦ ‖m k‖) atTop (𝓝 (0 : ℝ)) := by simpa using hm.norm
  filter_upwards [ha, hm'.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with k hak hmk
  exact ⟨hak.le, hmk.le⟩

lemma affineValue_norm_le {A : Matrix (Fin n) (Fin n) ℝ} {m : Reference.Space n}
    (hA : ‖A‖ ≤ 2) (hm : ‖m‖ ≤ 1) (x : Reference.Space n) :
    ‖affineValue A m x‖ ≤ 2 * (‖x‖ + 1) := by
  calc
    _ ≤ ‖A‖ * ‖x - m‖ := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A).le_opNorm _
    _ ≤ 2 * (‖x‖ + 1) := mul_le_mul hA
      ((norm_sub_le x m).trans (add_le_add_left hm _)) (norm_nonneg _) (by norm_num)

lemma affine_perturb_fourth_bound {A : Matrix (Fin n) (Fin n) ℝ} {m : Reference.Space n}
    (hA : ‖A‖ ≤ 2) (hm : ‖m‖ ≤ 1) (k : ℕ) (p : Reference.Space n × Reference.Space n) :
    ‖affineValue A m (perturb k p)‖ ^ 4 ≤
      16 * 8 * (8 * (‖p.1‖ ^ 4 + ‖p.2‖ ^ 4) + 1) := by
  have hb : ‖affineValue A m (perturb k p)‖ ≤ 2 * ((‖p.1‖ + ‖p.2‖) + 1) :=
    (affineValue_norm_le hA hm _).trans (by
      gcongr
      exact perturb_norm_le k p)
  have h₁ := add_pow_le (show 0 ≤ ‖p.1‖ + ‖p.2‖ by positivity) (by norm_num : (0 : ℝ) ≤ 1) 4
  have h₂ := add_pow_le (norm_nonneg p.1) (norm_nonneg p.2) 4
  have h₃ := pow_le_pow_left₀ (norm_nonneg _) hb 4
  norm_num only [Nat.sub_eq, Nat.reduceSub, one_pow, Nat.cast_ofNat, OfNat.ofNat, pow_succ,
    pow_zero, mul_one] at h₁ h₂
  calc
    _ ≤ (2 * ((‖p.1‖ + ‖p.2‖) + 1)) ^ 4 := h₃
    _ = 16 * ((‖p.1‖ + ‖p.2‖) + 1) ^ 4 := by ring
    _ ≤ 16 * (8 * ((‖p.1‖ + ‖p.2‖) ^ 4 + 1)) := by nlinarith [h₁]
    _ ≤ _ := by nlinarith [h₂]

/-- Simultaneous perturbation, normalization, and a moving affine map near
the identity preserve every continuous observable of fourth-order growth. -/
theorem integral_affine_perturbedTruncation_tendsto
    (μ ν : Measure (Reference.Space n)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 4) μ)
    (hν : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 4) ν)
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {m : ℕ → Reference.Space n}
    (hA : Tendsto A atTop (𝓝 1)) (hm : Tendsto m atTop (𝓝 0))
    {f : Reference.Space n → ℝ} (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ 4)) :
    Tendsto (fun k ↦ ∫ x, f (affineValue (A k) (m k) x) ∂perturbedTruncation μ ν k)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  let D : Reference.Space n × Reference.Space n → ℝ := fun p ↦
    C * (1 + 16 * 8 * (8 * (‖p.1‖ ^ 4 + ‖p.2‖ ^ 4) + 1))
  have hiD : Integrable D (μ.prod ν) := by
    exact ((integrable_const 1).add
      ((((hμ.comp_fst ν).add (hν.comp_snd μ)).const_mul 8 |>.add (integrable_const 1)).const_mul
        (16 * 8))).const_mul C
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ.prod ν)
    (F := fun k ↦ (truncationEvent k).indicator (fun p ↦ f (affineValue (A k) (m k) (perturb k p))))
    (f := fun p ↦ f p.1) D
    (Eventually.of_forall (fun k ↦
      ((hf.comp (continuous_affineValue (A k) (m k))).comp (continuous_perturb k)).measurable.indicator
        (measurableSet_truncationEvent k) |>.aestronglyMeasurable))
    (by
      filter_upwards [eventually_affine_bounds hA hm] with k hk
      exact ae_of_all _ (fun p ↦ by
        by_cases hp : p ∈ truncationEvent k
        · rw [indicator_of_mem hp]
          exact (hbound _).trans (mul_le_mul_of_nonneg_left
            (add_le_add_left (affine_perturb_fourth_bound hk.1 hk.2 k p) 1) hC)
        · rw [indicator_of_notMem hp, norm_zero]
          dsimp [D]
          positivity)) hiD
    (ae_of_all _ (fun p ↦ by
      apply (hf.continuousAt.tendsto.comp (affineValue_tendsto hA hm (tendsto_perturb p))).congr'
      filter_upwards [eventually_mem_truncationEvent p] with k hk
      simp only [indicator_of_mem hk, Function.comp_apply]))
  have hi : Integrable f μ := ((integrable_const 1).add hμ |>.const_mul C).mono'
    hf.aestronglyMeasurable (ae_of_all _ hbound)
  have hprod : (∫ p : Reference.Space n × Reference.Space n, f p.1 ∂μ.prod ν) = ∫ x, f x ∂μ := by
    rw [integral_prod _ (hi.comp_fst ν)]
    simp
  rw [hprod] at ht
  have hd := ht.div (tendsto_truncation_mass μ ν) (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun k ↦ (∫ p, (truncationEvent k).indicator
    (fun q ↦ f (affineValue (A k) (m k) (perturb k q))) p ∂μ.prod ν) /
      (μ.prod ν (truncationEvent k)).toReal) atTop (𝓝 ((∫ x, f x ∂μ) / 1)) at hd
  simp only [div_one] at hd
  apply hd.congr'
  exact Eventually.of_forall (fun k ↦
    (integral_perturbedTruncation μ ν k
      (hf.comp (continuous_affineValue (A k) (m k))).measurable).symm)

lemma norm_sq_integrable_of_fourth {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 4) μ) :
    Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ := by
  apply ((integrable_const (1 : ℝ)).add hμ).mono' (by fun_prop)
  exact ae_of_all _ (fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖x‖ ^ 2 ≤ 1 + ‖x‖ ^ 4
    nlinarith [sq_nonneg (‖x‖ ^ 2 - 1)])

lemma coordinates_memLp_of_norm_sq {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ) (i : Fin n) :
    MemLp (fun x : Reference.Space n ↦ x i) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i).aestronglyMeasurable).mpr
  simpa only [pow_two] using coordinate_product_integrable_of_norm_sq hμ i i

lemma covariance_eq_reference {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hX : ∀ i : Fin n, MemLp (fun x ↦ x i) 2 μ) : covariance μ = Reference.covariance μ :=
  (Reference.covariance_eq_covarianceMatrix hX).symm

lemma covariance_perturbedTruncation_tendsto (μ ν : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ)
    (hν : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) ν) :
    Tendsto (fun k ↦ covariance (perturbedTruncation μ ν k)) atTop (𝓝 (covariance μ)) := by
  rw [covariance_eq_reference (coordinates_memLp_of_norm_sq hμ)]
  apply (reference_covariance_perturbedTruncation_tendsto μ ν hμ hν).congr'
  filter_upwards [eventually_perturbedTruncation_probability μ ν] with k hk
  letI := hk
  exact (covariance_eq_reference
    (compact_coordinates_memLp (perturbedTruncation_compactlySupported μ ν k))).symm

lemma eventually_perturbedTruncation_covariance_psd
    (μ ν : Measure (Reference.Space n)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∀ᶠ k in atTop, (covariance (perturbedTruncation μ ν k)).PosSemidef := by
  filter_upwards [eventually_perturbedTruncation_probability μ ν] with k hk
  letI := hk
  exact covarianceMatrix_posSemidef
    (compact_coordinates_memLp (perturbedTruncation_compactlySupported μ ν k))

lemma center_perturbedTruncation_tendsto (μ ν : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ)
    (hν : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) ν) :
    Tendsto (fun k ↦ center (perturbedTruncation μ ν k)) atTop (𝓝 (center μ)) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.continuous.tendsto _ |>.comp
    (meanVector_perturbedTruncation_tendsto μ ν hμ hν)

lemma isotropic_covariance_eq_one {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hiso : Reference.isotropic μ) : covariance μ = 1 := by
  rw [covariance_eq_reference (Reference.isotropic_coordinate_memLp hiso), hiso.2]

lemma isotropic_center_eq_zero {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hiso : Reference.isotropic μ) : center μ = 0 := by
  rw [center_eq_mean (fun i ↦ (Reference.isotropic_coordinate_memLp hiso i).integrable (by norm_num)), hiso.1]

lemma integral_law (μ : Measure (Reference.Space n)) {f : Reference.Space n → ℝ} (hf : Measurable f) :
    (∫ x, f x ∂law μ) = ∫ x, f (whitenMap μ x) ∂μ := by
  rw [law, integral_map (continuous_whitenMap μ).measurable.aemeasurable hf.aestronglyMeasurable]

/-- Complete fourth-polynomial-growth approximation for the genuinely
whitened normalized compact laws. The covariance, means, and affine maps
are all those of the constructed laws, with no approximation hypothesis. -/
theorem integral_whitened_perturbedTruncation_tendsto
    (μ ν : Measure (Reference.Space n)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 4) μ)
    (hν : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 4) ν)
    (hiso : Reference.isotropic μ)
    {f : Reference.Space n → ℝ} (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ 4)) :
    Tendsto (fun k ↦ ∫ x, f x ∂law (perturbedTruncation μ ν k))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hμ₂ := Reference.isotropic_norm_sq_integrable hiso
  have hν₂ := norm_sq_integrable_of_fourth hν
  have hcov := covariance_perturbedTruncation_tendsto μ ν hμ₂ hν₂
  rw [isotropic_covariance_eq_one hiso] at hcov
  have hA := inverseRoot_tendsto_one hcov (eventually_perturbedTruncation_covariance_psd μ ν)
  have hm := center_perturbedTruncation_tendsto μ ν hμ₂ hν₂
  rw [isotropic_center_eq_zero hiso] at hm
  have h := integral_affine_perturbedTruncation_tendsto μ ν hμ hν hA hm hf hC hbound
  simpa only [integral_law _ hf.measurable, whitenMap, affineValue] using h

/-- The same explicit approximation is eventually an actual compactly
supported isotropic probability law. -/
theorem eventually_whitened_perturbedTruncation_isotropic
    (μ ν : Measure (Reference.Space n)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) ν)
    (hiso : Reference.isotropic μ) :
    ∀ᶠ k in atTop,
      IsProbabilityMeasure (law (perturbedTruncation μ ν k)) ∧
      Reference.compactlySupported (law (perturbedTruncation μ ν k)) ∧
      Reference.isotropic (law (perturbedTruncation μ ν k)) := by
  filter_upwards [eventually_perturbedTruncation_probability μ ν,
    eventually_perturbedTruncation_covariance_posDef μ ν
      (Reference.isotropic_norm_sq_integrable hiso) hν hiso] with k hpk hck
  letI := hpk
  have hc := perturbedTruncation_compactlySupported μ ν k
  have hX := compact_coordinates_memLp hc
  have hC : (covariance (perturbedTruncation μ ν k)).PosDef := by
    rw [covariance_eq_reference hX]
    exact hck
  exact ⟨inferInstance, law_compactlySupported hc, law_isotropic hX hC⟩

/-- Every polynomial of degree at most four has the correct limiting integral
after Gaussian regularization, normalized truncation, and exact whitening. -/
theorem gaussianTruncation_whitened_polynomial_moment_tendsto
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 4) μ)
    (hiso : Reference.isotropic μ) (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ 4) :
    Tendsto (fun k ↦ ∫ x, MvPolynomial.eval (fun i ↦ x i) p
      ∂law (perturbedTruncation μ (Paouris.standardGaussian n) k))
      atTop (𝓝 (∫ x, MvPolynomial.eval (fun i ↦ x i) p ∂μ)) := by
  apply integral_whitened_perturbedTruncation_tendsto μ (Paouris.standardGaussian n) hμ
    (standardGaussian_norm_fourth_integrable n) hiso (p.continuous_eval.comp (by fun_prop))
    (Finset.sum_nonneg (fun a _ ↦ norm_nonneg (p.coeff a)))
  exact polynomial_fourth_growth p hp

end GaussianTilt.Whitening
