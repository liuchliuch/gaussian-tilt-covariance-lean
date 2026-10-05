import GaussianTilt.PaourisDirection

/-!
# Gaussian integration by parts for the Paouris comparison step

The Gaussian law here is constructed from its actual radial Lebesgue density.
Normalization and Stein's directional integration identity are proved rather
than supplied as Gaussian-comparison assumptions.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris

variable {n : ℕ}

/-- Unnormalized standard Gaussian density. -/
def gaussianKernel (n : ℕ) (x : Reference.Space n) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)

lemma integral_gaussianKernel (n : ℕ) :
    (∫ x, gaussianKernel n x) = (2 * Real.pi) ^ ((n : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := Reference.Space n) (show (0 : ℝ) < 1 / 2 by norm_num)
  simpa only [finrank_euclideanSpace_fin, div_div_eq_mul_div, div_one, mul_comm] using h

lemma gaussianKernel_integral_pos (n : ℕ) : 0 < ∫ x, gaussianKernel n x := by
  rw [integral_gaussianKernel]
  positivity

lemma gaussianKernel_integrable (n : ℕ) : Integrable (gaussianKernel n) := by
  by_contra h
  have hp := gaussianKernel_integral_pos n
  rw [integral_undef h] at hp
  exact lt_irrefl _ hp

lemma gaussianKernel_hasFDerivAt (x : Reference.Space n) :
    HasFDerivAt (gaussianKernel n)
      (-(gaussianKernel n x) • innerSL ℝ x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-(1 / 2 : ℝ))).exp
  convert h using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, gaussianKernel]
  ring

lemma gaussianKernel_fderiv_apply (x v : Reference.Space n) :
    fderiv ℝ (gaussianKernel n) x v = -⟪x, v⟫_ℝ * gaussianKernel n x := by
  rw [(gaussianKernel_hasFDerivAt x).fderiv]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply, smul_eq_mul]
  ring

/-- Normalized standard Gaussian density. -/
def standardGaussianDensity (n : ℕ) (x : Reference.Space n) : ℝ :=
  gaussianKernel n x / ∫ y, gaussianKernel n y

lemma standardGaussianDensity_pos (x : Reference.Space n) : 0 < standardGaussianDensity n x :=
  div_pos (Real.exp_pos _) (gaussianKernel_integral_pos _)

lemma standardGaussianDensity_continuous (n : ℕ) : Continuous (standardGaussianDensity n) := by
  unfold standardGaussianDensity gaussianKernel
  fun_prop

lemma standardGaussianDensity_integral (n : ℕ) : ∫ x, standardGaussianDensity n x = 1 := by
  change (∫ x, gaussianKernel n x / ∫ y, gaussianKernel n y) = 1
  rw [integral_div, div_self (gaussianKernel_integral_pos n).ne']

/-- The actual normalized radial Gaussian law. -/
def standardGaussian (n : ℕ) : Measure (Reference.Space n) :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (standardGaussianDensity n x))

instance standardGaussian_probability (n : ℕ) : IsProbabilityMeasure (standardGaussian n) := by
  constructor
  rw [standardGaussian, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_of_integral_eq_one (standardGaussianDensity_integral n))
      (Filter.Eventually.of_forall fun x ↦ (standardGaussianDensity_pos x).le),
    standardGaussianDensity_integral]
  norm_num

lemma integral_standardGaussian (g : Reference.Space n → ℝ) :
    (∫ x, g x ∂standardGaussian n) =
      (∫ x, g x * gaussianKernel n x) / ∫ x, gaussianKernel n x := by
  have h := integral_withDensity_eq_integral_toReal_smul (μ := volume)
    (standardGaussianDensity_continuous n).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) g
  change (∫ x, g x ∂standardGaussian n) = _ at h
  simp_rw [ENNReal.toReal_ofReal (standardGaussianDensity_pos _).le] at h
  simp only [smul_eq_mul, standardGaussianDensity] at h
  rw [h, ← integral_div]
  congr 1
  ext x
  ring

lemma integrable_standardGaussian_iff (g : Reference.Space n → ℝ) :
    Integrable g (standardGaussian n) ↔ Integrable (fun x ↦ g x * gaussianKernel n x) := by
  have h := integrable_withDensity_iff_integrable_smul' (μ := volume)
    (standardGaussianDensity_continuous n).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) (g := g)
  change Integrable g (standardGaussian n) ↔ _ at h
  simp_rw [ENNReal.toReal_ofReal (standardGaussianDensity_pos _).le] at h
  simp only [smul_eq_mul, standardGaussianDensity] at h
  have heq : (fun x ↦ gaussianKernel n x / (∫ x, gaussianKernel n x) * g x) =
      (fun x ↦ (g x * gaussianKernel n x) / ∫ x, gaussianKernel n x) := by ext x; ring
  rw [heq] at h
  simp only [div_eq_mul_inv] at h
  rwa [integrable_mul_const_iff (isUnit_iff_ne_zero.mpr
    (inv_ne_zero (gaussianKernel_integral_pos n).ne'))] at h

/-- Multivariate Gaussian Stein identity, with only the usual differentiability
and integrability hypotheses. This is the integration-by-parts input for
Gaussian covariance interpolation. -/
theorem standardGaussian_integration_by_parts {g : Reference.Space n → ℝ}
    (hg : Differentiable ℝ g) (v : Reference.Space n)
    (hgi : Integrable g (standardGaussian n))
    (hdgi : Integrable (fun x ↦ fderiv ℝ g x v) (standardGaussian n))
    (hxgi : Integrable (fun x ↦ ⟪x, v⟫_ℝ * g x) (standardGaussian n)) :
    (∫ x, fderiv ℝ g x v ∂standardGaussian n) =
      ∫ x, ⟪x, v⟫_ℝ * g x ∂standardGaussian n := by
  have hfg := (integrable_standardGaussian_iff g).mp hgi
  have hdfg := (integrable_standardGaussian_iff _).mp hdgi
  have hxfd := (integrable_standardGaussian_iff _).mp hxgi
  have hfg' : Integrable (fun x ↦ g x * fderiv ℝ (gaussianKernel n) x v) := by
    simp_rw [gaussianKernel_fderiv_apply]
    convert hxfd.neg using 1
    ext x
    simp only [Pi.neg_apply]
    ring
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hdfg hfg' hfg hg (fun x ↦ (gaussianKernel_hasFDerivAt x).differentiableAt)
  simp_rw [gaussianKernel_fderiv_apply] at h
  have heq : (fun x ↦ g x * (-⟪x, v⟫_ℝ * gaussianKernel n x)) =
      (fun x ↦ -((⟪x, v⟫_ℝ * g x) * gaussianKernel n x)) := by ext x; ring
  rw [heq, integral_neg, neg_inj] at h
  rw [integral_standardGaussian, integral_standardGaussian]
  exact congrArg (fun r : ℝ ↦ r / ∫ x, gaussianKernel n x) h.symm

/-- Compactly supported `C¹` test functions automatically satisfy every
integrability condition in the Gaussian integration-by-parts identity. -/
theorem standardGaussian_integration_by_parts_compact {g : Reference.Space n → ℝ}
    (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) (v : Reference.Space n) :
    (∫ x, fderiv ℝ g x v ∂standardGaussian n) =
      ∫ x, ⟪x, v⟫_ℝ * g x ∂standardGaussian n := by
  apply standardGaussian_integration_by_parts (hg.differentiable le_rfl) v
  · exact hg.continuous.integrable_of_hasCompactSupport hs
  · exact ((hg.continuous_fderiv le_rfl).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ v)
  · exact ((continuous_id.inner continuous_const).mul hg.continuous).integrable_of_hasCompactSupport
      hs.mul_left

/-- Every positive Gaussian radial kernel is integrable; the proof uses the
explicit finite-dimensional Gaussian integral. -/
lemma exp_neg_norm_sq_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Reference.Space n ↦ Real.exp (-b * ‖x‖ ^ 2)) := by
  by_contra h
  have hi := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Reference.Space n) hb
  rw [integral_undef h] at hi
  have hp : 0 < (Real.pi / b) ^ ((Module.finrank ℝ (Reference.Space n) : ℝ) / 2) := by
    positivity
  linarith

lemma norm_sq_mul_gaussianKernel_le (x : Reference.Space n) :
    ‖x‖ ^ 2 * gaussianKernel n x ≤
      4 * Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2) := by
  have he : ‖x‖ ^ 2 / 4 ≤ Real.exp (‖x‖ ^ 2 / 4) := by
    linarith [Real.add_one_le_exp (‖x‖ ^ 2 / 4)]
  have hm := mul_le_mul_of_nonneg_right he
    (Real.exp_nonneg (-(1 / 2 : ℝ) * ‖x‖ ^ 2))
  rw [← Real.exp_add] at hm
  have heq : ‖x‖ ^ 2 / 4 + -(1 / 2 : ℝ) * ‖x‖ ^ 2 = -(1 / 4 : ℝ) * ‖x‖ ^ 2 := by ring
  rw [heq] at hm
  dsimp [gaussianKernel]
  nlinarith

/-- Gaussian second moments are genuinely finite. -/
lemma standardGaussian_norm_sq_integrable (n : ℕ) :
    Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) (standardGaussian n) := by
  apply (integrable_standardGaussian_iff _).mpr
  apply ((exp_neg_norm_sq_integrable (n := n)
    (show (0 : ℝ) < 1 / 4 by norm_num)).const_mul 4).mono' (by
      unfold gaussianKernel
      fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ ‖x‖ ^ 2 * gaussianKernel n x by
    unfold gaussianKernel; positivity)]
  exact norm_sq_mul_gaussianKernel_le x

lemma standardGaussian_norm_integrable (n : ℕ) :
    Integrable (fun x : Reference.Space n ↦ ‖x‖) (standardGaussian n) := by
  apply ((integrable_const (1 : ℝ)).add (standardGaussian_norm_sq_integrable n)).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  simp only [norm_norm, Pi.add_apply]
  nlinarith [sq_nonneg (‖x‖ - 1)]

/-- Bounded continuous functions are integrable for the normalized law. -/
lemma standardGaussian_integrable_of_bound {g : Reference.Space n → ℝ}
    (hg : Continuous g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    Integrable g (standardGaussian n) :=
  (integrable_const C).mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- Bounded derivatives have integrable Gaussian directional moments. -/
lemma standardGaussian_inner_mul_integrable_of_bound {g : Reference.Space n → ℝ}
    (hg : Continuous g) {C : ℝ} (hbound : ∀ x, |g x| ≤ C)
    (v : Reference.Space n) :
    Integrable (fun x ↦ ⟪x, v⟫_ℝ * g x) (standardGaussian n) := by
  apply ((standardGaussian_norm_integrable n).const_mul (‖v‖ * C)).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    |⟪x, v⟫_ℝ| * |g x| ≤ (‖x‖ * ‖v‖) * C :=
      mul_le_mul (abs_real_inner_le_norm _ _) (hbound x) (abs_nonneg _) (by positivity)
    _ = (‖v‖ * C) * ‖x‖ := by ring

end GaussianTilt.Paouris
