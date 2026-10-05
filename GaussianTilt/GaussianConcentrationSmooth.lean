import GaussianTilt.GaussianConcentrationRotation
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Pisier's rotation argument

The proof connects two independent Gaussian points by a quarter-circle,
applies the fundamental theorem of calculus and Jensen's inequality, and
then uses Gaussian rotation invariance and the exact linear exponential
moment. The resulting constant is universal and independent of dimension.
-/
noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace
namespace GaussianTilt.Paouris
variable {n : ℕ}

/-- Uniform probability measure on the unit interval. -/
def gaussianRotationTime : Measure ℝ := volume.restrict (Icc 0 1)

instance gaussianRotationTime_probability : IsProbabilityMeasure gaussianRotationTime := by
  constructor
  simp [gaussianRotationTime, Real.volume_Icc]

lemma integral_gaussianRotationTime (g : ℝ → ℝ) :
    (∫ t, g t ∂gaussianRotationTime) = ∫ t in (0 : ℝ)..1, g t := by
  rw [gaussianRotationTime, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num)]

/-- The scalar derivative integrand along the quarter-circle. -/
def gaussianRotationDerivative (f : Reference.Space n → ℝ) (s t : ℝ)
    (z : Reference.Space n × Reference.Space n) : ℝ :=
  s * (Real.pi / 2) *
    fderiv ℝ f (gaussianPairRotation (Real.pi / 2 * t) z).1
      (gaussianPairRotation (Real.pi / 2 * t) z).2

lemma gaussianRotationDerivative_continuous {f : Reference.Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (s : ℝ) :
    Continuous (fun w : ℝ × (Reference.Space n × Reference.Space n) ↦
      gaussianRotationDerivative f s w.1 w.2) := by
  unfold gaussianRotationDerivative gaussianPairRotation
  exact continuous_const.mul ((hf.continuous_fderiv le_rfl).comp
    ((Real.continuous_cos.comp (continuous_const.mul continuous_fst)).smul
      continuous_snd.fst |>.add
      ((Real.continuous_sin.comp (continuous_const.mul continuous_fst)).smul
        continuous_snd.snd)) |>.clm_apply
        (((Real.continuous_sin.comp (continuous_const.mul continuous_fst)).neg.smul
          continuous_snd.fst).add
          ((Real.continuous_cos.comp (continuous_const.mul continuous_fst)).smul
            continuous_snd.snd)))

lemma gaussianRotationDerivative_hasDerivAt {f : Reference.Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (s t : ℝ) (z : Reference.Space n × Reference.Space n) :
    HasDerivAt (fun r ↦ s * f (gaussianPairRotation (Real.pi / 2 * r) z).1)
      (gaussianRotationDerivative f s t z) t := by
  have hangle : HasDerivAt (fun r : ℝ ↦ Real.pi / 2 * r) (Real.pi / 2) t := by
    simpa using (hasDerivAt_id t).const_mul (Real.pi / 2)
  have hpath := (hangle.cos.smul_const z.1).add (hangle.sin.smul_const z.2)
  have hh := (((hf.differentiable le_rfl _).hasFDerivAt).comp_hasDerivAt t hpath).const_mul s
  convert hh using 1
  unfold gaussianRotationDerivative gaussianPairRotation
  simp only [map_add, map_smul, smul_eq_mul, Pi.add_apply]
  ring

lemma integral_gaussianRotationDerivative {f : Reference.Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (s : ℝ) (z : Reference.Space n × Reference.Space n) :
    (∫ t, gaussianRotationDerivative f s t z ∂gaussianRotationTime) =
      s * (f z.2 - f z.1) := by
  rw [integral_gaussianRotationTime]
  have hdf := hf.continuous_fderiv le_rfl
  have hc : Continuous (fun t ↦ gaussianRotationDerivative f s t z) := by
    unfold gaussianRotationDerivative gaussianPairRotation
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ gaussianRotationDerivative_hasDerivAt hf s t z)
    (hc.intervalIntegrable 0 1)
  simpa [gaussianPairRotation, mul_sub] using hi

/-- Jensen's inequality along the real quarter-circle, before any Gaussian
integration. -/
theorem gaussian_rotation_exp_difference_le {f : Reference.Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (s : ℝ) (z : Reference.Space n × Reference.Space n) :
    Real.exp (s * (f z.2 - f z.1)) ≤
      ∫ t, Real.exp (gaussianRotationDerivative f s t z) ∂gaussianRotationTime := by
  have hdf := hf.continuous_fderiv le_rfl
  have hc : Continuous (fun t ↦ gaussianRotationDerivative f s t z) := by
    unfold gaussianRotationDerivative gaussianPairRotation
    fun_prop
  have h := convexOn_exp.map_integral_le (μ := gaussianRotationTime)
    (f := fun t ↦ gaussianRotationDerivative f s t z)
    Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ ↦ mem_univ _)
    hc.integrableOn_Icc (Real.continuous_exp.comp hc).integrableOn_Icc
  rwa [integral_gaussianRotationDerivative hf s z] at h

lemma gaussianPairRotation_snd_norm_le (t : ℝ)
    (z : Reference.Space n × Reference.Space n) :
    ‖(gaussianPairRotation t z).2‖ ≤ ‖z.1‖ + ‖z.2‖ := by
  dsimp [gaussianPairRotation]
  calc
    _ ≤ ‖-Real.sin t • z.1‖ + ‖Real.cos t • z.2‖ := norm_add_le _ _
    _ = |Real.sin t| * ‖z.1‖ + |Real.cos t| * ‖z.2‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_neg]
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (norm_nonneg z.1),
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t) (norm_nonneg z.2)]

lemma gaussianRotationDerivative_abs_le {f : Reference.Space n → ℝ}
    {K : ℝ≥0} (hlip : LipschitzWith K f) (s t : ℝ)
    (z : Reference.Space n × Reference.Space n) :
    |gaussianRotationDerivative f s t z| ≤
      (|s * (Real.pi / 2)| * K) * (‖z.1‖ + ‖z.2‖) := by
  unfold gaussianRotationDerivative
  rw [abs_mul]
  have h := (fderiv ℝ f (gaussianPairRotation (Real.pi / 2 * t) z).1).le_opNorm
    (gaussianPairRotation (Real.pi / 2 * t) z).2
  have h' : |fderiv ℝ f (gaussianPairRotation (Real.pi / 2 * t) z).1
      (gaussianPairRotation (Real.pi / 2 * t) z).2| ≤
      (K : ℝ) * (‖z.1‖ + ‖z.2‖) := by
    exact h.trans (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hlip)
      (gaussianPairRotation_snd_norm_le _ z) (norm_nonneg _) K.coe_nonneg)
  exact (mul_le_mul_of_nonneg_left h' (abs_nonneg _)).trans_eq (by ring)

lemma gaussianRotation_exp_integrable {f : Reference.Space n → ℝ}
    (hf : ContDiff ℝ 1 f) {K : ℝ≥0} (hlip : LipschitzWith K f) (s : ℝ) :
    Integrable (fun w : ℝ × (Reference.Space n × Reference.Space n) ↦
      Real.exp (gaussianRotationDerivative f s w.1 w.2))
      (gaussianRotationTime.prod ((standardGaussian n).prod (standardGaussian n))) := by
  let c := |s * (Real.pi / 2)| * K
  have hg := (standardGaussian_exp_norm_integrable (n := n) c).mul_prod
    (standardGaussian_exp_norm_integrable (n := n) c)
  have hg' := (integrable_const (1 : ℝ) (μ := gaussianRotationTime)).mul_prod hg
  apply hg'.mono' ((Real.continuous_exp.comp
    (gaussianRotationDerivative_continuous hf s)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro w
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans ((gaussianRotationDerivative_abs_le hlip s w.1 w.2).trans_eq
    (by dsimp [c]; ring))

lemma standardGaussian_exp_fderiv_integrable {f : Reference.Space n → ℝ}
    (hf : ContDiff ℝ 1 f) {K : ℝ≥0} (hlip : LipschitzWith K f) (a : ℝ) :
    Integrable (fun z : Reference.Space n × Reference.Space n ↦
      Real.exp (a * fderiv ℝ f z.1 z.2))
      ((standardGaussian n).prod (standardGaussian n)) := by
  have hg := (integrable_const (1 : ℝ) (μ := standardGaussian n)).mul_prod
    (standardGaussian_exp_norm_integrable (n := n) (|a| * K))
  have hdf := hf.continuous_fderiv le_rfl
  apply hg.mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro z
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
  apply Real.exp_le_exp.mpr
  have h := (fderiv ℝ f z.1).le_opNorm z.2
  have h' := mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := z.1)) (norm_nonneg z.2)
  have h'' := mul_le_mul_of_nonneg_left (h.trans h') (abs_nonneg a)
  rw [Real.norm_eq_abs] at h''
  have hab : a * fderiv ℝ f z.1 z.2 ≤ |a| * |fderiv ℝ f z.1 z.2| := by
    rw [← abs_mul]; exact le_abs_self _
  nlinarith

lemma standardGaussian_integral_exp_fderiv_le {f : Reference.Space n → ℝ}
    (hf : ContDiff ℝ 1 f) {K : ℝ≥0} (hlip : LipschitzWith K f) (a : ℝ) :
    (∫ z : Reference.Space n × Reference.Space n,
      Real.exp (a * fderiv ℝ f z.1 z.2) ∂((standardGaussian n).prod (standardGaussian n))) ≤
      Real.exp ((a * K) ^ 2 / 2) := by
  have hi := standardGaussian_exp_fderiv_integrable hf hlip a
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _ : Reference.Space n, Real.exp ((a * K) ^ 2 / 2) ∂standardGaussian n := by
      apply integral_mono hi.integral_prod_left (integrable_const _)
      intro x
      have he := standardGaussian_integral_exp_dual (a • fderiv ℝ f x)
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at he
      dsimp only
      rw [he]
      apply Real.exp_le_exp.mpr
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_pow]
      have hk := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := x)
      nlinarith [mul_le_mul_of_nonneg_left
        (sq_le_sq₀ (norm_nonneg _) K.coe_nonneg |>.mpr hk) (sq_nonneg a)]
    _ = _ := by simp

lemma standardGaussian_lipschitz_integrable {f : Reference.Space n → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) : Integrable f (standardGaussian n) := by
  apply (((standardGaussian_norm_integrable n).const_mul K).add
    (integrable_const |f 0|)).mono' hf.continuous.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have h := hf.norm_sub_le x 0
  simp only [sub_zero] at h
  exact (norm_le_norm_sub_add (f x) (f 0)).trans (by
    simpa only [Real.norm_eq_abs] using add_le_add_right h ‖f 0‖)

lemma standardGaussian_exp_difference_integrable {f : Reference.Space n → ℝ}
    {K : ℝ≥0} (hlip : LipschitzWith K f) (s : ℝ) :
    Integrable (fun z : Reference.Space n × Reference.Space n ↦
      Real.exp (s * (f z.2 - f z.1)))
      ((standardGaussian n).prod (standardGaussian n)) := by
  have h := (standardGaussian_exp_lipschitz_integrable hlip (-s)).mul_prod
    (standardGaussian_exp_lipschitz_integrable hlip s)
  convert h using 1
  ext z
  rw [← Real.exp_add]
  congr 1
  ring

/-- Pisier's dimension-free exponential bound for the difference of two
independent Gaussian copies of a smooth Lipschitz observable. -/
theorem standardGaussian_integral_exp_difference_le {f : Reference.Space n → ℝ}
    (hf : ContDiff ℝ 1 f) {K : ℝ≥0} (hlip : LipschitzWith K f) (s : ℝ) :
    (∫ z : Reference.Space n × Reference.Space n, Real.exp (s * (f z.2 - f z.1))
      ∂((standardGaussian n).prod (standardGaussian n))) ≤
      Real.exp ((s * (Real.pi / 2) * K) ^ 2 / 2) := by
  have hi := gaussianRotation_exp_integrable hf hlip s
  calc
    _ ≤ ∫ z, ∫ t, Real.exp (gaussianRotationDerivative f s t z)
        ∂gaussianRotationTime ∂((standardGaussian n).prod (standardGaussian n)) := by
      exact integral_mono (standardGaussian_exp_difference_integrable hlip s)
        hi.integral_prod_right (gaussian_rotation_exp_difference_le hf s)
    _ = ∫ t, ∫ z, Real.exp (gaussianRotationDerivative f s t z)
        ∂((standardGaussian n).prod (standardGaussian n)) ∂gaussianRotationTime :=
      (integral_integral_swap hi).symm
    _ ≤ ∫ _ : ℝ, Real.exp ((s * (Real.pi / 2) * K) ^ 2 / 2)
        ∂gaussianRotationTime := by
      apply integral_mono hi.integral_prod_left (integrable_const _)
      intro t
      have he := integral_gaussianPairRotation (Real.pi / 2 * t)
        (fun z ↦ Real.exp ((s * (Real.pi / 2)) * fderiv ℝ f z.1 z.2))
      change (∫ z, Real.exp (gaussianRotationDerivative f s t z)
        ∂((standardGaussian n).prod (standardGaussian n))) ≤ _
      rw [show (fun z ↦ Real.exp (gaussianRotationDerivative f s t z)) =
        (fun z ↦ Real.exp ((s * (Real.pi / 2)) *
          fderiv ℝ f (gaussianPairRotation (Real.pi / 2 * t) z).1
            (gaussianPairRotation (Real.pi / 2 * t) z).2)) from rfl, he]
      exact standardGaussian_integral_exp_fderiv_le hf hlip _
    _ = _ := by simp

lemma standardGaussian_exp_center_integrable {f : Reference.Space n → ℝ}
    {K : ℝ≥0} (hlip : LipschitzWith K f) (s : ℝ) :
    Integrable (fun x ↦ Real.exp (s * (f x - ∫ y, f y ∂standardGaussian n)))
      (standardGaussian n) := by
  have h := (standardGaussian_exp_lipschitz_integrable hlip s).const_mul
    (Real.exp (-s * ∫ y, f y ∂standardGaussian n))
  convert h using 1
  ext x
  rw [← Real.exp_add]
  congr 1
  ring

lemma gaussian_exp_center_le_difference {f : Reference.Space n → ℝ}
    {K : ℝ≥0} (hlip : LipschitzWith K f) (s : ℝ) (y : Reference.Space n) :
    Real.exp (s * (f y - ∫ x, f x ∂standardGaussian n)) ≤
      ∫ x, Real.exp (s * (f y - f x)) ∂standardGaussian n := by
  have hi := ((integrable_const (f y)).sub
    (standardGaussian_lipschitz_integrable hlip)).const_mul s
  have hei : Integrable (fun x ↦ Real.exp (s * (f y - f x))) (standardGaussian n) := by
    have h := (standardGaussian_exp_lipschitz_integrable hlip (-s)).const_mul
      (Real.exp (s * f y))
    convert h using 1
    ext x
    rw [← Real.exp_add]
    congr 1
    ring
  have h := convexOn_exp.map_integral_le (μ := standardGaussian n)
    (f := fun x ↦ s * (f y - f x))
    Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ ↦ mem_univ _) hi hei
  simpa only [integral_const_mul, integral_sub (integrable_const _)
    (standardGaussian_lipschitz_integrable hlip), integral_const,
    measureReal_univ_eq_one, smul_eq_mul, one_mul] using h

/-- A genuine centered Gaussian MGF bound, with universal variance proxy
`(π L / 2)²`, for every `C¹` globally Lipschitz observable. -/
theorem standardGaussian_integral_exp_center_le_of_contDiff {f : Reference.Space n → ℝ}
    (hf : ContDiff ℝ 1 f) {K : ℝ≥0} (hlip : LipschitzWith K f) (s : ℝ) :
    (∫ x, Real.exp (s * (f x - ∫ y, f y ∂standardGaussian n)) ∂standardGaussian n) ≤
      Real.exp ((s * (Real.pi / 2) * K) ^ 2 / 2) := by
  have hi := standardGaussian_exp_difference_integrable hlip s
  calc
    _ ≤ ∫ y, ∫ x, Real.exp (s * (f y - f x)) ∂standardGaussian n ∂standardGaussian n :=
      integral_mono (standardGaussian_exp_center_integrable hlip s)
        hi.integral_prod_right (gaussian_exp_center_le_difference hlip s)
    _ = ∫ z, Real.exp (s * (f z.2 - f z.1))
        ∂((standardGaussian n).prod (standardGaussian n)) := (integral_prod_symm _ hi).symm
    _ ≤ _ := standardGaussian_integral_exp_difference_le hf hlip s

end GaussianTilt.Paouris
