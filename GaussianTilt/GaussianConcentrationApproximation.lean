import GaussianTilt.GaussianConcentrationSmooth
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Smooth approximation preserving the Lipschitz constant

Normalized nonnegative compactly supported mollifiers approximate a globally
Lipschitz function uniformly, without increasing its Lipschitz constant.
This permits the genuinely proved smooth Gaussian concentration estimate to
pass to all Lipschitz observables, including norms.
-/
noncomputable section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace Convolution
namespace GaussianTilt.Paouris
variable {n : ℕ}

/-- Normalized compactly supported convolution used in concentration. -/
def gaussianMollify (φ : ContDiffBump (0 : Reference.Space n))
    (f : Reference.Space n → ℝ) : Reference.Space n → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] f

lemma gaussianMollify_contDiff (φ : ContDiffBump (0 : Reference.Space n))
    {f : Reference.Space n → ℝ} (hf : Continuous f) :
    ContDiff ℝ 1 (gaussianMollify φ f) := by
  exact φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed hf.locallyIntegrable

lemma gaussianMollify_integrable (φ : ContDiffBump (0 : Reference.Space n))
    {f : Reference.Space n → ℝ} (hf : Continuous f) (x : Reference.Space n) :
    Integrable (fun y ↦ φ.normed volume y * f (x - y)) := by
  exact φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
    φ.continuous_normed hf.locallyIntegrable x

lemma gaussianMollify_lipschitz (φ : ContDiffBump (0 : Reference.Space n))
    {f : Reference.Space n → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (gaussianMollify φ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, gaussianMollify, convolution_def, convolution_def]
  simp only [lsmul_apply, smul_eq_mul]
  rw [← integral_sub (gaussianMollify_integrable φ hf.continuous x)
      (gaussianMollify_integrable φ hf.continuous y)]
  have h := norm_integral_le_of_norm_le
    (f := fun z ↦ φ.normed volume z * f (x - z) - φ.normed volume z * f (y - z)) ((φ.integrable_normed (μ := volume)).mul_const
    ((K : ℝ) * dist x y)) (Filter.Eventually.of_forall (fun z ↦ ?_))
  · simpa only [integral_mul_const, φ.integral_normed, one_mul] using h
  · simp only [← mul_sub, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (φ.nonneg_normed z)]
    apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed z)
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hf.dist_le_mul (x - z) (y - z)

lemma gaussianMollify_dist_le (φ : ContDiffBump (0 : Reference.Space n))
    {f : Reference.Space n → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (x : Reference.Space n) :
    dist (gaussianMollify φ f x) (f x) ≤ K * φ.rOut := by
  apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left hy.le K.coe_nonneg)

/-- Every globally Lipschitz function admits uniformly close smooth
approximations with precisely the same global Lipschitz constant. -/
theorem exists_contDiff_lipschitz_uniform_approximation
    {f : Reference.Space n → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Reference.Space n → ℝ, ContDiff ℝ 1 g ∧ LipschitzWith K g ∧
      ∀ x, dist (g x) (f x) ≤ ε := by
  let r := ε / (K + 1)
  have hr : 0 < r := div_pos hε (by positivity)
  let φ : ContDiffBump (0 : Reference.Space n) :=
    ⟨r / 2, r, by positivity, by linarith⟩
  refine ⟨gaussianMollify φ f, gaussianMollify_contDiff φ hf.continuous,
    gaussianMollify_lipschitz φ hf, fun x ↦ (gaussianMollify_dist_le φ hf x).trans ?_⟩
  change (K : ℝ) * (ε / (K + 1)) ≤ ε
  have hd : 0 < (K : ℝ) + 1 := by positivity
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hd).mpr
  nlinarith

end GaussianTilt.Paouris
