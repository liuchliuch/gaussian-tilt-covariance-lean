import GaussianTilt.MomentMapIsotropicApproximation
import GaussianTilt.PaperResults

/-! # Genuine vanishing quadratic tilts of regular approximants

The quadratic coefficient is strictly positive for every index. All limiting
moments below are proved on the original independent product probability space.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped Topology ENNReal BigOperators Matrix.Norms.L2Operator
namespace GaussianTilt.MomentMapApproximation
open Paouris Whitening
variable {n : ℕ}

def tiltScale (k : ℕ) : ℝ := (((k : ℝ) + 1)⁻¹) ^ 4

def tiltWeight (k : ℕ) (x : Reference.Space n) : ℝ :=
  Real.exp (-tiltScale k * ‖x‖ ^ 2)

def strongTruncation (μ : Measure (Reference.Space n)) (k : ℕ) : Measure (Reference.Space n) :=
  Reference.gaussianTilt (perturbedTruncation μ (standardGaussian n) k) (tiltScale k)

lemma tiltScale_pos (k : ℕ) : 0 < tiltScale k := by unfold tiltScale; positivity

lemma tiltScale_tendsto : Tendsto tiltScale atTop (𝓝 0) := by
  have hi : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  simpa only [tiltScale, zero_pow (by norm_num : 4 ≠ 0)] using hi.pow 4

lemma continuous_tiltWeight (k : ℕ) : Continuous (tiltWeight (n := n) k) := by
  unfold tiltWeight
  fun_prop

lemma tiltWeight_pos (k : ℕ) (x : Reference.Space n) : 0 < tiltWeight k x := Real.exp_pos _

lemma tiltWeight_le_one (k : ℕ) (x : Reference.Space n) : tiltWeight k x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (tiltScale_pos k).le) (sq_nonneg _)

lemma tiltWeight_perturb_tendsto (p : Reference.Space n × Reference.Space n) :
    Tendsto (fun k => tiltWeight k (perturb k p)) atTop (𝓝 1) := by
  have h := Real.continuous_exp.continuousAt.tendsto.comp
    (tiltScale_tendsto.neg.mul ((tendsto_perturb p).norm.pow 2))
  simpa only [neg_zero, zero_mul, Real.exp_zero, tiltWeight] using h

instance strongTruncation_probability (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (k : ℕ) : IsProbabilityMeasure (strongTruncation μ k) :=
  Reference.gaussianTilt_probability _ (perturbedTruncation_compactlySupported μ (standardGaussian n) k) _

lemma strongTruncation_compactlySupported (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (k : ℕ) : Reference.compactlySupported (strongTruncation μ k) :=
  Reference.gaussianTilt_compactlySupported _
    (perturbedTruncation_compactlySupported μ (standardGaussian n) k) _

lemma integral_gaussianTilt {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (t : ℝ) (f : Reference.Space n → ℝ) :
    (∫ x, f x ∂(Reference.gaussianTilt μ t)) =
      (∫ x, Real.exp (-t * ‖x‖ ^ 2) * f x ∂μ) / Reference.partition μ t := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hc
  exact P.integral_tilt t f

/-- Weighted moving-affine observables converge before normalizing the tilt. -/
theorem weighted_affine_integral_tendsto
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ)
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {m : ℕ → Reference.Space n}
    (hA : Tendsto A atTop (𝓝 1)) (hm : Tendsto m atTop (𝓝 0))
    {f : Reference.Space n → ℝ} (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ 4)) :
    Tendsto (fun k => ∫ x, tiltWeight k x * f (affineValue (A k) (m k) x)
      ∂perturbedTruncation μ (standardGaussian n) k) atTop (𝓝 (∫ x, f x ∂μ)) := by
  let ν := standardGaussian n
  have hν := standardGaussian_norm_fourth_integrable n
  let D : Reference.Space n × Reference.Space n → ℝ := fun p =>
    C * (1 + 16 * 8 * (8 * (‖p.1‖ ^ 4 + ‖p.2‖ ^ 4) + 1))
  have hiD : Integrable D (μ.prod ν) := by
    exact ((integrable_const 1).add
      ((((hμ.comp_fst ν).add (hν.comp_snd μ)).const_mul 8 |>.add (integrable_const 1)).const_mul
        (16 * 8))).const_mul C
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ.prod ν)
    (F := fun k => (truncationEvent k).indicator
      (fun p => tiltWeight k (perturb k p) * f (affineValue (A k) (m k) (perturb k p))))
    (f := fun p => f p.1) D
    (Eventually.of_forall (fun k =>
      (((continuous_tiltWeight k).comp (continuous_perturb k)).mul
        ((hf.comp (continuous_affineValue (A k) (m k))).comp (continuous_perturb k))).measurable.indicator
          (measurableSet_truncationEvent k) |>.aestronglyMeasurable))
    (by
      filter_upwards [eventually_affine_bounds hA hm] with k hk
      exact ae_of_all _ (fun p => by
        by_cases hp : p ∈ truncationEvent k
        · rw [indicator_of_mem hp, norm_mul, Real.norm_eq_abs,
            abs_of_pos (tiltWeight_pos _ _)]
          calc
            _ ≤ ‖f (affineValue (A k) (m k) (perturb k p))‖ :=
              mul_le_of_le_one_left (norm_nonneg _) (tiltWeight_le_one _ _)
            _ ≤ D p := (hbound _).trans (mul_le_mul_of_nonneg_left
              (add_le_add_left (affine_perturb_fourth_bound hk.1 hk.2 k p) 1) hC)
        · rw [indicator_of_notMem hp, norm_zero]
          dsimp [D]
          positivity)) hiD
    (ae_of_all _ (fun p => by
      have hl := (tiltWeight_perturb_tendsto p).mul
        (hf.continuousAt.tendsto.comp (affineValue_tendsto hA hm (tendsto_perturb p)))
      simp only [one_mul] at hl
      apply hl.congr'
      filter_upwards [eventually_mem_truncationEvent p] with k hk
      simp only [indicator_of_mem hk, Function.comp_apply]))
  have hi : Integrable f μ := ((integrable_const 1).add hμ |>.const_mul C).mono'
    hf.aestronglyMeasurable (ae_of_all _ hbound)
  have hprod : (∫ p : Reference.Space n × Reference.Space n, f p.1 ∂μ.prod ν) = ∫ x, f x ∂μ := by
    rw [integral_prod _ (hi.comp_fst ν)]
    simp
  rw [hprod] at ht
  have hd := ht.div (tendsto_truncation_mass μ ν) (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun k => (∫ p, (truncationEvent k).indicator
    (fun q => tiltWeight k (perturb k q) * f (affineValue (A k) (m k) (perturb k q))) p ∂μ.prod ν) /
      (μ.prod ν (truncationEvent k)).toReal) atTop (𝓝 ((∫ x, f x ∂μ) / 1)) at hd
  simp only [div_one] at hd
  apply hd.congr'
  exact Eventually.of_forall (fun k =>
    (integral_perturbedTruncation μ ν k
      ((continuous_tiltWeight k).mul (hf.comp (continuous_affineValue (A k) (m k)))).measurable).symm)

lemma tiltPartition_tendsto (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ) :
    Tendsto (fun k => Reference.partition (perturbedTruncation μ (standardGaussian n) k) (tiltScale k))
      atTop (𝓝 1) := by
  have h := weighted_affine_integral_tendsto μ hμ
    (A := fun _ => 1) (m := fun _ => 0) tendsto_const_nhds tendsto_const_nhds
    (f := fun _ => 1) continuous_const (C := 1) (by norm_num) (fun x => by simp)
  simpa only [tiltWeight, mul_one, integral_const, measureReal_univ_eq_one, one_smul,
    Reference.partition] using h

/-- Actual Gaussian-tilted and normalized moving-affine moments converge. -/
theorem integral_affine_strongTruncation_tendsto
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ)
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {m : ℕ → Reference.Space n}
    (hA : Tendsto A atTop (𝓝 1)) (hm : Tendsto m atTop (𝓝 0))
    {f : Reference.Space n → ℝ} (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ 4)) :
    Tendsto (fun k => ∫ x, f (affineValue (A k) (m k) x) ∂strongTruncation μ k)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  have h := (weighted_affine_integral_tendsto μ hμ hA hm hf hC hbound).div
    (tiltPartition_tendsto μ hμ) (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  apply h.congr'
  exact Eventually.of_forall (fun k => (integral_gaussianTilt
    (perturbedTruncation_compactlySupported μ (standardGaussian n) k) (tiltScale k) _).symm)

lemma integral_strongTruncation_tendsto
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ)
    {f : Reference.Space n → ℝ} (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ 4)) :
    Tendsto (fun k => ∫ x, f x ∂strongTruncation μ k) atTop (𝓝 (∫ x, f x ∂μ)) := by
  simpa only [affineValue, sub_zero, map_one, ContinuousLinearMap.one_apply] using
    integral_affine_strongTruncation_tendsto μ hμ (A := fun _ => 1) (m := fun _ => 0)
      tendsto_const_nhds tendsto_const_nhds hf hC hbound

end GaussianTilt.MomentMapApproximation
