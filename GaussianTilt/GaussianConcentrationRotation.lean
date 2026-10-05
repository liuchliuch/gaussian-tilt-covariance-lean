import GaussianTilt.GaussianConcentrationMgf
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris
variable {n : ℕ}

/-- The simultaneous rotation of a pair of independent Gaussian vectors. -/
def gaussianPairRotation (t : ℝ) (z : Reference.Space n × Reference.Space n) :=
  (Real.cos t • z.1 + Real.sin t • z.2,
   -Real.sin t • z.1 + Real.cos t • z.2)

lemma gaussianPairRotation_norm_sq (t : ℝ) (z : Reference.Space n × Reference.Space n) :
    ‖(gaussianPairRotation t z).1‖ ^ 2 + ‖(gaussianPairRotation t z).2‖ ^ 2 =
      ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  dsimp [gaussianPairRotation]
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right, neg_mul, neg_sq]
  linear_combination (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) * Real.sin_sq_add_cos_sq t

/-- Pair rotation as an actual linear isometry of the Euclidean product. -/
def gaussianPairRotationIsometry (t : ℝ) :
    WithLp 2 (Reference.Space n × Reference.Space n) ≃ₗᵢ[ℝ]
      WithLp 2 (Reference.Space n × Reference.Space n) where
  toFun z := WithLp.toLp 2 (gaussianPairRotation t z.ofLp)
  invFun z := WithLp.toLp 2 (gaussianPairRotation (-t) z.ofLp)
  left_inv z := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext <;> ext i <;>
      simp [gaussianPairRotation] <;>
      first
      | linear_combination (z.fst i) * Real.sin_sq_add_cos_sq t
      | linear_combination (z.snd i) * Real.sin_sq_add_cos_sq t
  right_inv z := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext <;> ext i <;>
      simp [gaussianPairRotation] <;>
      first
      | linear_combination (z.fst i) * Real.sin_sq_add_cos_sq t
      | linear_combination (z.snd i) * Real.sin_sq_add_cos_sq t
  map_add' z w := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext <;> ext i <;> simp [gaussianPairRotation] <;> ring
  map_smul' c z := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext <;> ext i <;> simp [gaussianPairRotation] <;> ring
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [WithLp.prod_norm_sq_eq_of_L2, WithLp.ofLp_toLp] using
      gaussianPairRotation_norm_sq t z.ofLp

/-- Lebesgue measure on the product is invariant under simultaneous rotation.
The proof transfers to the Euclidean product norm and uses uniqueness of Haar
measure; no determinant formula or Gaussian comparison assumption is needed. -/
lemma integral_gaussianPairRotation_volume (t : ℝ)
    (f : Reference.Space n × Reference.Space n → ℝ) :
    (∫ z, f (gaussianPairRotation t z) ∂(volume.prod volume)) =
      ∫ z, f z ∂(volume.prod volume) := by
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ
    (Reference.Space n) (Reference.Space n)).symm
  let μ : Measure (Reference.Space n × Reference.Space n) := volume.prod volume
  let ν := μ.map e
  haveI : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hν := Measure.isAddLeftInvariant_eq_smul ν volume
  have hpres : MeasurePreserving (gaussianPairRotationIsometry (n := n) t) ν ν := by
    rw [hν]
    exact (gaussianPairRotationIsometry (n := n) t).measurePreserving.smul_measure _
  have hi := hpres.integral_comp'
    (f := (gaussianPairRotationIsometry (n := n) t).toMeasurableEquiv)
    (fun z ↦ f (e.symm z))
  rw [show ν = μ.map e.toHomeomorph.toMeasurableEquiv from rfl,
    integral_map_equiv, integral_map_equiv] at hi
  simpa only [e, μ, gaussianPairRotationIsometry, WithLp.prodContinuousLinearEquiv_apply,
    WithLp.prodContinuousLinearEquiv_symm_apply, WithLp.ofLp_toLp] using hi

lemma integral_standardGaussian_prod (f : Reference.Space n × Reference.Space n → ℝ) :
    (∫ z, f z ∂((standardGaussian n).prod (standardGaussian n))) =
      (∫ z, f z * (gaussianKernel n z.1 * gaussianKernel n z.2) ∂(volume.prod volume)) /
        (∫ x, gaussianKernel n x) ^ 2 := by
  rw [standardGaussian, prod_withDensity
    ((standardGaussianDensity_continuous n).measurable.ennreal_ofReal)
    ((standardGaussianDensity_continuous n).measurable.ennreal_ofReal)]
  have hm : Measurable (fun z : Reference.Space n × Reference.Space n ↦
      ENNReal.ofReal (standardGaussianDensity n z.1) *
      ENNReal.ofReal (standardGaussianDensity n z.2)) :=
    ((standardGaussianDensity_continuous n).measurable.comp measurable_fst).ennreal_ofReal.mul
      ((standardGaussianDensity_continuous n).measurable.comp measurable_snd).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.mul_lt_top
      ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (standardGaussianDensity_pos _).le]
  rw [← integral_div]
  congr 1
  ext z
  simp only [smul_eq_mul, standardGaussianDensity]
  ring

lemma gaussianKernel_prod_rotation (t : ℝ)
    (z : Reference.Space n × Reference.Space n) :
    gaussianKernel n (gaussianPairRotation t z).1 *
      gaussianKernel n (gaussianPairRotation t z).2 =
      gaussianKernel n z.1 * gaussianKernel n z.2 := by
  unfold gaussianKernel
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  nlinarith [gaussianPairRotation_norm_sq t z]

/-- Joint standard Gaussian law is invariant under simultaneous rotation.
This is the independence/rotation step in Pisier's concentration argument. -/
theorem integral_gaussianPairRotation (t : ℝ)
    (f : Reference.Space n × Reference.Space n → ℝ) :
    (∫ z, f (gaussianPairRotation t z) ∂((standardGaussian n).prod (standardGaussian n))) =
      ∫ z, f z ∂((standardGaussian n).prod (standardGaussian n)) := by
  rw [integral_standardGaussian_prod, integral_standardGaussian_prod]
  congr 1
  have hi := integral_gaussianPairRotation_volume t
    (fun z ↦ f z * (gaussianKernel n z.1 * gaussianKernel n z.2))
  simpa only [gaussianKernel_prod_rotation] using hi

lemma gaussianPairRotation_continuous (t : ℝ) :
    Continuous (gaussianPairRotation (n := n) t) := by
  unfold gaussianPairRotation
  fun_prop

/-- The Gaussian rotation identity as a measure-preserving transformation. -/
theorem gaussianPairRotation_measurePreserving (t : ℝ) :
    MeasurePreserving (gaussianPairRotation (n := n) t)
      ((standardGaussian n).prod (standardGaussian n))
      ((standardGaussian n).prod (standardGaussian n)) := by
  refine ⟨(gaussianPairRotation_continuous t).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hi := integral_gaussianPairRotation t (s.indicator (fun _ ↦ (1 : ℝ)))
  rw [← integral_map (gaussianPairRotation_continuous t).measurable.aemeasurable
    ((measurable_const.indicator hs).aestronglyMeasurable),
    integral_indicator_const _ hs, integral_indicator_const _ hs] at hi
  simpa only [smul_eq_mul, mul_one] using hi

end GaussianTilt.Paouris
