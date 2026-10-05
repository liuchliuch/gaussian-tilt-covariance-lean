import GaussianTilt.NegativeSobolevClosure

/-! # Actual compact mollification on Lebesgue L² -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal Convolution
namespace GaussianTilt.Letwin

/-- Scalar convolution with respect to actual coordinate Lebesgue measure. -/
def scalarConvolution {n : ℕ} (ρ f : CoordinateSpace n → ℝ) : CoordinateSpace n → ℝ :=
  convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- The measure associated to a nonnegative convolution kernel. -/
def kernelMeasure {n : ℕ} (ρ : CoordinateSpace n → ℝ) : Measure (CoordinateSpace n) :=
  volume.withDensity (fun x => ENNReal.ofReal (ρ x))

lemma integral_kernelMeasure {n : ℕ} {ρ : CoordinateSpace n → ℝ}
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (f : CoordinateSpace n → ℝ) :
    (∫ x, f x ∂kernelMeasure ρ) = ∫ x, ρ x * f x := by
  rw [kernelMeasure, integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (hρ0 _), smul_eq_mul]
  · exact hρ.measurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

lemma integrable_kernelMeasure_iff {n : ℕ} {ρ : CoordinateSpace n → ℝ}
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (f : CoordinateSpace n → ℝ) :
    Integrable f (kernelMeasure ρ) ↔ Integrable (fun x => ρ x * f x) := by
  simpa only [kernelMeasure, ENNReal.toReal_ofReal (hρ0 _), smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (g := f))

lemma kernelMeasure_probability {n : ℕ} {ρ : CoordinateSpace n → ℝ}
    (hρi : Integrable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : (∫ x, ρ x) = 1) :
    IsProbabilityMeasure (kernelMeasure ρ) := by
  constructor
  rw [kernelMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hρi (Filter.Eventually.of_forall hρ0), hρ1]
  norm_num

lemma memLp_sub_left {n : ℕ} {f : CoordinateSpace n → ℝ} (hf : MemLp f 2 volume)
    (x : CoordinateSpace n) : MemLp (fun y => f (x - y)) 2 volume := by
  apply (memLp_two_iff_integrable_sq (hf.1.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_sub_left_of_right_invariant volume x))).2
  exact hf.integrable_sq.comp_sub_left x

lemma memLp_kernelMeasure_sub_left {n : ℕ} {ρ f : CoordinateSpace n → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hf : MemLp f 2 volume) (x : CoordinateSpace n) :
    MemLp (fun y => f (x - y)) 2 (kernelMeasure ρ) := by
  have ht := memLp_sub_left hf x
  have hm : AEStronglyMeasurable (fun y => f (x-y)) (kernelMeasure ρ) :=
    AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous volume _) ht.1
  apply (memLp_two_iff_integrable_sq hm).2
  rw [integrable_kernelMeasure_iff hρ hρ0]
  simpa only [smul_eq_mul] using
    ht.integrable_sq.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hρ hρc

/-- Pointwise Jensen for actual convolution, proved via the actual normalized
kernel measure. All L² and weighted-integrability obligations are discharged. -/
theorem scalarConvolution_sq_le {n : ℕ} {ρ f : CoordinateSpace n → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : (∫ x, ρ x) = 1) (hf : MemLp f 2 volume) (x : CoordinateSpace n) :
    (scalarConvolution ρ f x)^2 ≤ scalarConvolution ρ (fun y => (f y)^2) x := by
  letI := kernelMeasure_probability (hρ.integrable_of_hasCompactSupport hρc) hρ0 hρ1
  have hvar := variance_nonneg (fun y => f (x-y)) (kernelMeasure ρ)
  rw [variance_eq_sub (memLp_kernelMeasure_sub_left hρ hρc hρ0 hf x)] at hvar
  simp only [Pi.pow_apply, integral_kernelMeasure hρ hρ0] at hvar
  change (∫ y, ρ y * f (x-y))^2 ≤ ∫ y, ρ y * (f (x-y))^2
  linarith

lemma scalarConvolution_continuous {n : ℕ} {ρ f : CoordinateSpace n → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hf : MemLp f 2 volume) :
    Continuous (scalarConvolution ρ f) :=
  hρc.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ
    (hf.locallyIntegrable (by norm_num))

/-- Actual compact nonnegative normalized convolution preserves L². -/
theorem scalarConvolution_memLp {n : ℕ} {ρ f : CoordinateSpace n → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : (∫ x, ρ x) = 1) (hf : MemLp f 2 volume) :
    MemLp (scalarConvolution ρ f) 2 volume := by
  apply (memLp_two_iff_integrable_sq (scalarConvolution_continuous hρ hρc hf).aestronglyMeasurable).2
  have hi := (hρ.integrable_of_hasCompactSupport hρc).integrable_convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) hf.integrable_sq
  apply hi.mono' ((scalarConvolution_continuous hρ hρc hf).pow 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact scalarConvolution_sq_le hρ hρc hρ0 hρ1 hf x

/-- The genuine L² contraction estimate for an actual normalized mollifier. -/
theorem integral_scalarConvolution_sq_le {n : ℕ} {ρ f : CoordinateSpace n → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : (∫ x, ρ x) = 1) (hf : MemLp f 2 volume) :
    (∫ x, (scalarConvolution ρ f x)^2) ≤ ∫ x, (f x)^2 := by
  have hρi : Integrable ρ volume := hρ.integrable_of_hasCompactSupport hρc
  have hi := hρi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf.integrable_sq
  calc
    _ ≤ ∫ x, scalarConvolution ρ (fun y => (f y)^2) x :=
      integral_mono (scalarConvolution_memLp hρ hρc hρ0 hρ1 hf).integrable_sq hi
        (scalarConvolution_sq_le hρ hρc hρ0 hρ1 hf)
    _ = _ := by
      rw [scalarConvolution, integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hρi hf.integrable_sq,
        hρ1]
      simp

end GaussianTilt.Letwin
