import GaussianTilt.BlockPrekopa
import GaussianTilt.Isotropization

/-! # Actual logconcave-density transport through linear equivalences -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace GaussianTilt.LinearImageDensity
open LogConcaveMarginal

lemma logconcave_const_mul {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {f : E → ℝ} (hf : IsLogConcave f) {c : ℝ} (hc : 0 < c) :
    IsLogConcave (fun x ↦ c * f x) := by
  apply IsLogConcave.mul _ hf
  refine ⟨fun _ ↦ hc.le, ?_⟩
  intro x y a b ha hb hab
  rw [← Real.rpow_add hc, hab, Real.rpow_one]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
  [SecondCountableTopology F]

/-- The Haar multiplier is derived from uniqueness, remains positive, and is
absorbed into the actual transported logconcave density. -/
theorem exists_density_map_linearEquiv (e : E ≃L[ℝ] F)
    (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {f : E → ℝ} (hf : IsLogConcave f) (hm : Measurable f) :
    ∃ c : ℝ, 0 < c ∧
      IsLogConcave (fun y ↦ c * f (e.symm y)) ∧
      Measurable (fun y ↦ c * f (e.symm y)) ∧
      Measure.map e (μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) =
        ν.withDensity (fun y ↦ ENNReal.ofReal (c * f (e.symm y))) := by
  letI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let c : NNReal := Measure.addHaarScalarFactor (Measure.map e μ) ν
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hc' : 0 < (c : ℝ) := by exact_mod_cast hc
  have hscale : Measure.map e μ = (c : ℝ≥0∞) • ν := Measure.isAddLeftInvariant_eq_smul _ _
  have hcomp : Measurable (fun y ↦ f (e.symm y)) := hm.comp e.symm.continuous.measurable
  refine ⟨c, hc', logconcave_const_mul
    (BlockPrekopa.logconcave_comp_linear hf e.symm.toLinearMap) hc',
    measurable_const.mul hcomp, ?_⟩
  have hmap := GaussianTilt.map_withDensity_comp e.toHomeomorph.measurableEmbedding μ
    (fun y ↦ ENNReal.ofReal (f (e.symm y)))
  change Measure.map e (μ.withDensity (fun x ↦ ENNReal.ofReal (f (e.symm (e x))))) =
    (Measure.map e μ).withDensity (fun y ↦ ENNReal.ofReal (f (e.symm y))) at hmap
  simp only [e.symm_apply_apply] at hmap
  rw [hmap, hscale, withDensity_smul_measure, ← withDensity_smul (c : ℝ≥0∞) hcomp.ennreal_ofReal]
  congr 1
  funext y
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul hc'.le, ENNReal.ofReal_coe_nnreal]

lemma transported_support_bound (e : E ≃L[ℝ] F) {f : E → ℝ} {R c : ℝ}
    (hs : ∀ x, R < ‖x‖ → f x = 0) :
    ∀ y, ‖e.toContinuousLinearMap‖ * R < ‖y‖ → c * f (e.symm y) = 0 := by
  intro y hy
  have hx : R < ‖e.symm y‖ := by
    by_contra h
    have hb := e.toContinuousLinearMap.le_opNorm (e.symm y)
    rw [show e.toContinuousLinearMap (e.symm y) = y from e.apply_symm_apply y] at hb
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt h) (norm_nonneg e.toContinuousLinearMap)
    exact (not_lt_of_ge (hb.trans hm)) hy
  rw [hs _ hx, mul_zero]

end GaussianTilt.LinearImageDensity
