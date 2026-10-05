import GaussianTilt.LinearImageDensity

/-! # Actual affine transport of logconcave Lebesgue densities

Translation and an invertible linear map act on the measure itself. Haar
uniqueness supplies the positive Jacobian scalar, rather than a density premise.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace GaussianTilt.AffineDensityTransport
open LogConcaveMarginal

lemma logconcave_add_const {E : Type*} [AddCommGroup E] [Module ℝ E]
    {f : E → ℝ} (hf : IsLogConcave f) (m : E) :
    IsLogConcave (fun x ↦ f (x + m)) := by
  refine ⟨fun x ↦ hf.1 (x + m), ?_⟩
  intro x y a b ha hb hab
  have heq : a • (x + m) + b • (y + m) = (a • x + b • y) + m := by
    rw [smul_add, smul_add]
    calc
      a • x + a • m + (b • y + b • m) = (a • x + b • y) + (a + b) • m := by
        rw [add_smul]; abel
      _ = _ := by rw [hab, one_smul]
  simpa only [heq] using hf.2 (x + m) (y + m) a b ha hb hab

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
  [SecondCountableTopology F]

lemma map_sub_withDensity (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → ℝ) (m : E) :
    Measure.map (fun x ↦ x - m) (μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) =
      μ.withDensity (fun y ↦ ENNReal.ofReal (f (y + m))) := by
  have h := GaussianTilt.map_withDensity_comp (Homeomorph.subRight m).measurableEmbedding μ
    (fun y ↦ ENNReal.ofReal (f (y + m)))
  change Measure.map (fun x ↦ x - m)
      (μ.withDensity (fun x ↦ ENNReal.ofReal (f ((x - m) + m)))) =
    (Measure.map (fun x ↦ x - m) μ).withDensity
      (fun y ↦ ENNReal.ofReal (f (y + m))) at h
  simp only [sub_add_cancel] at h
  rw [h]
  congr 1
  simpa only [sub_eq_add_neg] using (measurePreserving_add_right μ (-m)).map_eq

/-- The actual affine image has the expected density and a strictly positive
Jacobian multiplier. -/
theorem exists_density_map_affine (e : E ≃L[ℝ] F) (m : E)
    (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {f : E → ℝ} (hf : IsLogConcave f) (hm : Measurable f) :
    ∃ c : ℝ, 0 < c ∧
      IsLogConcave (fun y ↦ c * f (e.symm y + m)) ∧
      Measurable (fun y ↦ c * f (e.symm y + m)) ∧
      Measure.map (fun x ↦ e (x - m)) (μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) =
        ν.withDensity (fun y ↦ ENNReal.ofReal (c * f (e.symm y + m))) := by
  obtain ⟨c, hc, hlog, hmeas, hmap⟩ := LinearImageDensity.exists_density_map_linearEquiv
    e μ ν (logconcave_add_const hf m) (hm.comp (measurable_id.add_const m))
  refine ⟨c, hc, hlog, hmeas, ?_⟩
  rw [← hmap, ← map_sub_withDensity μ f m,
    Measure.map_map e.continuous.measurable
      (show Measurable (fun x : E ↦ x - m) by fun_prop)]
  rfl

lemma transported_support_bound (e : E ≃L[ℝ] F) (m : E) {f : E → ℝ} {R c : ℝ}
    (hs : ∀ x, R < ‖x‖ → f x = 0) :
    ∀ y, ‖e.toContinuousLinearMap‖ * (R + ‖m‖) < ‖y‖ →
      c * f (e.symm y + m) = 0 := by
  intro y hy
  have hx : R < ‖e.symm y + m‖ := by
    by_contra h
    have hb := e.toContinuousLinearMap.le_opNorm (e.symm y)
    rw [show e.toContinuousLinearMap (e.symm y) = y from e.apply_symm_apply y] at hb
    have hm : ‖e.symm y‖ ≤ R + ‖m‖ := by
      calc
        ‖e.symm y‖ = ‖(e.symm y + m) - m‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖e.symm y + m‖ + ‖m‖ := norm_sub_le _ _
        _ ≤ R + ‖m‖ := add_le_add_right (le_of_not_gt h) _
    exact (not_lt_of_ge (hb.trans (mul_le_mul_of_nonneg_left hm (norm_nonneg _)))) hy
  rw [hs _ hx, mul_zero]

end GaussianTilt.AffineDensityTransport

namespace GaussianTilt.Reference

lemma logconcave_map_affine {n : ℕ} {μ : Measure (Space n)}
    (hμ : logconcave μ) (e : Space n ≃L[ℝ] Space n) (m : Space n) :
    logconcave (Measure.map (fun x ↦ e (x - m)) μ) := by
  obtain ⟨f, hf, rfl⟩ := hμ
  obtain ⟨c, hc, hl, hm, heq⟩ := AffineDensityTransport.exists_density_map_affine
    e m volume volume ⟨hf.1, hf.2.2⟩ hf.2.1
  exact ⟨_, ⟨hl.1, hm, hl.2⟩, heq⟩

lemma compactlySupported_map_continuous {n : ℕ} {μ : Measure (Space n)}
    (hμ : compactlySupported μ) {f : Space n → Space n} (hf : Continuous f) :
    compactlySupported (Measure.map f μ) := by
  obtain ⟨K, hK, hμK⟩ := hμ
  refine ⟨f '' K, hK.image hf, ?_⟩
  rw [Measure.map_apply hf.measurable (hK.image hf).isClosed.measurableSet.compl]
  apply le_antisymm _ (zero_le _)
  rw [← hμK]
  apply measure_mono
  intro x hx hxK
  exact hx ⟨x, hxK, rfl⟩

end GaussianTilt.Reference
