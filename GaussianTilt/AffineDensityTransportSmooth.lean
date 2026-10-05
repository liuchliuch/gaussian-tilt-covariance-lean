import GaussianTilt.AffineDensityTransport
import GaussianTilt.ScalarLogConcaveMoments

/-! # Smooth positive potentials under the actual affine density transport -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace GaussianTilt.AffineDensityTransport
open LogConcaveMarginal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual inverse affine coordinate map. -/
def inverseAffine (e : E ≃L[ℝ] F) (m : E) : F →ᵃ[ℝ] E :=
  e.symm.toLinearMap.toAffineMap + AffineMap.const ℝ F m

@[simp] lemma inverseAffine_apply (e : E ≃L[ℝ] F) (m : E) (y : F) :
    inverseAffine e m y = e.symm y + m := rfl

/-- The correct transformed potential absorbs the positive Haar multiplier. -/
def affinePotential (e : E ≃L[ℝ] F) (m : E) (c : ℝ) (V : E → ℝ) (y : F) : ℝ :=
  V (e.symm y + m) - Real.log c

lemma contDiff_affinePotential (e : E ≃L[ℝ] F) (m : E) (c : ℝ)
    {V : E → ℝ} {r : WithTop ℕ∞} (hV : ContDiff ℝ r V) :
    ContDiff ℝ r (affinePotential e m c V) := by
  exact (hV.comp (e.symm.toContinuousLinearMap.contDiff.add contDiff_const)).sub contDiff_const

lemma affine_image_eq_inverse_preimage (e : E ≃L[ℝ] F) (m : E) (S : Set E) :
    (fun x ↦ e (x - m)) '' S = inverseAffine e m ⁻¹' S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨e.symm y + m, hy, by simp⟩

lemma convex_affine_image (e : E ≃L[ℝ] F) (m : E) {S : Set E} (hS : Convex ℝ S) :
    Convex ℝ ((fun x ↦ e (x - m)) '' S) := by
  rw [affine_image_eq_inverse_preimage]
  exact hS.affine_preimage (inverseAffine e m)

lemma convexOn_affinePotential (e : E ≃L[ℝ] F) (m : E) (c : ℝ)
    {S : Set E} {V : E → ℝ} (hV : ConvexOn ℝ S V) :
    ConvexOn ℝ ((fun x ↦ e (x - m)) '' S) (affinePotential e m c V) := by
  rw [affine_image_eq_inverse_preimage]
  simpa only [affinePotential, Function.comp_def, inverseAffine_apply, Pi.add_apply,
    sub_eq_add_neg] using (hV.comp_affineMap (inverseAffine e m)).add_const (-Real.log c)

lemma convexOn_univ_affinePotential (e : E ≃L[ℝ] F) (m : E) (c : ℝ)
    {V : E → ℝ} (hV : ConvexOn ℝ univ V) :
    ConvexOn ℝ univ (affinePotential e m c V) := by
  have h := convexOn_affinePotential e m c hV
  rwa [affine_image_eq_inverse_preimage, preimage_univ] at h

lemma exp_neg_affinePotential (e : E ≃L[ℝ] F) (m : E) {c : ℝ} (hc : 0 < c)
    (V : E → ℝ) (y : F) :
    Real.exp (-affinePotential e m c V y) = c * Real.exp (-V (e.symm y + m)) := by
  rw [affinePotential, neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log hc]

lemma positive_affine_density (e : E ≃L[ℝ] F) (m : E) {c : ℝ} (hc : 0 < c)
    {f : E → ℝ} (hf : ∀ x, 0 < f x) (y : F) : 0 < c * f (e.symm y + m) :=
  mul_pos hc (hf _)

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [SecondCountableTopology E] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional ℝ F] [SecondCountableTopology F]

lemma logconcave_exp_neg_of_convex {V : E → ℝ} (hV : ConvexOn ℝ univ V) :
    IsLogConcave (fun x ↦ Real.exp (-V x)) := by
  refine ⟨fun x ↦ Real.exp_nonneg _, ?_⟩
  intro x y a b ha hb hab
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := hV.2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at h
  nlinarith

/-- Affine transport of a genuine smooth positive logconcave density is again
represented by the exponential of a smooth convex potential, with the measure
identity proved from the Haar change of variables. -/
theorem exists_smooth_convex_potential_map_affine
    (e : E ≃L[ℝ] F) (m : E) (μ : Measure E) (ν : Measure F)
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {V : E → ℝ} {r : WithTop ℕ∞} (hVs : ContDiff ℝ r V)
    (hVc : ConvexOn ℝ univ V) :
    ∃ W : F → ℝ, ContDiff ℝ r W ∧ ConvexOn ℝ univ W ∧
      (∀ y, 0 < Real.exp (-W y)) ∧
      Measure.map (fun x ↦ e (x - m))
        (μ.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-V x)))) =
      ν.withDensity (fun y ↦ ENNReal.ofReal (Real.exp (-W y))) := by
  obtain ⟨c, hc, hl, hm, heq⟩ := exists_density_map_affine e m μ ν (logconcave_exp_neg_of_convex hVc)
    hVs.continuous.neg.rexp.measurable
  refine ⟨affinePotential e m c V, contDiff_affinePotential e m c hVs,
    convexOn_univ_affinePotential e m c hVc, fun y ↦ Real.exp_pos _, ?_⟩
  simpa only [exp_neg_affinePotential e m hc V] using heq

/-- The density identity also preserves an explicitly restricted convex
support, with a globally smooth convex potential on the transformed domain. -/
theorem exists_smooth_convex_potential_map_affine_indicator
    (e : E ≃L[ℝ] F) (m : E) (μ : Measure E) (ν : Measure F)
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {V : E → ℝ} {r : WithTop ℕ∞} (hVs : ContDiff ℝ r V)
    (hVc : ConvexOn ℝ univ V) {S : Set E} (hS : Convex ℝ S) (hSm : MeasurableSet S) :
    ∃ W : F → ℝ, ContDiff ℝ r W ∧ ConvexOn ℝ univ W ∧
      Measure.map (fun x ↦ e (x - m))
        (μ.withDensity (fun x ↦ ENNReal.ofReal (S.indicator (fun z ↦ Real.exp (-V z)) x))) =
      ν.withDensity (fun y ↦ ENNReal.ofReal
        (((fun x ↦ e (x - m)) '' S).indicator (fun z ↦ Real.exp (-W z)) y)) := by
  have hl := ScalarLogConcaveMoments.logconcave_indicator (logconcave_exp_neg_of_convex hVc) hS
  obtain ⟨c, hc, -, -, heq⟩ := exists_density_map_affine e m μ ν hl
    (hVs.continuous.neg.rexp.measurable.indicator hSm)
  refine ⟨affinePotential e m c V, contDiff_affinePotential e m c hVs,
    convexOn_univ_affinePotential e m c hVc, ?_⟩
  rw [heq]
  congr 1
  funext y
  rw [affine_image_eq_inverse_preimage]
  by_cases hy : e.symm y + m ∈ S
  · have hy' : y ∈ inverseAffine e m ⁻¹' S := hy
    simp only [indicator_of_mem hy, indicator_of_mem hy', exp_neg_affinePotential e m hc V]
  · have hy' : y ∉ inverseAffine e m ⁻¹' S := hy
    simp only [indicator_of_notMem hy, indicator_of_notMem hy', mul_zero]

end GaussianTilt.AffineDensityTransport
