import GaussianTilt.NegativeSobolevGenerator
import GaussianTilt.EllipticRegularityCutoffs

/-! # Local unweighted integrability of the genuine weighted L² functions -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

lemma volume_absolutelyContinuous_potentialMeasure {n : ℕ}
    {φ : CoordinateSpace n → ℝ} (hφ : Continuous φ) :
    volume ≪ potentialMeasure φ := by
  apply withDensity_absolutelyContinuous'
  · exact ((Real.continuous_exp.comp hφ.neg).measurable.ennreal_ofReal).aemeasurable
  · exact Eventually.of_forall fun x => ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)

lemma potentialMeasure_isOpenPosMeasure {n : ℕ}
    {φ : CoordinateSpace n → ℝ} (hφ : Continuous φ) :
    (potentialMeasure φ).IsOpenPosMeasure :=
  (volume_absolutelyContinuous_potentialMeasure hφ).isOpenPosMeasure

/-- Multiplying an actual weighted L² function by any continuous compact
coefficient gives a genuine unweighted L² function. -/
theorem memLp_compact_mul_of_potential {n : ℕ}
    {φ h a : CoordinateSpace n → ℝ} (hφ : Continuous φ)
    (hh : MemLp h 2 (potentialMeasure φ)) (ha : Continuous a) (hac : HasCompactSupport a) :
    MemLp (fun x => a x * h x) 2 volume := by
  have hhvol : AEStronglyMeasurable h volume :=
    hh.aestronglyMeasurable.mono_ac (volume_absolutelyContinuous_potentialMeasure hφ)
  apply (memLp_two_iff_integrable_sq (ha.aestronglyMeasurable.mul hhvol)).mpr
  have hw : Integrable (fun x => Real.exp (-φ x) * h x ^ 2) volume :=
    (integrable_potentialMeasure_iff hφ _).mp hh.integrable_sq
  let b := fun x => a x ^ 2 * Real.exp (φ x)
  have hb : Continuous b := (ha.pow 2).mul (Real.continuous_exp.comp hφ)
  have hbc : HasCompactSupport b := by
    simpa only [b, pow_two] using (hac.mul_right (f' := a)).mul_right
      (f' := fun x => Real.exp (φ x))
  have hi := hw.bdd_mul hb.aestronglyMeasurable (hbc.exists_bound_of_continuous hb)
  convert hi using 1
  funext x
  dsimp [b]
  have hexp : Real.exp (φ x) * Real.exp (-φ x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith only [hexp]

/-- Weighted L² functions are locally integrable with respect to the actual
Lebesgue measure; compact cutoffs and positive smooth density prove this. -/
theorem locallyIntegrable_of_potential_memLp {n : ℕ}
    {φ h : CoordinateSpace n → ℝ} (hφ : Continuous φ)
    (hh : MemLp h 2 (potentialMeasure φ)) : LocallyIntegrable h volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : CoordinateSpace n)
  have hc := memLp_compact_mul_of_potential hφ hh (ellipticCutoff_contDiff n R).continuous
    (ellipticCutoff_compact n hR.ne')
  apply ((hc.locallyIntegrable (by norm_num)).integrableOn_isCompact hK).congr_fun
  · intro x hx
    change ellipticCutoff n R x * h x = h x
    rw [ellipticCutoff_eq_one hR (by simpa only [Metric.mem_closedBall, dist_zero_right] using hKR hx), one_mul]
  · exact hK.measurableSet

end GaussianTilt.Letwin
