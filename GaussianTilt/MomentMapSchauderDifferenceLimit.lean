import GaussianTilt.MomentMapSchauderVectorDifferences
import GaussianTilt.MomentMapHolderDerivativeLimit
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Genuine differentiability gain from bounded source finite differences -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
open Set Filter
open scoped ContDiff Topology
namespace GaussianTilt.MomentMapSchauder
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma tendsto_vectorDifferenceQuotient {f : E → F} {x e : E}
    (hf : DifferentiableAt ℝ f x) :
    Tendsto (fun s : ℝ => vectorDifferenceQuotient f (s • e) s x) (𝓝[≠] 0)
      (𝓝 (fderiv ℝ f x e)) := by
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x+(0 : ℝ) • e) := by simpa using hf.hasFDerivAt
  have hd : HasDerivAt (fun s : ℝ => f (x+s • e)) (fderiv ℝ f x e) 0 := by
    simpa only [one_smul] using
      hf'.comp_hasDerivAt (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x)
  simpa only [zero_add, zero_smul, add_zero, vectorDifferenceQuotient] using hd.tendsto_slope_zero

def positiveVanishingStep (R : ℝ) (k : ℕ) : ℝ := R/((k : ℝ)+1)

lemma positiveVanishingStep_pos {R : ℝ} (hR : 0 < R) (k : ℕ) : 0 < positiveVanishingStep R k := by
  unfold positiveVanishingStep
  positivity

lemma positiveVanishingStep_le {R : ℝ} (hR : 0 ≤ R) (k : ℕ) : positiveVanishingStep R k ≤ R := by
  unfold positiveVanishingStep
  exact div_le_self hR (by have hh := Nat.cast_nonneg (α := ℝ) k; linarith)

lemma tendsto_positiveVanishingStep {R : ℝ} (hR : 0 < R) :
    Tendsto (positiveVanishingStep R) atTop (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hh := tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat (a := R)
    simpa only [positiveVanishingStep, mul_one_div, mul_zero] using hh
  · exact Filter.Eventually.of_forall (fun k => (positiveVanishingStep_pos hR k).ne')

/-- Bounded Hölder derivatives of actual difference quotients give the
true next derivative of a C¹ function. Compactness and limit differentiation
are invoked through the proved generic endpoint. -/
theorem contDiffOn_fderiv_apply_of_quotient_derivative_bounds
    [CompleteSpace F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} (hf : ContDiff ℝ 1 f) {S : Set E} (hS : IsCompact S)
    {α C R : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (hR : 0 < R) (e : E)
    (hb : ∀ s : ℝ, s ≠ 0 → |s| ≤ R → ∀ x ∈ S,
      ‖vectorDifferenceQuotient (fderiv ℝ f) (s • e) s x‖ ≤ C)
    (hh : ∀ s : ℝ, s ≠ 0 → |s| ≤ R → ∀ x ∈ S, ∀ y ∈ S,
      ‖vectorDifferenceQuotient (fderiv ℝ f) (s • e) s x-
        vectorDifferenceQuotient (fderiv ℝ f) (s • e) s y‖ ≤ C*‖x-y‖^α) :
    ContDiffOn ℝ 1 (fun x => fderiv ℝ f x e) (interior S) ∧
      (∀ x ∈ interior S, ‖fderiv ℝ (fun y => fderiv ℝ f y e) x‖ ≤ C) ∧
      (∀ x ∈ interior S, ∀ y ∈ interior S,
        ‖fderiv ℝ (fun z => fderiv ℝ f z e) x-fderiv ℝ (fun z => fderiv ℝ f z e) y‖ ≤ C*‖x-y‖^α) := by
  let s := positiveVanishingStep R
  have hsn (k : ℕ) : s k ≠ 0 := (positiveVanishingStep_pos hR k).ne'
  have hsb (k : ℕ) : |s k| ≤ R := by
    rw [abs_of_pos (positiveVanishingStep_pos hR k)]
    exact positiveVanishingStep_le hR.le k
  have hDc : Continuous (fderiv ℝ f) := (hf.fderiv_right (m := 0) (by norm_num)).continuous
  have hres := GaussianTilt.HolderSpace.contDiffOn_one_of_holder_derivative_bounds hS hα hC
    (fun k => vectorDifferenceQuotient f (s k • e) (s k))
    (fun k => vectorDifferenceQuotient (fderiv ℝ f) (s k • e) (s k))
    (fun x => fderiv ℝ f x e)
    (fun k => (continuous_const.smul ((hDc.comp (continuous_id.add continuous_const)).sub hDc)).continuousOn)
    (fun k x hx => hb (s k) (hsn k) (hsb k) x hx)
    (fun k x hx y hy => by simpa only [dist_eq_norm] using hh (s k) (hsn k) (hsb k) x hx y hy)
    (fun k x _ => by
      dsimp only
      rw [← fderiv_vectorDifferenceQuotient (hf.differentiable le_rfl)]
      exact ((contDiff_vectorDifferenceQuotient hf _ _).differentiable le_rfl x).hasFDerivAt)
    (fun x _ => (tendsto_vectorDifferenceQuotient (hf.differentiable le_rfl x)).comp
      (tendsto_positiveVanishingStep hR))
  simpa only [dist_eq_norm] using hres

end GaussianTilt.MomentMapSchauder
