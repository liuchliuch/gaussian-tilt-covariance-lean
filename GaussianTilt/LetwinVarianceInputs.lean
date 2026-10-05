import GaussianTilt.LetwinMomentTransfer

/-! # Fully constructed inputs to the smooth negative-Sobolev variance theorem

This module asserts no quadratic variance inequality. It constructs every
analytic input needed by that theorem, with the exact sharp limiting budget.
-/
noncomputable section
open MeasureTheory Matrix Set
open scoped BigOperators ContDiff ENNReal
namespace GaussianTilt.Letwin

set_option maxHeartbeats 1200000 in
/-- Every input to the smooth H⁻¹ variance theorem is constructed from the
regular moment-potential data and the actual target density. -/
theorem regular_noisy_variance_application_data {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hc : ConvexOn ℝ univ φ)
    (hH : ∀ x, (coordinateHessian φ x).PosDef)
    {K U : Set (CoordinateSpace n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hgrad : ∀ x, coordinateGradient φ x∈K)
    (hV : ContDiffOn ℝ 2 V U) (hVc : ConvexOn ℝ U V)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x+V (coordinateGradient φ x))
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (hiso : covarianceMatrix (potentialMeasure φ) (coordinateGradient φ)=1)
    {f : CoordinateSpace n → ℝ} (hf : LogConcaveMarginal.IsLogConcave f) (hfm : Measurable f)
    (hμ : momentMeasure φ=volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) (hdet : B.det≠0)
    (r : ℝ) (hr : r≠0) :
    ∃ ψ : CoordinateSpace n → ℝ,
      ContDiff ℝ ∞ ψ ∧ (∀ x, (coordinateHessian ψ x).PosSemidef) ∧
      IsProbabilityMeasure (potentialMeasure ψ) ∧
      noisyMomentMeasure φ (spectralMagnitudeRoot hB) r=potentialMeasure ψ ∧
      MemLp (matrixQuadratic (spectralSign hB)) 2 (potentialMeasure ψ) ∧
      (∀ i, CompactNegativeSobolevBound (potentialMeasure ψ)
        (coordinateDerivative i (matrixQuadratic (spectralSign hB)))
        (noisySteinDualConstant φ (spectralMagnitudeRoot hB) r (fun j => 2*spectralSign hB i j))) ∧
      (∑ i, noisySteinDualConstant φ (spectralMagnitudeRoot hB) r
        (fun j => 2*spectralSign hB i j)^2) ≤
        8*Matrix.trace (B^2)+8*r^2*Matrix.trace (spectralAbsolute hB)+4*r^4*(n : ℝ) := by
  have hφ1 := contDiff_infty.mp hφ 1
  have hT := spectralMagnitudeRoot_posDef hB hdet
  obtain ⟨ψ,hψ,hψc,hψlaw⟩ := noisyMomentMeasure_has_smooth_convex_potential hφ1 hK hgrad
    hf hfm hμ (spectralMagnitudeRoot hB) hT.det_pos.ne' r hr
  have hp : IsProbabilityMeasure (potentialMeasure ψ) := by
    rw [← hψlaw]
    exact noisyMomentMeasure_probability hφ1 _ r
  have hLp : MemLp (matrixQuadratic (spectralSign hB)) 2 (potentialMeasure ψ) := by
    rw [← hψlaw]
    exact quadratic_noisyMomentMeasure_memLp hφ1 hK hgrad _ _ r
  refine ⟨ψ,hψ,(fun x => coordinateHessian_posSemidef_of_convex isOpen_univ hψc
    (contDiff_infty.mp hψ 2).contDiffOn (mem_univ x)),hp,hψlaw,hLp,?_,?_⟩
  · intro i
    rw [← hψlaw]
    exact regular_noisy_quadratic_gradient_dual_bounds hφ hK hgrad S hHb hB r i
  · exact regular_noisy_quadratic_dual_budget hφ hc hH hK hU hKU hgrad hV hVc hMA S hHb hiso hB r

end GaussianTilt.Letwin
