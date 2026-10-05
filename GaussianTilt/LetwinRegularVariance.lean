import GaussianTilt.LetwinVarianceInputs
import GaussianTilt.NegativeSobolevVariance
import GaussianTilt.WhiteningQuadraticApproximation

/-! # The genuine regular Letwin quadratic variance theorem

The proof uses the constructed Gaussian smoothing, the unconditional proved
negative-Sobolev variance theorem, the exact dual budget and actual variance
continuity. Singular matrices are handled by the constructed spectral
approximation. No variance, Stein, range-density or limiting assertion is
included among the assumptions.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ContDiff ENNReal
namespace GaussianTilt.Letwin

set_option maxHeartbeats 1400000 in
/-- The regular theorem for nonsingular symmetric quadratic matrices. -/
theorem regular_mongeAmpere_quadratic_variance_invertible {n : ℕ} {φ V : CoordinateSpace n → ℝ}
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
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) (hdet : B.det≠0) :
    variance (matrixQuadratic B) (momentMeasure φ) ≤ 8*Matrix.trace (B^2) := by
  have hφ1 := contDiff_infty.mp hφ 1
  have hnoise (r : ℝ) (hr : 0<r) :
      variance (matrixQuadratic (spectralSign hB)) (noisyMomentMeasure φ (spectralMagnitudeRoot hB) r) ≤
        8*Matrix.trace (B^2)+(8*Matrix.trace (spectralAbsolute hB))*r^2+(4*(n : ℝ))*r^4 := by
    obtain ⟨ψ,hψ,hψH,hψp,hψlaw,hq,hdual,hbudget⟩ := regular_noisy_variance_application_data
      hφ hc hH hK hU hKU hgrad hV hVc hMA S hHb hiso hf hfm hμ hB hdet r hr.ne'
    letI := hψp
    have hvar := variance_le_sum_compactNegativeSobolev_sq hψ (contDiff_matrixQuadratic (spectralSign hB)) hq hψH
      (fun i => noisySteinDualConstant φ (spectralMagnitudeRoot hB) r (fun j => 2*spectralSign hB i j))
      (fun i => noisySteinDualConstant_nonneg _ _ _ _) hdual
    rw [← hψlaw] at hvar
    have h := hvar.trans hbudget
    convert h using 1 <;> ring
  have hlimit := quadratic_variance_le_of_noisy_bounds hφ1 hK hgrad (spectralMagnitudeRoot hB)
    (spectralSign hB) (8*Matrix.trace (B^2)) (8*Matrix.trace (spectralAbsolute hB)) (4*(n : ℝ)) hnoise
  rw [variance_spectralCoordinates hφ1 hB] at hlimit
  rw [variance_momentMeasure hφ1 B]
  exact hlimit

set_option maxHeartbeats 1400000 in
/-- Letwin's sharp regular quadratic variance theorem for every symmetric
matrix, including indefinite and singular matrices. -/
theorem regular_mongeAmpere_quadratic_variance {n : ℕ} {φ V : CoordinateSpace n → ℝ}
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
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    variance (matrixQuadratic B) (momentMeasure φ) ≤ 8*Matrix.trace (B^2) := by
  have hφ1 := contDiff_infty.mp hφ 1
  have hproducts (i j : Fin n) : MemLp
      (fun x => coordinateGradient φ x i*coordinateGradient φ x j) 2 (potentialMeasure φ) :=
    memLp_comp_gradient (g := fun z => z i*z j) hφ1 hK hgrad (by fun_prop) 2
  rw [variance_momentMeasure hφ1 B]
  apply Whitening.quadratic_bound_of_invertible hproducts (C := 8) ?_ B hB
  intro A hA hdet
  have hAh : A.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  have h := regular_mongeAmpere_quadratic_variance_invertible hφ hc hH hK hU hKU hgrad
    hV hVc hMA S hHb hiso hf hfm hμ hAh hdet
  rw [variance_momentMeasure hφ1 A] at h
  exact h

/-- The same proved estimate stated for the actual target probability law;
its isotropy and pushforward relation discharge source covariance exactly. -/
theorem regular_target_quadratic_variance {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hc : ConvexOn ℝ univ φ)
    (hH : ∀ x, (coordinateHessian φ x).PosDef)
    {K U : Set (CoordinateSpace n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hgrad : ∀ x, coordinateGradient φ x∈K)
    (hV : ContDiffOn ℝ 2 V U) (hVc : ConvexOn ℝ U V)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x+V (coordinateGradient φ x))
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    {μ : Measure (CoordinateSpace n)} (hmap : momentMeasure φ=μ) (hiso : covarianceMatrix μ id=1)
    {f : CoordinateSpace n → ℝ} (hf : LogConcaveMarginal.IsLogConcave f) (hfm : Measurable f)
    (hμ : μ=volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    variance (matrixQuadratic B) μ ≤ 8*Matrix.trace (B^2) := by
  have h := regular_mongeAmpere_quadratic_variance hφ hc hH hK hU hKU hgrad hV hVc hMA S hHb
    (momentPotential_covariance_of_target (contDiff_infty.mp hφ 1) hmap hiso) hf hfm (hmap.trans hμ) B hB
  simpa only [hmap] using h

end GaussianTilt.Letwin
