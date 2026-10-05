import GaussianTilt.NegativeSobolevRange
import GaussianTilt.NegativeSobolevNorm
import GaussianTilt.LetwinConvexity

/-!
# The genuine negative-Sobolev variance theorem for smooth log-concave laws

This is the regular-class Barthe--Klartag/Letwin H⁻¹ theorem. The actual
weighted Laplacian range is proved dense in mean-zero L² using local elliptic
regularity, actual mollification, Sobolev compactness, cutoff Caccioppoli and
rough Liouville. The actual Euclidean Bochner estimate and dual pairing then
yield the variance inequality. No range, Poisson-existence, Poincaré, or
variance assertion is a hypothesis.

The test-duality form directly serves the Gaussian-smoothed quadratic-form
application. The extended-norm form uses the full source locally Lipschitz L²
test class and allows infinite H⁻¹ norm. The observable in this regular
version is smooth and L²; its derivatives need not be globally L² for the
compact-test formulation.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ContDiff Topology ENNReal
namespace GaussianTilt.Letwin

/-- Genuine H⁻¹ variance control from the actual compact-test pairings,
for every smooth L² observable under an actual smooth log-concave density.
All weighted elliptic range/density inputs are proved, not assumed. -/
theorem variance_le_sum_compactNegativeSobolev_sq {n : ℕ}
    {φ f : CoordinateSpace n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (hfL : MemLp f 2 (potentialMeasure φ))
    (hH : ∀ x, (coordinateHessian φ x).PosSemidef)
    (C : Fin n → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hB : ∀ i, CompactNegativeSobolevBound (potentialMeasure φ)
      (coordinateDerivative i f) (C i)) :
    variance f (potentialMeasure φ) ≤ ∑ i, C i^2 :=
  variance_le_dual_sq_of_generatorClosure_eq hφ hf hfL hH
    (weightedLaplacianToL2_closure_eq_meanZero hφ) C hC hB

/-- The actual extended-real H⁻¹ inequality. This is Letwin Proposition 2.8
on the fully proved smooth positive-density/smooth-observable regular class.
Infinite negative Sobolev norms are handled honestly as infinity. -/
theorem variance_le_sum_negativeSobolev_sq {n : ℕ}
    {φ f : CoordinateSpace n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (hfL : MemLp f 2 (potentialMeasure φ))
    (hH : ∀ x, (coordinateHessian φ x).PosSemidef) :
    ENNReal.ofReal (variance f (potentialMeasure φ)) ≤
      ∑ i, (negativeSobolevNorm (potentialMeasure φ) (coordinateDerivative i f))^2 := by
  let N := fun i => negativeSobolevNorm (potentialMeasure φ) (coordinateDerivative i f)
  by_cases hfin : ∀ i, N i ≠ ⊤
  · have hb := variance_le_sum_compactNegativeSobolev_sq hφ hf hfL hH
      (fun i => (N i).toReal) (fun i => ENNReal.toReal_nonneg)
      (fun i => compactNegativeSobolevBound_of_norm_le ENNReal.toReal_nonneg
        (by rw [ENNReal.ofReal_toReal (hfin i)]))
    have hcast := ENNReal.ofReal_le_ofReal hb
    simpa only [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ((N i).toReal)),
      ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin _)] using hcast
  · push_neg at hfin
    obtain ⟨i, hi⟩ := hfin
    have ht : (∑ j, N j^2) = ⊤ := ENNReal.sum_eq_top.2 ⟨i, Finset.mem_univ i, by simp [hi]⟩
    change _ ≤ ∑ j, N j^2
    rw [ht]
    exact le_top

/-- The identical bound with the source's signed supremum, rather than the
equivalent absolute-pairing implementation. -/
theorem variance_le_sum_signedNegativeSobolev_sq {n : ℕ}
    {φ f : CoordinateSpace n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (hfL : MemLp f 2 (potentialMeasure φ))
    (hH : ∀ x, (coordinateHessian φ x).PosSemidef) :
    ENNReal.ofReal (variance f (potentialMeasure φ)) ≤
      ∑ i, (signedNegativeSobolevNorm (potentialMeasure φ) (coordinateDerivative i f))^2 := by
  simpa only [negativeSobolevNorm_eq_signed] using variance_le_sum_negativeSobolev_sq hφ hf hfL hH

/-- Convex-potential form: Hessian semidefiniteness is derived from actual
convexity instead of being a matrix side condition. -/
theorem variance_le_sum_compactNegativeSobolev_sq_of_convex {n : ℕ}
    {φ f : CoordinateSpace n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hconv : ConvexOn ℝ Set.univ φ)
    (hf : ContDiff ℝ ∞ f) (hfL : MemLp f 2 (potentialMeasure φ))
    (C : Fin n → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hB : ∀ i, CompactNegativeSobolevBound (potentialMeasure φ)
      (coordinateDerivative i f) (C i)) :
    variance f (potentialMeasure φ) ≤ ∑ i, C i^2 :=
  variance_le_sum_compactNegativeSobolev_sq hφ hf hfL
    (fun x => coordinateHessian_posSemidef_of_convex isOpen_univ hconv
      (contDiff_infty.mp hφ 2).contDiffOn (Set.mem_univ x)) C hC hB

/-- Letwin's H⁻¹ bound on the proved smooth regular class, directly under
convexity of the actual density potential. -/
theorem variance_le_sum_negativeSobolev_sq_of_convex {n : ℕ}
    {φ f : CoordinateSpace n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hconv : ConvexOn ℝ Set.univ φ)
    (hf : ContDiff ℝ ∞ f) (hfL : MemLp f 2 (potentialMeasure φ)) :
    ENNReal.ofReal (variance f (potentialMeasure φ)) ≤
      ∑ i, (negativeSobolevNorm (potentialMeasure φ) (coordinateDerivative i f))^2 :=
  variance_le_sum_negativeSobolev_sq hφ hf hfL
    (fun x => coordinateHessian_posSemidef_of_convex isOpen_univ hconv
      (contDiff_infty.mp hφ 2).contDiffOn (Set.mem_univ x))

end GaussianTilt.Letwin
