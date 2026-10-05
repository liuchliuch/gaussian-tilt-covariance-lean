import GaussianTilt.FunctionalBrascampLimit
import GaussianTilt.LetwinMongeAmpere

/-! # Regularity of the actual inverse-Hessian energy -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ContDiff
namespace GaussianTilt.FunctionalBrascampLieb
open GaussianTilt.Letwin

lemma diffusionGamma_inverseHessian_eq {n : ℕ} (φ f : CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    diffusionGamma (inverseHessian φ) f f x =
      coordinateGradient f x ⬝ᵥ ((coordinateHessian φ x)⁻¹ *ᵥ coordinateGradient f x) := by
  simp only [diffusionGamma, diffusionFlux, inverseHessian, coordinateGradient, dotProduct, mulVec]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma diffusionGamma_inverseHessian_nonneg {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ∀ x, (coordinateHessian φ x).PosDef) (f : CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    0 ≤ diffusionGamma (inverseHessian φ) f f x := by
  rw [diffusionGamma_inverseHessian_eq]
  have h := (hφ x).inv.posSemidef.2 (coordinateGradient f x)
  simpa only [star_trivial] using h

lemma contDiff_inverseHessian_energy {n : ℕ} {φ f : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (hH : ∀ x, (coordinateHessian φ x).PosDef) :
    ContDiff ℝ ∞ (diffusionGamma (inverseHessian φ) f f) := by
  have hdφ (i : Fin n) : ContDiff ℝ ∞ (coordinateDerivative i φ) :=
    contDiff_coordinateDerivative hφ (by simp) i
  have hHsmooth (i j : Fin n) : ContDiff ℝ ∞ (fun x ↦ coordinateHessian φ x i j) :=
    contDiff_coordinateDerivative (hdφ i) (by simp) j
  have hInv (i j : Fin n) : ContDiff ℝ ∞ (fun x ↦ inverseHessian φ x i j) :=
    contDiff_matrix_inv hHsmooth (fun x ↦ (hH x).det_pos.ne') i j
  have hdf (i : Fin n) : ContDiff ℝ ∞ (coordinateDerivative i f) :=
    contDiff_coordinateDerivative hf (by simp) i
  apply ContDiff.sum
  intro i _
  apply ContDiff.mul ?_ (hdf i)
  apply ContDiff.sum
  intro j _
  exact (hInv i j).mul (hdf j)

end GaussianTilt.FunctionalBrascampLieb
