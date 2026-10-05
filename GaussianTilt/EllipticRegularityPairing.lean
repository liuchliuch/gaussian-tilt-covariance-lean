import GaussianTilt.NegativeSobolevWeakDuality
import GaussianTilt.EllipticRegularityDistribution

/-! # Recovering unweighted derivative pairings from localized weighted H¹ -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

/-- The actual compact smooth test e^φ ψ. -/
def weightedExponentTest {n : ℕ} {φ ψ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    smoothCompactCore n :=
  ⟨fun x => Real.exp (φ x)*ψ x, hφ.exp.mul hψ, hψc.mul_left⟩

lemma adjoint_weightedExponentTest {n : ℕ} {φ ψ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (i : Fin n) (x : CoordinateSpace n) :
    (smoothCompactDerivativeAdjoint hφ i (weightedExponentTest hφ hψ hψc)).1 x =
      -Real.exp (φ x)*coordinateDerivative i ψ x := by
  change coordinateDerivative i φ x * (Real.exp (φ x)*ψ x) -
    coordinateDerivative i (fun y => Real.exp (φ y)*ψ y) x = _
  rw [coordinateDerivative_mul ((hφ.differentiable (by simp)).exp) (hψ.differentiable (by simp)),
    coordinateDerivative_exp (hφ.differentiable (by simp))]
  ring

lemma cutoff_mul_coordinateDerivative_eq {n : ℕ} {χ ψ : CoordinateSpace n → ℝ}
    (hχ : ∀ x ∈ tsupport ψ, χ x = 1) (i : Fin n) (x : CoordinateSpace n) :
    χ x * coordinateDerivative i ψ x = coordinateDerivative i ψ x := by
  by_cases hx : x ∈ tsupport ψ
  · rw [hχ x hx, one_mul]
  · have hd : coordinateDerivative i ψ x = 0 := by
      simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hx, ContinuousLinearMap.zero_apply]
    rw [hd, mul_zero]

/-- The requested exact pairing: an actual weighted local Sobolev
representative of χh controls the unweighted distributional derivative of h
on every compact smooth test supported where χ=1. -/
theorem localized_weightedSobolev_unweighted_derivative_pairing {n : ℕ}
    {φ χ h ψ : CoordinateSpace n → ℝ}
    [IsFiniteMeasureOnCompacts (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (u : weightedSobolev (potentialMeasure φ))
    (hu : u.1 0 =ᵐ[potentialMeasure φ] fun x => χ x*h x)
    (hχ : ∀ x ∈ tsupport ψ, χ x = 1) (i : Fin n) :
    (∫ x, h x * coordinateDerivative i ψ x) =
      -inner ℝ (u.1 i.succ)
        (smoothCompactToL2 (potentialMeasure φ) (weightedExponentTest hφ hψ hψc)) := by
  let g := weightedExponentTest hφ hψ hψc
  have hp := weightedSobolev_integration_by_parts hφ u i g
  rw [inner_smoothCompact_right (potentialMeasure φ) (u.1 0) (smoothCompactDerivativeAdjoint hφ i g)] at hp
  have heq : (∫ x, u.1 0 x * (smoothCompactDerivativeAdjoint hφ i g).1 x ∂potentialMeasure φ) =
      -(∫ x, h x * coordinateDerivative i ψ x) := by
    have hv : (fun x => u.1 0 x * (smoothCompactDerivativeAdjoint hφ i g).1 x) =ᵐ[potentialMeasure φ]
        (fun x => (χ x*h x) * (smoothCompactDerivativeAdjoint hφ i g).1 x) := by
      filter_upwards [hu] with x hx
      rw [hx]
    rw [integral_congr_ae hv]
    simp only [g, adjoint_weightedExponentTest]
    rw [integral_potentialMeasure hφ.continuous, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    have hexp : Real.exp (-φ x)*Real.exp (φ x) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      _ = -(Real.exp (-φ x)*Real.exp (φ x)) * h x * (χ x*coordinateDerivative i ψ x) := by ring
      _ = _ := by rw [hexp, cutoff_mul_coordinateDerivative_eq hχ i x]; ring
  rw [heq] at hp
  change _ = -inner ℝ (u.1 i.succ) (smoothCompactToL2 (potentialMeasure φ) g)
  linarith

end GaussianTilt.Letwin
