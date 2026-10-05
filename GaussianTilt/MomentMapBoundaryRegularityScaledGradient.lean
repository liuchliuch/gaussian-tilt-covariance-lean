import GaussianTilt.MomentMapBoundaryRegularityInteriorGradient
import GaussianTilt.MomentMapBoundaryRegularityRescaling

/-! # Correctly scaled signed elliptic gradient estimates -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

theorem exists_scaled_interior_gradient_bound {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (v f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (c : CoordinateSpace n) (r U F : ℝ),
      0 < r → 0 ≤ U → 0 ≤ F → ContDiff ℝ ∞ v → Differentiable ℝ f →
      (∀ i j, Differentiable ℝ (fun y => A y i j)) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < 2*r → |v y| ≤ U) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r → (A y).PosSemidef) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r → ∀ w : CoordinateSpace n,
        lam*‖(coordinateEquiv n).symm w‖^2 ≤ w ⬝ᵥ (A y *ᵥ w) ∧
        w ⬝ᵥ (A y *ᵥ w) ≤ Λ*‖(coordinateEquiv n).symm w‖^2) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r →
        ∀ k i j, r*|matrixCoordinateDerivative A k y i j| ≤ K) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r → r^2*|f y| ≤ F) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r →
        ∀ k, r^3*|coordinateDerivative k f y| ≤ F) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r → linearizedMA (A y) v y = f y) →
      ∀ i, r*|coordinateDerivative i v c| ≤ C*(U+F) := by
  obtain ⟨C,hC,hgrad⟩ := exists_signed_interior_gradient_bound (n := n) hlam hΛ hK
  refine ⟨C,hC,?_⟩
  intro v f A c r U F hr hU hF hv hf hAd hub hA hEll hDA hfb hDfb hP
  let P := ellipticRescalePoint c r
  let v' := fun z => v (P z)
  let f' := fun z => r^2*f (P z)
  let A' := fun z => A (P z)
  have hPr : ContDiff ℝ ∞ P := contDiff_ellipticRescalePoint c r
  have hv' : ContDiff ℝ ∞ v' := hv.comp hPr
  have hf' : Differentiable ℝ f' := (hf.comp (hPr.differentiable (by simp))).const_mul _
  have hAd' (i j : Fin n) : Differentiable ℝ (fun z => A' z i j) := (hAd i j).comp (hPr.differentiable (by simp))
  have hnear (z : CoordinateSpace n) (hz : ‖(coordinateEquiv n).symm z‖ < 1) :
      ‖(coordinateEquiv n).symm (P z)-(coordinateEquiv n).symm c‖ < r := by
    rw [ellipticRescalePoint_norm _ _ hr.le]
    nlinarith
  have hbound := hgrad v' f' A' U F hU hF hv' hf' hAd'
    (fun z hz => hub (P z) (by rw [ellipticRescalePoint_norm _ _ hr.le]; nlinarith))
    (fun z hz => hA (P z) (hnear z hz)) (fun z hz => hEll (P z) (hnear z hz))
    (fun z hz k i j => by
      change |coordinateDerivative k (fun w => A (P w) i j) z| ≤ K
      rw [coordinateDerivative_ellipticRescale (hAd i j), abs_mul, abs_of_pos hr]
      exact hDA (P z) (hnear z hz) k i j)
    (fun z hz => by
      change |r^2*f (P z)| ≤ F
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact hfb (P z) (hnear z hz))
    (fun z hz k => by
      change |coordinateDerivative k (fun w => r^2*f (P w)) z| ≤ F
      have hfp : Differentiable ℝ (fun w => f (P w)) := hf.comp (hPr.differentiable (by simp))
      rw [coordinateDerivative_const_mul hfp, coordinateDerivative_ellipticRescale hf,
        abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos hr]
      convert hDfb (P z) (hnear z hz) k using 1 <;> ring)
    (fun z hz => by
      change linearizedMA (A (P z)) (fun w => v (P w)) z = r^2*f (P z)
      rw [linearizedMA_ellipticRescale hv, hP (P z) (hnear z hz)])
  intro i
  have hh := hbound i
  change |coordinateDerivative i (fun z => v (ellipticRescalePoint c r z)) 0| ≤ C*(U+F) at hh
  rw [coordinateDerivative_ellipticRescale (hv.differentiable (by simp))] at hh
  simpa only [ellipticRescalePoint,smul_zero,add_zero,abs_mul,abs_of_pos hr] using hh

end GaussianTilt.MomentMapRegularity
