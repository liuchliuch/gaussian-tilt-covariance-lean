import GaussianTilt.MomentMapBoundaryRegularityInteriorHarnack

/-! # Actual translation and scale covariance of the elliptic equations -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def ellipticRescalePoint (c : CoordinateSpace n) (r : ℝ) (x : CoordinateSpace n) : CoordinateSpace n := c+r•x

lemma contDiff_ellipticRescalePoint (c : CoordinateSpace n) (r : ℝ) :
    ContDiff ℝ ∞ (ellipticRescalePoint c r) := contDiff_const.add (contDiff_const.smul contDiff_id)

lemma coordinateDerivative_ellipticRescale {v : CoordinateSpace n → ℝ}
    (hv : Differentiable ℝ v) (c : CoordinateSpace n) (r : ℝ) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => v (ellipticRescalePoint c r y)) x =
      r*coordinateDerivative i v (ellipticRescalePoint c r x) := by
  have hl : HasFDerivAt (ellipticRescalePoint c r) (r • ContinuousLinearMap.id ℝ (CoordinateSpace n)) x := by
    simpa [ellipticRescalePoint] using ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul r).const_add c
  unfold coordinateDerivative
  have hc := ((hv _).hasFDerivAt.comp x hl).fderiv
  simp only [Function.comp_def] at hc
  rw [hc]
  simp

lemma coordinateHessian_ellipticRescale {v : CoordinateSpace n → ℝ}
    (hv : ContDiff ℝ ∞ v) (c : CoordinateSpace n) (r : ℝ) (x : CoordinateSpace n) :
    coordinateHessian (fun y => v (ellipticRescalePoint c r y)) x =
      r^2 • coordinateHessian v (ellipticRescalePoint c r x) := by
  ext i j
  have he : coordinateDerivative i (fun y => v (ellipticRescalePoint c r y)) =
      fun y => r*coordinateDerivative i v (ellipticRescalePoint c r y) :=
    funext (coordinateDerivative_ellipticRescale (hv.differentiable (by simp)) c r i)
  have hd : Differentiable ℝ (fun y => coordinateDerivative i v (ellipticRescalePoint c r y)) :=
    ((smooth_coordinateDerivative hv i).comp (contDiff_ellipticRescalePoint c r)).differentiable (by simp)
  change coordinateDerivative j (coordinateDerivative i (fun y => v (ellipticRescalePoint c r y))) x = _
  rw [he, coordinateDerivative_const_mul hd,
    coordinateDerivative_ellipticRescale ((smooth_coordinateDerivative hv i).differentiable (by simp))]
  change r*(r*coordinateHessian v (ellipticRescalePoint c r x) i j) = r^2*coordinateHessian v (ellipticRescalePoint c r x) i j
  ring

lemma linearizedMA_ellipticRescale {v : CoordinateSpace n → ℝ}
    (hv : ContDiff ℝ ∞ v) (A : Matrix (Fin n) (Fin n) ℝ)
    (c : CoordinateSpace n) (r : ℝ) (x : CoordinateSpace n) :
    linearizedMA A (fun y => v (ellipticRescalePoint c r y)) x =
      r^2 * linearizedMA A v (ellipticRescalePoint c r x) := by
  simp only [linearizedMA, coordinateHessian_ellipticRescale hv,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

lemma ellipticRescalePoint_norm (c x : CoordinateSpace n) {r : ℝ} (hr : 0 ≤ r) :
    ‖(coordinateEquiv n).symm (ellipticRescalePoint c r x) - (coordinateEquiv n).symm c‖ =
      r*‖(coordinateEquiv n).symm x‖ := by
  simp only [ellipticRescalePoint, map_add, map_smul, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hr]

/-- The real PDE, first coefficient derivatives, and forcing derivatives
all acquire their correct powers of the spatial scale. -/
theorem exists_scaled_interior_harnack {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ H : ℝ, 0 < H ∧
      ∀ (v f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (c : CoordinateSpace n) (r : ℝ),
      0 < r → ContDiff ℝ ∞ v → Differentiable ℝ f →
      (∀ i j, Differentiable ℝ (fun y => A y i j)) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < 2*r → 0 ≤ v y) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r → (A y).PosSemidef) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r → ∀ w : CoordinateSpace n,
        lam*‖(coordinateEquiv n).symm w‖^2 ≤ w ⬝ᵥ (A y *ᵥ w) ∧
        w ⬝ᵥ (A y *ᵥ w) ≤ Λ*‖(coordinateEquiv n).symm w‖^2) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r →
        ∀ k i j, r*|matrixCoordinateDerivative A k y i j| ≤ K) →
      ∀ F : ℝ, 0 ≤ F →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r → r^2*|f y| ≤ F) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r →
        ∀ k, r^3*|coordinateDerivative k f y| ≤ F) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r → linearizedMA (A y) v y = f y) →
      ∀ x y, ‖(coordinateEquiv n).symm x-(coordinateEquiv n).symm c‖ ≤ r/2 →
        ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ ≤ r/2 → v x ≤ H*(v y+F) := by
  obtain ⟨H,hH,harnack⟩ := exists_interior_harnack_with_bounded_forcing (n := n) hlam hΛ hK
  refine ⟨H,hH,?_⟩
  intro v f A c r hr hv hf hAd hn hA hEll hDA F hF hfb hDfb hP
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
  have hbound := harnack v' f' A' hv' hf' hAd'
    (fun z hz => hn (P z) (by rw [ellipticRescalePoint_norm _ _ hr.le]; nlinarith))
    (fun z hz => hA (P z) (hnear z hz)) (fun z hz => hEll (P z) (hnear z hz))
    (fun z hz k i j => by
      change |coordinateDerivative k (fun w => A (P w) i j) z| ≤ K
      rw [coordinateDerivative_ellipticRescale (hAd i j), abs_mul, abs_of_pos hr]
      exact hDA (P z) (hnear z hz) k i j) F hF
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
  intro x y hx hy
  let X := r⁻¹ • (x-c)
  let Y := r⁻¹ • (y-c)
  have hPX : P X = x := by dsimp [P, X, ellipticRescalePoint]; simp [smul_smul, hr.ne']
  have hPY : P Y = y := by dsimp [P, Y, ellipticRescalePoint]; simp [smul_smul, hr.ne']
  have hXN : ‖(coordinateEquiv n).symm X‖ ≤ 1/2 := by
    have he := ellipticRescalePoint_norm c X hr.le
    rw [show ellipticRescalePoint c r X = x from hPX] at he
    rw [he] at hx
    nlinarith
  have hYN : ‖(coordinateEquiv n).symm Y‖ ≤ 1/2 := by
    have he := ellipticRescalePoint_norm c Y hr.le
    rw [show ellipticRescalePoint c r Y = y from hPY] at he
    rw [he] at hy
    nlinarith
  simpa only [v', hPX, hPY] using hbound X Y hXN hYN

end GaussianTilt.MomentMapRegularity
