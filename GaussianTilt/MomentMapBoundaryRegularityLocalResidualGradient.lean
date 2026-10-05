import GaussianTilt.MomentMapBoundaryRegularityLocalGradient
import GaussianTilt.MomentMapBoundaryRegularityWithinNormalDerivative

/-! # Interior gradient control of the genuine within-boundary affine residual -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma within_boundary_affine_residual_bound {u : CoordinateSpace n → ℝ}
    {j : Fin n} {B r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hb : ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |u x| ≤ B*x j)
    {D : CoordinateSpace n →L[ℝ] ℝ} (hu : HasFDerivWithinAt u D (flatClosedHalfBall j) 0) :
    ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ r → 0 ≤ x j →
      |u x-D (Pi.single j 1)*x j| ≤ boundaryQuotientOscillation u j r*x j := by
  have hp := within_boundary_normal_mem_quotient_interval hr hr1 hb (y := 0)
    (by simpa using hr) (by simp) hu
  intro x hx hj
  have hux := boundaryQuotient_ball_bounds hr1 hb x hx hj
  have hlo := mul_le_mul_of_nonneg_right hp.1 hj
  have hup := mul_le_mul_of_nonneg_right hp.2 hj
  unfold boundaryQuotientOscillation
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma coordinateDerivative_sub_at_local {u v : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) (i : Fin n) :
    coordinateDerivative i (fun y => u y-v y) x=coordinateDerivative i u x-coordinateDerivative i v x := by
  unfold coordinateDerivative
  rw [fderiv_fun_sub hu hv]
  rfl

theorem exists_local_boundary_residual_gradient_bound {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (j : Fin n) (u f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (M B : ℝ) (D : CoordinateSpace n →L[ℝ] ℝ),
      0 ≤ M → 0 ≤ B → LocalFlatEllipticSystem j u f A lam Λ K M →
      HasFDerivWithinAt u D (flatClosedHalfBall j) 0 →
      (∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → 0 ≤ y j → |u y| ≤ B*y j) →
      ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1/4 → 0 < x j →
      ∀ i, |coordinateDerivative i u x-D (Pi.single j 1)*(if i=j then 1 else 0)| ≤
        C*(boundaryQuotientOscillation u j (2*‖(coordinateEquiv n).symm x‖)+M*x j) := by
  obtain ⟨C,hC,hgrad⟩ := exists_local_scaled_gradient_bound (n := n) hlam hΛ hK
  refine ⟨8*C,by positivity,?_⟩
  intro j u f A M B D hM hB hs hD hb x hx ht i
  let t := x j
  let d := ‖(coordinateEquiv n).symm x‖
  let r := t/4
  let W := boundaryQuotientOscillation u j (2*d)
  let p := D (Pi.single j 1)
  let v : CoordinateSpace n → ℝ := fun y => u y-p*y j
  have htd : t ≤ d := (le_abs_self _).trans (abs_coordinate_le_euclidean_norm x j)
  have hd : 0 < d := ht.trans_le htd
  have hr : 0 < r := div_pos ht (by norm_num)
  have h2d : 2*d ≤ 1 := by dsimp only [d]; linarith
  have hW : 0 ≤ W := boundaryQuotientOscillation_nonneg (by positivity) h2d hb
  have hcoord : ContDiff ℝ ∞ (fun y : CoordinateSpace n => y j) := by fun_prop
  have hv : ContDiffOn ℝ ∞ v (flatHalfBall j) :=
    hs.smooth_interior.sub (contDiffOn_const.mul hcoord.contDiffOn)
  have hnear (y : CoordinateSpace n)
      (hy : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ ≤ 2*r) :
      y ∈ flatHalfBall j ∧ ‖(coordinateEquiv n).symm y‖ ≤ 2*d ∧ y j ≤ 2*t ∧ r ≤ y j := by
    have hc := abs_coordinate_le_euclidean_norm (y-x) j
    simp only [Pi.sub_apply,map_sub] at hc
    have hn := norm_add_le ((coordinateEquiv n).symm y-(coordinateEquiv n).symm x) ((coordinateEquiv n).symm x)
    rw [sub_add_cancel] at hn
    have hlo := (abs_le.mp hc).1
    have hup := (abs_le.mp hc).2
    change -(‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖) ≤ y j-t at hlo
    change y j-t ≤ ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ at hup
    change ‖(coordinateEquiv n).symm y‖ ≤ ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖+d at hn
    have htpos : 0 < t := ht
    have hd4 : d ≤ 1/4 := hx
    dsimp only [r] at hy ⊢
    refine ⟨⟨?_,?_⟩,?_,?_,?_⟩ <;> nlinarith
  have hnear1 (y : CoordinateSpace n)
      (hy : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r) :=
    hnear y (show ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ ≤ 2*r by linarith)
  have hU (y : CoordinateSpace n)
      (hy : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < 2*r) : |v y| ≤ 2*t*W := by
    have hgeom := hnear y hy.le
    have hres := within_boundary_affine_residual_bound (show 0 < 2*d by positivity) h2d hb hD
      y hgeom.2.1 hgeom.1.2.le
    have hm := mul_le_mul_of_nonneg_left hgeom.2.2.1 hW
    change |v y| ≤ W*y j at hres
    nlinarith
  have hAb (y : CoordinateSpace n)
      (hy : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r) (k a b : Fin n) :
      r*|matrixCoordinateDerivative A k y a b| ≤ K := by
    have hg := hnear1 y hy
    have hh := hs.coefficient_bound y hg.1 k a b
    nlinarith [mul_le_mul_of_nonneg_right hg.2.2.2 (abs_nonneg (matrixCoordinateDerivative A k y a b))]
  have hDb (y : CoordinateSpace n)
      (hy : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r) (k : Fin n) :
      r^3*|coordinateDerivative k f y| ≤ r^2*M := by
    have hg := hnear1 y hy
    have hh := hs.forcing_derivative_bound y hg.1 k
    have hlow : r*|coordinateDerivative k f y| ≤ M := by
      nlinarith [mul_le_mul_of_nonneg_right hg.2.2.2 (abs_nonneg (coordinateDerivative k f y))]
    have hm := mul_le_mul_of_nonneg_left hlow (sq_nonneg r)
    nlinarith
  have hPv (y : CoordinateSpace n)
      (hy : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r) : linearizedMA (A y) v y=f y := by
    have hu2 := contDiffAt_infty.mp (hs.contDiffAt_u (hnear1 y hy).1) 2
    rw [linearizedMA_sub_at _ hu2 (contDiffAt_const.mul (contDiff_infty.mp hcoord 2).contDiffAt),
      linearizedMA_const_mul_at _ (contDiff_infty.mp hcoord 2).contDiffAt]
    have hz : linearizedMA (A y) (fun z => z j) y=0 := by
      simp only [linearizedMA,coordinateHessian_coordinate,Matrix.mul_zero,Matrix.trace_zero]
    rw [hz,mul_zero,sub_zero]
    exact hs.equation y (hnear1 y hy).1
  have hg := hgrad v f A (flatHalfBall j) x r (2*t*W) (r^2*M) (isOpen_flatHalfBall j)
    hr (by positivity) (by positivity) hv hs.forcing_smooth hs.coefficient_smooth
    (fun y hy => (hnear y hy).1) hU
    (fun y hy => (hs.positive y (hnear1 y hy).1).posSemidef)
    (fun y hy => hs.elliptic y (hnear1 y hy).1) hAb
    (fun y hy => mul_le_mul_of_nonneg_left (hs.forcing_bound y (hnear1 y hy).1) (sq_nonneg r)) hDb hPv i
  have hxU : x ∈ flatHalfBall j := ⟨by linarith,ht⟩
  have hux := (hs.contDiffAt_u hxU).differentiableAt (by simp)
  have hpx : DifferentiableAt ℝ (fun y : CoordinateSpace n => p*y j) x :=
    ((hcoord.differentiable (by simp)) x).const_mul p
  have hDv : coordinateDerivative i v x=coordinateDerivative i u x-p*(if i=j then 1 else 0) := by
    rw [coordinateDerivative_sub_at_local hux hpx,
      coordinateDerivative_const_mul_at (hcoord.differentiable (by simp) x),coordinateDerivative_coordinate]
  rw [hDv] at hg
  change |coordinateDerivative i u x-p*(if i=j then 1 else 0)| ≤ 8*C*(W+M*t)
  dsimp only [r] at hg
  have htpos : 0 < t := ht
  have hm : 0 ≤ C*M*t^2 := by positivity
  nlinarith

end GaussianTilt.MomentMapRegularity
