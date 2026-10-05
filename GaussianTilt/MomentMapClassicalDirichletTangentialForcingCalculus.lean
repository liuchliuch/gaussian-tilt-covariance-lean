import GaussianTilt.MomentMapClassicalDirichletInteriorCoefficientBounds
import GaussianTilt.MomentMapBoundaryRegularityBernsteinCalculus

/-! # Actual differentiation of the tangential-field forcing -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The literal source term after differentiating along the fixed boundary
chart tangent vector field. -/
def tangentialFieldForcing (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (u F β : CoordinateSpace n → ℝ) (a j : Fin n) (x : CoordinateSpace n) : ℝ :=
  coordinateDerivative a F x - β x*coordinateDerivative j F x -
    coordinateDerivative j u x*linearizedMA (A x) β x - 2*coordinateDerivative j β x

lemma differentiable_variable_linearizedMA {β : CoordinateSpace n → ℝ} (hβ : ContDiff ℝ ∞ β)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, Differentiable ℝ (fun x => A x i j)) :
    Differentiable ℝ (fun x => linearizedMA (A x) β x) := by
  unfold linearizedMA Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply]
  apply Differentiable.fun_sum
  intro i _
  apply Differentiable.fun_sum
  intro j _
  exact (hA i j).mul ((smooth_coordinateHessian hβ j i).differentiable (by simp))

lemma coordinateDerivative_variable_linearizedMA {β : CoordinateSpace n → ℝ} (hβ : ContDiff ℝ ∞ β)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, Differentiable ℝ (fun x => A x i j)) (k : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative k (fun y => linearizedMA (A y) β y) x =
      (matrixCoordinateDerivative A k x * coordinateHessian β x).trace +
        (A x * matrixCoordinateDerivative (coordinateHessian β) k x).trace := by
  rw [coordinateDerivative_variable_operator hβ hA]
  rw [linearizedMA,hessian_coordinateDerivative_eq_matrixDerivative hβ]

/-- The actual derivative contains only second source derivatives,
first inverse-coefficient derivatives, and fixed chart third derivatives. -/
theorem coordinateDerivative_tangentialFieldForcing
    {u F β : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hF : ContDiff ℝ ∞ F) (hβ : ContDiff ℝ ∞ β)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, Differentiable ℝ (fun x => A x i j)) (a j k : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative k (tangentialFieldForcing A u F β a j) x =
      coordinateHessian F x a k - coordinateDerivative k β x*coordinateDerivative j F x -
      β x*coordinateHessian F x j k - coordinateHessian u x j k*linearizedMA (A x) β x -
      coordinateDerivative j u x*((matrixCoordinateDerivative A k x*coordinateHessian β x).trace +
        (A x*matrixCoordinateDerivative (coordinateHessian β) k x).trace) - 2*coordinateHessian β x j k := by
  have hFa := ((smooth_coordinateDerivative hF a).differentiable (by simp) x).hasFDerivAt
  have hFj := ((smooth_coordinateDerivative hF j).differentiable (by simp) x).hasFDerivAt
  have hβd := (hβ.differentiable (by simp) x).hasFDerivAt
  have huj := ((smooth_coordinateDerivative hu j).differentiable (by simp) x).hasFDerivAt
  have hβj := ((smooth_coordinateDerivative hβ j).differentiable (by simp) x).hasFDerivAt
  have hL := (differentiable_variable_linearizedMA hβ hA x).hasFDerivAt
  have hd := ((hFa.sub (hβd.mul hFj)).sub (huj.mul hL)).sub (hβj.const_mul 2)
  change HasFDerivAt (tangentialFieldForcing A u F β a j) _ x at hd
  change (fderiv ℝ (tangentialFieldForcing A u F β a j) x) (Pi.single k 1) = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  change coordinateHessian F x a k -
    (β x*coordinateHessian F x j k+coordinateDerivative j F x*coordinateDerivative k β x) -
    (coordinateDerivative j u x*coordinateDerivative k (fun y => linearizedMA (A y) β y) x+
      linearizedMA (A x) β x*coordinateHessian u x j k) -
    2*coordinateHessian β x j k = _
  rw [coordinateDerivative_variable_linearizedMA hβ hA]
  ring

lemma contDiff_tangentialFieldForcing
    {u F β : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F)
    (hβ : ContDiff ℝ ∞ β) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j)) (a j : Fin n) :
    ContDiff ℝ ∞ (tangentialFieldForcing A u F β a j) := by
  have hL : ContDiff ℝ ∞ (fun x => linearizedMA (A x) β x) := by
    unfold linearizedMA Matrix.trace Matrix.diag
    simp only [Matrix.mul_apply]
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact (hA i j).mul (smooth_coordinateHessian hβ j i)
  exact (((smooth_coordinateDerivative hF a).sub (hβ.mul (smooth_coordinateDerivative hF j))).sub
    ((smooth_coordinateDerivative hu j).mul hL)).sub (contDiff_const.mul (smooth_coordinateDerivative hβ j))

end GaussianTilt.MomentMapRegularity
