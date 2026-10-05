import GaussianTilt.MomentMapSchauderLinearThirdOrder

/-! # Actual differentiation of variable-coefficient elliptic equations -/
noncomputable section
set_option maxHeartbeats 1000000
open Matrix Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma contDiff_kernelDirectionalDerivative {m : WithTop ℕ∞} {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ (m + 1) u) (v : KernelSpace n) :
    ContDiff ℝ m (kernelDirectionalDerivative v u) :=
  (hu.fderiv_right le_rfl).clm_apply contDiff_const

lemma directional_derivative_secondFrechet {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 3 u) (v x a b : KernelSpace n) :
    fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y a b) x v =
      fderiv ℝ (fderiv ℝ (kernelDirectionalDerivative v u)) x a b := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hDv : ContDiff ℝ 2 (kernelDirectionalDerivative v u) :=
    contDiff_kernelDirectionalDerivative hu v
  have hDb : ContDiff ℝ 2 (kernelDirectionalDerivative b u) :=
    contDiff_kernelDirectionalDerivative hu b
  have he : kernelDirectionalDerivative a (kernelDirectionalDerivative b (kernelDirectionalDerivative v u)) =
      kernelDirectionalDerivative v (kernelDirectionalDerivative a (kernelDirectionalDerivative b u)) := by
    rw [kernelDirectionalDerivative_commute hu2 b v,
      kernelDirectionalDerivative_commute hDb a v]
  have hh := congrFun he x
  change directionalHessian (kernelDirectionalDerivative v u) x b a =
    fderiv ℝ (fun y => directionalHessian u y b a) x v at hh
  simpa only [directionalHessian_eq_secondFrechet hDv, directionalHessian_eq_secondFrechet hu2] using hh.symm

lemma contDiff_secondFrechet_entry {m : WithTop ℕ∞} {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ (m + 2) u) (a b : KernelSpace n) :
    ContDiff ℝ m (fun x => fderiv ℝ (fderiv ℝ u) x a b) := by
  have hd : ContDiff ℝ (m + 1) (fderiv ℝ u) := hu.fderiv_right (by norm_num [add_assoc])
  exact ((hd.fderiv_right le_rfl).clm_apply contDiff_const).clm_apply contDiff_const

def ellipticDerivativeError (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (u : KernelSpace n → ℝ) (v x : KernelSpace n) : ℝ :=
  ∑ i, ∑ j, fderiv ℝ (fun y => A y i j) x v * fderiv ℝ (fderiv ℝ u) x
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)

/-- The actual product rule exposes exactly the lower-order forcing error. -/
theorem directional_ellipticOperator_product_rule {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 3 u) {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) (v x : KernelSpace n) :
    fderiv ℝ (fun y => euclideanEllipticOperator (A y) u y) x v =
      euclideanEllipticOperator (A x) (kernelDirectionalDerivative v u) x + ellipticDerivativeError A u v x := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hH (i j : Fin n) : ContDiff ℝ 1 (fun y => fderiv ℝ (fderiv ℝ u) y (b i) (b j)) :=
    contDiff_secondFrechet_entry hu (b i) (b j)
  have hprod (i j : Fin n) := ((hA i j).mul (hH i j)).differentiable le_rfl
  simp only [euclideanEllipticOperator, ellipticDerivativeError, ← Finset.sum_add_distrib]
  rw [fderiv_fun_sum (A := fun i y => ∑ j, A y i j * fderiv ℝ (fderiv ℝ u) y (b i) (b j))
    (fun i _ => ((ContDiff.sum (fun j _ => (hA i j).mul (hH i j))).differentiable le_rfl x))]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_fun_sum (A := fun j y => A y i j * fderiv ℝ (fderiv ℝ u) y (b i) (b j))
    (fun j _ => hprod i j x)]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_mul ((hA i j).differentiable le_rfl x) ((hH i j).differentiable le_rfl x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    directional_derivative_secondFrechet hu]
  ring

/-- A literal equation differentiates to a literal equation; no formal
commutator or differentiated PDE is passed as a premise. -/
theorem differentiated_elliptic_equation {u f : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 3 u) {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (heq : ∀ x, euclideanEllipticOperator (A x) u x = f x) (v x : KernelSpace n) :
    euclideanEllipticOperator (A x) (kernelDirectionalDerivative v u) x =
      kernelDirectionalDerivative v f x - ellipticDerivativeError A u v x := by
  have hh := directional_ellipticOperator_product_rule hu hA v x
  rw [show (fun y => euclideanEllipticOperator (A y) u y) = f from funext heq] at hh
  change fderiv ℝ f x v = _ at hh
  dsimp [kernelDirectionalDerivative]
  linarith

end GaussianTilt.MomentMapSchauder
