import GaussianTilt.MomentMapSchauderEuclideanFreezing
import GaussianTilt.MomentMapSchauderCutoff

/-! # Exact Euclidean cutoff calculus for the nondivergence operator -/
noncomputable section
open Matrix Set
open scoped BigOperators ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic

section Product
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma secondFrechet_mul_apply {u χ : E → ℝ} (hu : ContDiff ℝ 2 u) (hχ : ContDiff ℝ 2 χ)
    (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => χ y * u y)) x v w =
      χ x * fderiv ℝ (fderiv ℝ u) x v w + u x * fderiv ℝ (fderiv ℝ χ) x v w +
      fderiv ℝ χ x v * fderiv ℝ u x w + fderiv ℝ u x v * fderiv ℝ χ x w := by
  have hud := hu.differentiable (by norm_num)
  have hχd := hχ.differentiable (by norm_num)
  have hDu := (hu.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl
  have hDχ := (hχ.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl
  have he : fderiv ℝ (fun y => χ y * u y) =
      (fun y => χ y • fderiv ℝ u y + u y • fderiv ℝ χ y) := by
    funext y
    exact fderiv_fun_mul (hχd y) (hud y)
  rw [he, fderiv_fun_add (f := fun y => χ y • fderiv ℝ u y)
    (g := fun y => u y • fderiv ℝ χ y) ((hχd x).smul (hDu x)) ((hud x).smul (hDχ x)),
    fderiv_fun_smul (hχd x) (hDu x), fderiv_fun_smul (hud x) (hDχ x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

end Product
variable {n : ℕ}

def euclideanEllipticCross (A : Matrix (Fin n) (Fin n) ℝ)
    (χ u : KernelSpace n → ℝ) (x : KernelSpace n) : ℝ :=
  ∑ i, ∑ j, A i j * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i) *
    fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j)

/-- The literal Euclidean cutoff equation does not differentiate its
coefficient matrix, and so applies at Hölder coefficient regularity. -/
theorem euclideanEllipticOperator_mul (A : Matrix (Fin n) (Fin n) ℝ)
    {u χ : KernelSpace n → ℝ} (hu : ContDiff ℝ 2 u) (hχ : ContDiff ℝ 2 χ)
    (x : KernelSpace n) (hA : A.IsSymm) :
    euclideanEllipticOperator A (fun y => χ y * u y) x =
      χ x * euclideanEllipticOperator A u x + u x * euclideanEllipticOperator A χ x +
        2 * euclideanEllipticCross A χ u x := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hswap : (∑ i, ∑ j, A i j * (fderiv ℝ u x (e i) * fderiv ℝ χ x (e j))) =
      euclideanEllipticCross A χ u x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hA.apply i j]
    ring
  simp only [euclideanEllipticOperator, secondFrechet_mul_apply hu hχ, mul_add, Finset.sum_add_distrib]
  rw [hswap]
  simp only [euclideanEllipticCross, Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end GaussianTilt.MomentMapSchauder
