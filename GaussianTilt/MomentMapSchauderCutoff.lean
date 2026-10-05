import GaussianTilt.MomentMapSchauderFreezing
import GaussianTilt.LetwinBochner

/-!
# Actual cutoff product calculus for nondivergence equations

Only the potential and cutoff are differentiated. Coefficients need no
first derivatives, as required in a Schauder argument with Hölder matrices.
-/
noncomputable section
open Matrix Set
open scoped BigOperators ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.Letwin

lemma coordinateHessian_mul {n : ℕ} {u χ : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) (hχ : ContDiff ℝ 2 χ) (x : CoordinateSpace n) (i j : Fin n) :
    coordinateHessian (fun y => χ y * u y) x i j =
      χ x * coordinateHessian u x i j + u x * coordinateHessian χ x i j +
        coordinateDerivative i χ x * coordinateDerivative j u x +
        coordinateDerivative j χ x * coordinateDerivative i u x := by
  have hud := hu.differentiable (by norm_num)
  have hχd := hχ.differentiable (by norm_num)
  have hDχ := (contDiff_coordinateDerivative hχ (m := 1) (by norm_num) i).differentiable le_rfl
  have hDu := (contDiff_coordinateDerivative hu (m := 1) (by norm_num) i).differentiable le_rfl
  have he : coordinateDerivative i (fun y => χ y * u y) =
      (fun y => coordinateDerivative i χ y * u y + χ y * coordinateDerivative i u y) :=
    funext (coordinateDerivative_mul hχd hud i)
  change coordinateDerivative j (coordinateDerivative i (fun y => χ y * u y)) x = _
  rw [he, coordinateDerivative_add (f := fun y => coordinateDerivative i χ y * u y)
      (g := fun y => χ y * coordinateDerivative i u y) (hDχ.mul hud) (hχd.mul hDu),
    coordinateDerivative_mul hDχ hud, coordinateDerivative_mul hχd hDu]
  simp only [coordinateHessian]
  ring

/-- The exact cross-gradient term in the nondivergence product rule. -/
def coordinateEllipticCross {n : ℕ}
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (χ u : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  ∑ i, ∑ j, A x i j * coordinateDerivative i χ x * coordinateDerivative j u x

/-- Product rule for the actual nondivergence PDE. No differentiability of
its coefficient matrix is requested or used. -/
theorem coordinateEllipticOperator_mul {n : ℕ}
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    {u χ : CoordinateSpace n → ℝ} (hu : ContDiff ℝ 2 u) (hχ : ContDiff ℝ 2 χ)
    (x : CoordinateSpace n) (hA : (A x).IsSymm) :
    coordinateEllipticOperator A (fun y => χ y * u y) x =
      χ x * coordinateEllipticOperator A u x + u x * coordinateEllipticOperator A χ x +
        2 * coordinateEllipticCross A χ u x := by
  have hswap : (∑ i, ∑ j, A x i j * coordinateDerivative j χ x * coordinateDerivative i u x) =
      coordinateEllipticCross A χ u x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hA.apply i j]
  simp only [coordinateEllipticOperator, matrixContraction, coordinateHessian_mul hu hχ,
    mul_add, Finset.sum_add_distrib]
  rw [show (∑ i, ∑ j, A x i j * (coordinateDerivative j χ x * coordinateDerivative i u x)) =
      coordinateEllipticCross A χ u x by simpa only [mul_assoc] using hswap]
  simp only [coordinateEllipticCross, Finset.mul_sum]
  repeat' rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A literal PDE gives the literal cutoff PDE used to pass to a
whole-space compact-support estimate. -/
theorem coordinateEllipticOperator_cutoff_equation {n : ℕ}
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    {u χ f : CoordinateSpace n → ℝ} (hu : ContDiff ℝ 2 u) (hχ : ContDiff ℝ 2 χ)
    {S : Set (CoordinateSpace n)} (hA : ∀ x ∈ S, (A x).IsSymm)
    (heq : ∀ x ∈ S, coordinateEllipticOperator A u x = f x) :
    ∀ x ∈ S, coordinateEllipticOperator A (fun y => χ y * u y) x =
      χ x * f x + u x * coordinateEllipticOperator A χ x + 2 * coordinateEllipticCross A χ u x := by
  intro x hx
  rw [coordinateEllipticOperator_mul A hu hχ x (hA x hx), heq x hx]

/-- Scalar product Hölder estimate, in the literal supnorm/seminorm data
used to bound cutoff error terms. -/
theorem holder_product_bound {E : Type*} [NormedAddCommGroup E]
    {f g : E → ℝ} {S : Set E} {F G C D α : ℝ}
    (hF : 0 ≤ F) (hG : 0 ≤ G) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ x ∈ S, |f x| ≤ F) (hg : ∀ x ∈ S, |g x| ≤ G)
    (hfh : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ C * ‖x - y‖ ^ α)
    (hgh : ∀ x ∈ S, ∀ y ∈ S, |g x - g y| ≤ D * ‖x - y‖ ^ α) :
    ∀ x ∈ S, ∀ y ∈ S,
      |f x * g x - f y * g y| ≤ (F * D + G * C) * ‖x - y‖ ^ α := by
  intro x hx y hy
  have hp := Real.rpow_nonneg (norm_nonneg (x - y)) α
  calc
    _ = |f x * (g x - g y) + (f x - f y) * g y| := by congr 1; ring
    _ ≤ |f x * (g x - g y)| + |(f x - f y) * g y| := abs_add_le _ _
    _ ≤ F * (D * ‖x - y‖ ^ α) + (C * ‖x - y‖ ^ α) * G := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul (hf x hx) (hgh x hx y hy) (abs_nonneg _) hF)
        (mul_le_mul (hfh x hx y hy) (hg y hy) (abs_nonneg _) (mul_nonneg hC hp))
    _ = _ := by ring

end GaussianTilt.MomentMapSchauder
