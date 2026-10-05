import GaussianTilt.MomentMapSchauderDifferences

/-!
# Quantitative coefficient freezing for the actual nondivergence operator

Freezing the matrix at a center moves a literal contraction of the coefficient
oscillation and the Hessian to the right-hand side. Both its supremum bound
and its Hölder modulus are proved with explicit dimension factors.
This module does not assume or assert an interior Schauder theorem.
-/
noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.Letwin
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise contraction of two matrices. -/
def matrixContraction (A B : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

lemma matrixContraction_add_left (A B C : Matrix ι ι ℝ) :
    matrixContraction (A + B) C = matrixContraction A C + matrixContraction B C := by
  simp [matrixContraction, add_mul, Finset.sum_add_distrib]

lemma matrixContraction_sub_left (A B C : Matrix ι ι ℝ) :
    matrixContraction (A - B) C = matrixContraction A C - matrixContraction B C := by
  simp [matrixContraction, sub_mul, Finset.sum_sub_distrib]

lemma matrixContraction_sub_right (A B C : Matrix ι ι ℝ) :
    matrixContraction A (B - C) = matrixContraction A B - matrixContraction A C := by
  simp [matrixContraction, mul_sub, Finset.sum_sub_distrib]

lemma abs_matrixContraction_le {A B : Matrix ι ι ℝ} {U V : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hA : ∀ i j, |A i j| ≤ U) (hB : ∀ i j, |B i j| ≤ V) :
    |matrixContraction A B| ≤ (Fintype.card ι : ℝ) ^ 2 * U * V := by
  calc
    _ ≤ ∑ i, ∑ j, |A i j * B i j| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : ι, ∑ _j : ι, U * V := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hA i j) (hB i j) (abs_nonneg _) hU
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The product Hölder estimate for the actual matrix contraction. -/
lemma abs_matrixContraction_sub_le {A B C D : Matrix ι ι ℝ} {U V P Q : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hA : ∀ i j, |A i j| ≤ U) (hD : ∀ i j, |D i j| ≤ V)
    (hAC : ∀ i j, |A i j - C i j| ≤ P)
    (hBD : ∀ i j, |B i j - D i j| ≤ Q) :
    |matrixContraction A B - matrixContraction C D| ≤
      (Fintype.card ι : ℝ) ^ 2 * (U * Q + P * V) := by
  have he : matrixContraction A B - matrixContraction C D =
      matrixContraction A (B - D) + matrixContraction (A - C) D := by
    rw [matrixContraction_sub_right, matrixContraction_sub_left]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  have hb := abs_matrixContraction_le hU hQ hA hBD
  have hc := abs_matrixContraction_le hP hV hAC hD
  calc
    _ ≤ (Fintype.card ι : ℝ) ^ 2 * U * Q + (Fintype.card ι : ℝ) ^ 2 * P * V :=
      add_le_add hb hc
    _ = _ := by ring

/-- The nondivergence operator, with actual iterated coordinate derivatives. -/
def coordinateEllipticOperator {n : ℕ}
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (u : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  matrixContraction (A x) (coordinateHessian u x)

/-- The residual after freezing a coefficient at one matrix. -/
def freezingResidual {n : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (u : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  matrixContraction (A₀ - A x) (coordinateHessian u x)

/-- Freezing is an exact identity of the literal PDE, not a postulated
linearization estimate. -/
theorem coordinateEllipticOperator_freeze {n : ℕ}
    (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (u : CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    coordinateEllipticOperator (fun _ => A₀) u x =
      coordinateEllipticOperator A u x + freezingResidual A₀ A u x := by
  simp only [coordinateEllipticOperator, freezingResidual, matrixContraction_sub_left]
  ring

/-- Supremum estimate for the frozen-coefficient error. -/
theorem freezingResidual_abs_le {n : ℕ} {A₀ : Matrix (Fin n) (Fin n) ℝ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {u : CoordinateSpace n → ℝ}
    {S : Set (CoordinateSpace n)} {osc H₀ : ℝ} (hosc : 0 ≤ osc) (hH₀ : 0 ≤ H₀)
    (hA : ∀ x ∈ S, ∀ i j, |A₀ i j - A x i j| ≤ osc)
    (hH : ∀ x ∈ S, ∀ i j, |coordinateHessian u x i j| ≤ H₀) :
    ∀ x ∈ S, |freezingResidual A₀ A u x| ≤ (n : ℝ) ^ 2 * osc * H₀ := by
  intro x hx
  simpa only [Fintype.card_fin] using abs_matrixContraction_le hosc hH₀ (hA x hx) (hH x hx)

/-- Hölder estimate for the frozen-coefficient error. The coefficient in
front of the Hessian Hölder bound is its small local oscillation. -/
theorem freezingResidual_holder_bound {n : ℕ} {A₀ : Matrix (Fin n) (Fin n) ℝ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {u : CoordinateSpace n → ℝ}
    {S : Set (CoordinateSpace n)} {osc H₀ Hα Cα α : ℝ}
    (hosc : 0 ≤ osc) (hH₀ : 0 ≤ H₀) (hHα : 0 ≤ Hα) (hCα : 0 ≤ Cα)
    (hA₀ : ∀ x ∈ S, ∀ i j, |A₀ i j - A x i j| ≤ osc)
    (hH : ∀ x ∈ S, ∀ i j, |coordinateHessian u x i j| ≤ H₀)
    (hA : ∀ x ∈ S, ∀ y ∈ S, ∀ i j, |A x i j - A y i j| ≤ Cα * ‖x - y‖ ^ α)
    (hHH : ∀ x ∈ S, ∀ y ∈ S, ∀ i j,
      |coordinateHessian u x i j - coordinateHessian u y i j| ≤ Hα * ‖x - y‖ ^ α) :
    ∀ x ∈ S, ∀ y ∈ S,
      |freezingResidual A₀ A u x - freezingResidual A₀ A u y| ≤
        ((n : ℝ) ^ 2 * (osc * Hα + Cα * H₀)) * ‖x - y‖ ^ α := by
  intro x hx y hy
  have hpow := Real.rpow_nonneg (norm_nonneg (x - y)) α
  have hb := abs_matrixContraction_sub_le hosc hH₀ (mul_nonneg hCα hpow) (mul_nonneg hHα hpow)
    (hA₀ x hx) (hH y hy) (A := A₀ - A x) (C := A₀ - A y)
    (B := coordinateHessian u x) (D := coordinateHessian u y) ?_ (hHH x hx y hy)
  · change |freezingResidual A₀ A u x - freezingResidual A₀ A u y| ≤ _ at hb
    apply hb.trans
    simp only [Fintype.card_fin]
    exact le_of_eq (by ring)
  · intro i j
    simp only [Matrix.sub_apply]
    have he : (A₀ i j - A x i j) - (A₀ i j - A y i j) = -(A x i j - A y i j) := by ring
    rw [he, abs_neg]
    exact hA x hx y hy i j

end GaussianTilt.MomentMapSchauder
