import GaussianTilt.MomentMapSchauderConstantCoefficients
import GaussianTilt.MomentMapSchauderFreezing

/-!
# Coefficient freezing in the actual Euclidean Hessian norm

These estimates link the true Euclidean constant-coefficient Schauder theorem
to a variable coefficient field. The error terms contain the initial Hessian
Hölder bound with its explicit small coefficient.
-/
noncomputable section
open Matrix Set
open scoped BigOperators ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma abs_euclidean_bilinear_entry_le_norm
    (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) (i j : Fin n) :
    |B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤ ‖B‖ := by
  have hi := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i
  have hj := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one j
  have h₁ := (B (EuclideanSpace.basisFun (Fin n) ℝ i)).le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ j)
  have h₂ := B.le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ i)
  rw [hj, mul_one, Real.norm_eq_abs] at h₁
  rw [hi, mul_one] at h₂
  exact h₁.trans h₂

def euclideanHessianMatrix (u : KernelSpace n → ℝ) (x : KernelSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)

def euclideanFreezingResidual (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ) (u : KernelSpace n → ℝ) (x : KernelSpace n) : ℝ :=
  matrixContraction (A₀ - A x) (euclideanHessianMatrix u x)

lemma euclideanEllipticOperator_freeze (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ) (u : KernelSpace n → ℝ) (x : KernelSpace n) :
    euclideanEllipticOperator A₀ u x = euclideanEllipticOperator (A x) u x + euclideanFreezingResidual A₀ A u x := by
  change matrixContraction A₀ (euclideanHessianMatrix u x) =
    matrixContraction (A x) (euclideanHessianMatrix u x) + matrixContraction (A₀ - A x) (euclideanHessianMatrix u x)
  rw [matrixContraction_sub_left]
  ring

lemma euclideanFreezingResidual_abs_bound {A₀ : Matrix (Fin n) (Fin n) ℝ}
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} {u : KernelSpace n → ℝ}
    {ε M : ℝ} (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hA : ∀ x i j, |A₀ i j - A x i j| ≤ ε)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ M) (x : KernelSpace n) :
    |euclideanFreezingResidual A₀ A u x| ≤ (n : ℝ)^2 * ε * M := by
  apply (abs_matrixContraction_le hε hM (hA x) ?_).trans_eq (by simp only [Fintype.card_fin])
  intro i j
  exact (abs_euclidean_bilinear_entry_le_norm _ i j).trans (hH x)

lemma euclideanFreezingResidual_holder_bound {A₀ : Matrix (Fin n) (Fin n) ℝ}
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} {u : KernelSpace n → ℝ}
    {ε M K Q α : ℝ} (hε : 0 ≤ ε) (hM : 0 ≤ M) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hA : ∀ x i j, |A₀ i j - A x i j| ≤ ε)
    (hAH : ∀ x y i j, |A x i j - A y i j| ≤ K * ‖x - y‖ ^ α)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ M)
    (hHH : ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ Q * ‖x - y‖ ^ α)
    (x y : KernelSpace n) :
    |euclideanFreezingResidual A₀ A u x - euclideanFreezingResidual A₀ A u y| ≤
      ((n : ℝ)^2 * (ε * Q + K * M)) * ‖x - y‖ ^ α := by
  have hp := Real.rpow_nonneg (norm_nonneg (x-y)) α
  have hb := abs_matrixContraction_sub_le hε hM (mul_nonneg hK hp) (mul_nonneg hQ hp)
    (A := A₀ - A x) (C := A₀ - A y) (B := euclideanHessianMatrix u x) (D := euclideanHessianMatrix u y)
    (hA x) (fun i j => (abs_euclidean_bilinear_entry_le_norm _ i j).trans (hH y)) ?_ ?_
  · change |euclideanFreezingResidual A₀ A u x - euclideanFreezingResidual A₀ A u y| ≤ _ at hb
    exact hb.trans_eq (by simp only [Fintype.card_fin]; ring)
  · intro i j
    simp only [Matrix.sub_apply]
    have he : (A₀ i j - A x i j) - (A₀ i j - A y i j) = -(A x i j - A y i j) := by ring
    rw [he, abs_neg]
    exact hAH x y i j
  · intro i j
    have he := abs_euclidean_bilinear_entry_le_norm
      (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y) i j
    exact he.trans (hHH x y)

end GaussianTilt.MomentMapSchauder
