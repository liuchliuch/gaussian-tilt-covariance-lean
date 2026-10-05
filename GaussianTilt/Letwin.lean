import Mathlib
import GaussianTilt.Quadratic
import GaussianTilt.LetwinIntegration
import GaussianTilt.LetwinExhaustion
import GaussianTilt.LetwinMongeAmpere
import GaussianTilt.LetwinPositivity
import GaussianTilt.LetwinBlock
import GaussianTilt.LetwinPerturbation

/-!
# Analytic and finite-dimensional steps in Letwin's variance argument

The source is Brayden Letwin, `arXiv:2607.24164v1`, Theorem 1.2.
The imported modules prove the weighted integration-by-parts identity A3,
the Hessian expectation identity 2.3 for actual moment potentials, and the
full regular Monge--Ampère cutoff and conservation arguments A4--A5, the
Hessian equation and positivity in 2.4, and local convexity of the functional
Brascamp--Lieb perturbation. This file
proves the tensor comparison in equation (2.12), including its specialization
to actual third coordinate derivatives. It does not postulate moment-map
existence or a quadratic variance inequality. The later `LetwinTraceBound` and `LetwinQuadraticDuality` modules prove the
full regular integrated Hessian trace bound and sharp quadratic Stein-duality
budget. Construction and regularity of the moment map and the weighted
negative-Sobolev variance theorem are separate analytic dependencies.
-/

noncomputable section
open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory

namespace GaussianTilt.Letwin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The square of the real Hilbert--Schmidt norm. -/
def hsSquare (A : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

theorem hsSquare_nonneg (A : Matrix ι ι ℝ) : 0 ≤ hsSquare A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem hsSquare_eq_trace (A : Matrix ι ι ℝ) :
    hsSquare A = Matrix.trace (A * A.transpose) := by
  simp [hsSquare, Matrix.trace, Matrix.mul_apply, pow_two]

theorem hsSquare_eq_trace_square (A : Matrix ι ι ℝ) (hA : A.IsSymm) :
    hsSquare A = Matrix.trace (A ^ 2) := by
  rw [hsSquare_eq_trace, hA.eq, pow_two]

/-- An exact sum-of-squares certificate for the matrix trace comparison.
It bypasses choosing eigenvectors in the normalized tensor argument. -/
theorem commutator_hsSquare (B T : Matrix ι ι ℝ)
    (hB : B.IsSymm) (hT : T.IsSymm) :
    hsSquare (B * T - T * B) =
      2 * (Matrix.trace (B ^ 2 * T ^ 2) - Matrix.trace (B * T * B * T)) := by
  rw [hsSquare_eq_trace]
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, hB.eq, hT.eq,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
  have h₁ : Matrix.trace (B * T * (T * B)) = Matrix.trace (B ^ 2 * T ^ 2) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (B * T * T) B]
    congr 1
    noncomm_ring
  have h₂ : Matrix.trace (T * B * (B * T)) = Matrix.trace (B ^ 2 * T ^ 2) := by
    calc
      Matrix.trace (T * B * (B * T)) = Matrix.trace (T * (B * B * T)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace ((B * B * T) * T) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (B ^ 2 * T ^ 2) := by
        congr 1
        noncomm_ring
  have h₃ : Matrix.trace (T * B * (T * B)) = Matrix.trace (B * T * B * T) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (T * B * T) B]
    congr 1
    noncomm_ring
  rw [h₁, h₂, h₃]
  simp only [← Matrix.mul_assoc]
  ring

theorem trace_alternating_le (B T : Matrix ι ι ℝ)
    (hB : B.IsSymm) (hT : T.IsSymm) :
    Matrix.trace (B * T * B * T) ≤ Matrix.trace (B ^ 2 * T ^ 2) := by
  have h := hsSquare_nonneg (B * T - T * B)
  rw [commutator_hsSquare B T hB hT] at h
  linarith

/-- Equation (2.12) after simultaneous normalization and diagonalization.
Only the indicated transposition symmetry of the third derivative is needed. -/
theorem symmetric_tensor_gap (b : ι → ℝ) (T : ι → ι → ι → ℝ)
    (hT : ∀ i j k, T i j k = T j i k) :
    (∑ i, ∑ j, ∑ k, b i ^ 2 * T i j k ^ 2) -
      (∑ i, ∑ j, ∑ k, b i * b j * T i j k ^ 2) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k, (b i - b j) ^ 2 * T i j k ^ 2 := by
  have hswap : (∑ i, ∑ j, ∑ k, b j ^ 2 * T i j k ^ 2) =
      (∑ i, ∑ j, ∑ k, b i ^ 2 * T i j k ^ 2) := by
    rw [Finset.sum_comm]
    congr 1
    funext i
    congr 1
    funext j
    simp only [hT j i]
  have hpoint : (∑ i, ∑ j, ∑ k, (b i - b j) ^ 2 * T i j k ^ 2) =
      (∑ i, ∑ j, ∑ k, b i ^ 2 * T i j k ^ 2) +
      (∑ i, ∑ j, ∑ k, b j ^ 2 * T i j k ^ 2) -
      2 * (∑ i, ∑ j, ∑ k, b i * b j * T i j k ^ 2) := by
    have hterm (i j k : ι) : (b i - b j) ^ 2 * T i j k ^ 2 =
        b i ^ 2 * T i j k ^ 2 + b j ^ 2 * T i j k ^ 2 -
          2 * (b i * b j * T i j k ^ 2) := by ring
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  rw [hpoint, hswap]
  ring

theorem symmetric_tensor_comparison (b : ι → ℝ) (T : ι → ι → ι → ℝ)
    (hT : ∀ i j k, T i j k = T j i k) :
    (∑ i, ∑ j, ∑ k, b i * b j * T i j k ^ 2) ≤
      (∑ i, ∑ j, ∑ k, b i ^ 2 * T i j k ^ 2) := by
  have h := symmetric_tensor_gap b T hT
  have hn : 0 ≤ ∑ i, ∑ j, ∑ k, (b i - b j) ^ 2 * T i j k ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

/-- Equation (2.12) for the actual third derivative tensor of a smooth
potential. Its required transposition symmetry follows from Schwarz's theorem. -/
theorem coordinateThirdDerivative_comparison {n : ℕ}
    {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x : Fin n → ℝ) (b : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, b i * b j * coordinateThirdDerivative φ x i j k ^ 2) ≤
      (∑ i, ∑ j, ∑ k, b i ^ 2 * coordinateThirdDerivative φ x i j k ^ 2) := by
  exact symmetric_tensor_comparison b (coordinateThirdDerivative φ x)
    (coordinateThirdDerivative_symm (hφ.of_le (by norm_num)) x)

end GaussianTilt.Letwin
