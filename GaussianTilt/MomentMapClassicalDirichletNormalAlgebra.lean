import GaussianTilt.MomentMapClassicalDirichletBarriers
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The actual normal-Hessian completion estimate

The determinant equation determines the normal entry through the Schur
complement of the tangential block. This converts genuine tangential
nondegeneracy and mixed-derivative bounds into a normal-derivative bound.
-/
noncomputable section
open Matrix
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normalBlockMatrix (A : Matrix ι ι ℝ) (b : ι → ℝ) (c : ℝ) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  Matrix.fromBlocks A (fun i _ => b i) (fun _ j => b j) (fun _ _ => c)

/-- Exact scalar Schur complement for the actual normal block. -/
theorem normalBlockMatrix_det {A : Matrix ι ι ℝ} (hA : A.det ≠ 0)
    (b : ι → ℝ) (c : ℝ) :
    (normalBlockMatrix A b c).det = A.det * (c - b ⬝ᵥ (A⁻¹ *ᵥ b)) := by
  letI := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA)
  rw [normalBlockMatrix, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec]
  congr 1
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The normal entry is obtained explicitly from the determinant and the
mixed quadratic form. -/
theorem normalBlockMatrix_normal_entry {A : Matrix ι ι ℝ} (hA : A.det ≠ 0)
    (b : ι → ℝ) (c : ℝ) :
    c = (normalBlockMatrix A b c).det / A.det + b ⬝ᵥ (A⁻¹ *ᵥ b) := by
  rw [normalBlockMatrix_det hA]
  field_simp
  ring

lemma quadraticForm_le_of_entry_bounds {A : Matrix ι ι ℝ} {b : ι → ℝ} {I K : ℝ}
    (hI : 0 ≤ I) (hK : 0 ≤ K) (hA : ∀ i j, |A i j| ≤ I) (hb : ∀ i, |b i| ≤ K) :
    b ⬝ᵥ (A *ᵥ b) ≤ (Fintype.card ι : ℝ) ^ 2 * I * K ^ 2 := by
  have hterm (i j : ι) : b i * (A i j * b j) ≤ K * (I * K) := by
    calc
      _ ≤ |b i * (A i j * b j)| := le_abs_self _
      _ = |b i| * (|A i j| * |b j|) := by rw [abs_mul, abs_mul]
      _ ≤ K * (I * K) := mul_le_mul (hb i)
        (mul_le_mul (hA i j) (hb j) (abs_nonneg _) hI)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hK
  calc
    _ = ∑ i, ∑ j, b i * (A i j * b j) := by simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ _i : ι, ∑ _j : ι, K * (I * K) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = _ := by simp; ring

/-- Quantitative normal Hessian control from tangential determinant and
inverse-entry bounds, mixed entries, and the actual determinant upper bound. -/
theorem normalBlockMatrix_normal_bound {A : Matrix ι ι ℝ}
    (hA : A.PosDef) {b : ι → ℝ} {c d I K F : ℝ}
    (hd : 0 < d) (hI : 0 ≤ I) (hK : 0 ≤ K) (hF : 0 ≤ F)
    (hdetA : d ≤ A.det) (hInv : ∀ i j, |A⁻¹ i j| ≤ I) (hb : ∀ i, |b i| ≤ K)
    (hdet : (normalBlockMatrix A b c).det ≤ F) :
    c ≤ F / d + (Fintype.card ι : ℝ) ^ 2 * I * K ^ 2 := by
  rw [normalBlockMatrix_normal_entry hA.det_pos.ne' b c]
  apply add_le_add
  · exact (div_le_div_of_nonneg_right hdet hA.det_pos.le).trans
      (div_le_div_of_nonneg_left hF hd hdetA)
  · exact quadraticForm_le_of_entry_bounds hI hK hInv hb

end GaussianTilt.MomentMapRegularity
