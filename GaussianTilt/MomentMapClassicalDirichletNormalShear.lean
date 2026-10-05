import GaussianTilt.MomentMapClassicalDirichletNormalAlgebra
import GaussianTilt.MomentMapClassicalDirichletMixedHessian

/-! # The actual determinant-preserving tangent-coordinate shear -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Change from coordinate directions to the genuine tangent directions
`e_a - β_a e_normal`, keeping the normal coordinate unchanged. -/
def boundaryNormalShear (β : ι → ℝ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  Matrix.fromBlocks 1 0 (fun _ a => -β a) 1

lemma boundaryNormalShear_det (β : ι → ℝ) : (boundaryNormalShear β).det = 1 := by
  simp [boundaryNormalShear, Matrix.det_fromBlocks_zero₁₂]

lemma boundaryNormalShear_injective (β : ι → ℝ) :
    Function.Injective (boundaryNormalShear β).mulVec := by
  apply Matrix.mulVec_injective_of_isUnit
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [boundaryNormalShear_det]; exact isUnit_one)

lemma boundaryNormalShear_posDef {H : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ}
    (hH : H.PosDef) (β : ι → ℝ) :
    ((boundaryNormalShear β)ᵀ * H * boundaryNormalShear β).PosDef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hH.conjTranspose_mul_mul_same (boundaryNormalShear_injective β)

lemma boundaryNormalShear_preserves_det (H : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)
    (β : ι → ℝ) :
    ((boundaryNormalShear β)ᵀ * H * boundaryNormalShear β).det = H.det := by
  simp [Matrix.det_mul, Matrix.det_transpose, boundaryNormalShear_det]

/-- The transformed entries are the true tangential block, adapted mixed
entries, and unchanged pure normal entry. -/
lemma boundaryNormalShear_transform (A : Matrix ι ι ℝ) (b β : ι → ℝ) (c : ℝ) :
    (boundaryNormalShear β)ᵀ * normalBlockMatrix A b c * boundaryNormalShear β =
      normalBlockMatrix
        (A - vecMulVec b β - vecMulVec β b + c • vecMulVec β β)
        (b - c • β) c := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [boundaryNormalShear, normalBlockMatrix, Matrix.mul_apply,
    Matrix.transpose_apply, Fintype.sum_sum_type, Matrix.vecMulVec_apply, Matrix.one_apply, Finset.sum_sub_distrib]
  all_goals ring

/-- Actual determinant identity in tangent-normal coordinates. -/
lemma normalBlockMatrix_tangential_det (A : Matrix ι ι ℝ) (b β : ι → ℝ) (c : ℝ) :
    (normalBlockMatrix
      (A - vecMulVec b β - vecMulVec β b + c • vecMulVec β β) (b - c • β) c).det =
      (normalBlockMatrix A b c).det := by
  rw [← boundaryNormalShear_transform, boundaryNormalShear_preserves_det]

/-- Normal completion now applies directly to the actual tangent and mixed
entries produced by the boundary geometry and patch estimate. -/
theorem normalBlockMatrix_bound_of_tangential_data
    {A : Matrix ι ι ℝ} {b β : ι → ℝ} {c d I K F : ℝ}
    (hA : (A - vecMulVec b β - vecMulVec β b + c • vecMulVec β β).PosDef)
    (hd : 0 < d) (hI : 0 ≤ I) (hK : 0 ≤ K) (hF : 0 ≤ F)
    (hdetA : d ≤ (A - vecMulVec b β - vecMulVec β b + c • vecMulVec β β).det)
    (hInv : ∀ i j, |(A - vecMulVec b β - vecMulVec β b + c • vecMulVec β β)⁻¹ i j| ≤ I)
    (hb : ∀ i, |b i - c * β i| ≤ K)
    (hdet : (normalBlockMatrix A b c).det ≤ F) :
    c ≤ F / d + (Fintype.card ι : ℝ)^2 * I * K^2 := by
  apply normalBlockMatrix_normal_bound (b := b - c • β) hA hd hI hK hF hdetA hInv
  · simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hb
  · rwa [normalBlockMatrix_tangential_det]

end GaussianTilt.MomentMapRegularity
