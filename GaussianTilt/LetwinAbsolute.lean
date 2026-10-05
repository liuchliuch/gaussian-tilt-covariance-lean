import GaussianTilt.LetwinHessianVariance

/-! # Removing positive semidefiniteness of the test matrix in Letwin 2.5 -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GaussianTilt.Letwin
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def spectralAbsolute {B : Matrix ι ι ℝ} (hB : B.IsHermitian) : Matrix ι ι ℝ :=
  (hB.eigenvectorUnitary : Matrix ι ι ℝ) * Matrix.diagonal (fun i => |hB.eigenvalues i|) *
    star (hB.eigenvectorUnitary : Matrix ι ι ℝ)

lemma spectralAbsolute_posSemidef {B : Matrix ι ι ℝ} (hB : B.IsHermitian) :
    (spectralAbsolute hB).PosSemidef :=
  (Matrix.PosSemidef.diagonal (fun i => abs_nonneg (hB.eigenvalues i))).mul_mul_conjTranspose_same _

lemma trace_square_unitary_conjugate (U D : Matrix ι ι ℝ) (hU : star U * U = 1) :
    Matrix.trace ((U * D * star U)^2) = Matrix.trace (D^2) := by
  have hs : (U * D * star U)^2 = U * D^2 * star U := by
    calc
      _ = U * D * (star U * U) * D * star U := by noncomm_ring
      _ = _ := by rw [hU]; simp only [Matrix.mul_one]; noncomm_ring
  rw [hs, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

lemma spectralAbsolute_trace_square {B : Matrix ι ι ℝ} (hB : B.IsHermitian) :
    Matrix.trace ((spectralAbsolute hB)^2) = Matrix.trace (B^2) := by
  let U : Matrix ι ι ℝ := hB.eigenvectorUnitary
  have hU : star U * U = 1 := unitary.coe_star_mul_self _
  have hspec : B = U * Matrix.diagonal hB.eigenvalues * star U := hB.spectral_theorem
  rw [spectralAbsolute, trace_square_unitary_conjugate _ _ hU]
  conv_rhs => rw [hspec, trace_square_unitary_conjugate _ _ hU]
  congr 1
  simp only [Matrix.diagonal_pow]
  congr 1
  funext i
  exact sq_abs (hB.eigenvalues i)

lemma trace_quadratic_conjugate (U D H : Matrix ι ι ℝ) :
    Matrix.trace ((U * D * star U) * H * (U * D * star U) * H) =
      Matrix.trace (D * (star U * H * U) * D * (star U * H * U)) := by
  calc
    _ = Matrix.trace (U * (D * (star U * H * U) * D * star U * H)) := by congr 1; noncomm_ring
    _ = Matrix.trace ((D * (star U * H * U) * D * star U * H) * U) := Matrix.trace_mul_comm _ _
    _ = _ := by congr 1; noncomm_ring

lemma trace_diagonal_quadratic (b : ι → ℝ) (H : Matrix ι ι ℝ) (hH : H.IsSymm) :
    Matrix.trace (Matrix.diagonal b * H * Matrix.diagonal b * H) =
      ∑ i, ∑ j, b i * b j * H i j ^ 2 := by
  change (∑ i, ∑ j, (Matrix.diagonal b * H * Matrix.diagonal b) i j * H j i) = _
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hH.apply i j]
  ring

/-- The pointwise comparison with the genuine spectral absolute value of a
symmetric matrix. This is the indefinite-matrix reduction in theorem 2.5. -/
theorem trace_quadratic_le_spectralAbsolute {B : Matrix ι ι ℝ} (hB : B.IsHermitian)
    (H : Matrix ι ι ℝ) (hH : H.PosSemidef) :
    Matrix.trace (B * H * B * H) ≤
      Matrix.trace (spectralAbsolute hB * H * spectralAbsolute hB * H) := by
  let U : Matrix ι ι ℝ := hB.eigenvectorUnitary
  have hspec : B = U * Matrix.diagonal hB.eigenvalues * star U := hB.spectral_theorem
  have hKp := hH.conjTranspose_mul_mul_same U
  have hKs : (star U * H * U).IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hKp.isHermitian
  conv_lhs => rw [hspec]
  rw [spectralAbsolute, trace_quadratic_conjugate, trace_quadratic_conjugate,
    trace_diagonal_quadratic _ _ hKs, trace_diagonal_quadratic _ _ hKs]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [abs_mul] using le_abs_self (hB.eigenvalues i * hB.eigenvalues j)

end GaussianTilt.Letwin
