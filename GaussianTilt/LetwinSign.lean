import GaussianTilt.LetwinAbsolute

/-! # Spectral sign and square-root coordinates for the quadratic argument -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GaussianTilt.Letwin
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sign is chosen to be +1 at a zero eigenvalue. Thus the sign matrix
remains orthogonal even before the invertible-matrix approximation. -/
def realPolarSign (a : ℝ) : ℝ := if 0 ≤ a then 1 else -1

lemma realPolarSign_sq (a : ℝ) : realPolarSign a ^ 2 = 1 := by
  unfold realPolarSign
  split_ifs <;> norm_num

lemma abs_mul_realPolarSign (a : ℝ) : |a| * realPolarSign a = a := by
  unfold realPolarSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

/-- An orthogonal symmetric matrix carrying the spectral signs. -/
def spectralSign {B : Matrix ι ι ℝ} (hB : B.IsHermitian) : Matrix ι ι ℝ :=
  (hB.eigenvectorUnitary : Matrix ι ι ℝ) * Matrix.diagonal (fun i => realPolarSign (hB.eigenvalues i)) *
    star (hB.eigenvectorUnitary : Matrix ι ι ℝ)

/-- The positive square root of the spectral absolute value, explicitly in
the same eigenbasis as the original matrix. -/
def spectralMagnitudeRoot {B : Matrix ι ι ℝ} (hB : B.IsHermitian) : Matrix ι ι ℝ :=
  (hB.eigenvectorUnitary : Matrix ι ι ℝ) * Matrix.diagonal (fun i => Real.sqrt |hB.eigenvalues i|) *
    star (hB.eigenvectorUnitary : Matrix ι ι ℝ)

lemma unitary_conjugate_mul (U D E : Matrix ι ι ℝ) (hU : star U * U = 1) :
    (U * D * star U) * (U * E * star U) = U * (D * E) * star U := by
  calc
    _ = U * D * (star U * U) * E * star U := by noncomm_ring
    _ = _ := by rw [hU]; simp only [Matrix.mul_one]; noncomm_ring

lemma real_unitary_conjugate_isSymm (U D : Matrix ι ι ℝ) (hD : D.IsSymm) :
    (U * D * star U).IsSymm := by
  change (U * D * Uᵀ)ᵀ = U * D * Uᵀ
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hD.eq,
    Matrix.mul_assoc]

lemma spectralSign_isSymm {B : Matrix ι ι ℝ} (hB : B.IsHermitian) :
    (spectralSign hB).IsSymm :=
  real_unitary_conjugate_isSymm _ _ (Matrix.isSymm_diagonal _)

lemma spectralMagnitudeRoot_isSymm {B : Matrix ι ι ℝ} (hB : B.IsHermitian) :
    (spectralMagnitudeRoot hB).IsSymm :=
  real_unitary_conjugate_isSymm _ _ (Matrix.isSymm_diagonal _)

lemma spectralMagnitudeRoot_posSemidef {B : Matrix ι ι ℝ} (hB : B.IsHermitian) :
    (spectralMagnitudeRoot hB).PosSemidef :=
  (Matrix.PosSemidef.diagonal (fun i => Real.sqrt_nonneg _)).mul_mul_conjTranspose_same _

lemma spectralSign_mul_self {B : Matrix ι ι ℝ} (hB : B.IsHermitian) :
    spectralSign hB * spectralSign hB = 1 := by
  rw [spectralSign, unitary_conjugate_mul _ _ _ (unitary.coe_star_mul_self _)]
  have hD : Matrix.diagonal (fun i => realPolarSign (hB.eigenvalues i)) *
      Matrix.diagonal (fun i => realPolarSign (hB.eigenvalues i)) = (1 : Matrix ι ι ℝ) := by
    rw [Matrix.diagonal_mul_diagonal]
    simpa only [← pow_two, realPolarSign_sq] using (Matrix.diagonal_one : Matrix.diagonal (fun _ : ι => (1 : ℝ)) = 1)
  rw [hD, Matrix.mul_one]
  exact unitary.coe_mul_star_self _

lemma spectralMagnitudeRoot_mul_self {B : Matrix ι ι ℝ} (hB : B.IsHermitian) :
    spectralMagnitudeRoot hB * spectralMagnitudeRoot hB = spectralAbsolute hB := by
  rw [spectralMagnitudeRoot, unitary_conjugate_mul _ _ _ (unitary.coe_star_mul_self _)]
  unfold spectralAbsolute
  congr 2
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact Real.mul_self_sqrt (abs_nonneg _)

lemma spectralMagnitudeRoot_sign_sandwich {B : Matrix ι ι ℝ} (hB : B.IsHermitian) :
    spectralMagnitudeRoot hB * spectralSign hB * spectralMagnitudeRoot hB = B := by
  rw [spectralMagnitudeRoot, spectralSign,
    unitary_conjugate_mul _ _ _ (unitary.coe_star_mul_self _),
    unitary_conjugate_mul _ _ _ (unitary.coe_star_mul_self _)]
  conv_rhs => rw [hB.spectral_theorem]
  congr 2
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  change Real.sqrt |hB.eigenvalues i| * realPolarSign (hB.eigenvalues i) *
    Real.sqrt |hB.eigenvalues i| = hB.eigenvalues i
  calc
    _ = (Real.sqrt |hB.eigenvalues i| * Real.sqrt |hB.eigenvalues i|) *
        realPolarSign (hB.eigenvalues i) := by ring
    _ = _ := by rw [Real.mul_self_sqrt (abs_nonneg _), abs_mul_realPolarSign]

lemma hsSquare_mul_orthogonal (U A : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) :
    hsSquare (U * A) = hsSquare A := by
  rw [hsSquare_eq_trace, Matrix.transpose_mul]
  calc
    _ = Matrix.trace (U * (A * Aᵀ) * Uᵀ) := by congr 1; noncomm_ring
    _ = Matrix.trace (Uᵀ * U * (A * Aᵀ)) := Matrix.trace_mul_cycle _ _ _
    _ = _ := by rw [hU, Matrix.one_mul, hsSquare_eq_trace]

lemma eigenvalues_ne_zero_of_det_ne {B : Matrix ι ι ℝ} (hB : B.IsHermitian)
    (hdet : B.det ≠ 0) (i : ι) : hB.eigenvalues i ≠ 0 := by
  rw [hB.det_eq_prod_eigenvalues] at hdet
  exact (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)

lemma spectralMagnitudeRoot_posDef {B : Matrix ι ι ℝ} (hB : B.IsHermitian)
    (hdet : B.det ≠ 0) : (spectralMagnitudeRoot hB).PosDef := by
  apply (Matrix.posDef_diagonal_iff.mpr (fun i =>
    Real.sqrt_pos.mpr (abs_pos.mpr (eigenvalues_ne_zero_of_det_ne hB hdet i)))).mul_mul_conjTranspose_same
  rw [Matrix.vecMul_injective_iff_isUnit, ← unitary.val_toUnits_apply]
  exact Units.isUnit _

/-- The original quadratic is the sign quadratic in square-root-absolute
coordinates, with no centering term needed for variance transport. -/
lemma matrixQuadratic_spectralCoordinates {B : Matrix ι ι ℝ} (hB : B.IsHermitian)
    (x : ι → ℝ) :
    matrixQuadratic (spectralSign hB) (spectralMagnitudeRoot hB *ᵥ x) = matrixQuadratic B x := by
  have heq : matrixQuadratic (spectralSign hB) (spectralMagnitudeRoot hB *ᵥ x) =
      matrixQuadratic ((spectralMagnitudeRoot hB)ᵀ * spectralSign hB * spectralMagnitudeRoot hB) x := by
    simp only [matrixQuadratic, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec x (spectralMagnitudeRoot hB)ᵀ, Matrix.vecMul_transpose]
  rw [heq, (spectralMagnitudeRoot_isSymm hB).eq, spectralMagnitudeRoot_sign_sandwich]

end GaussianTilt.Letwin
