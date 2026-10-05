import GaussianTilt.WhiteningMoments

/-! # Positive covariance square roots and genuine whitening identities -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder
namespace GaussianTilt.Whitening
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The canonical positive square root of the covariance. -/
def root (C : Matrix ι ι ℝ) : Matrix ι ι ℝ := CFC.sqrt C
/-- Its genuine nonsingular matrix inverse. -/
def inverseRoot (C : Matrix ι ι ℝ) : Matrix ι ι ℝ := (root C)⁻¹

lemma root_posDef {C : Matrix ι ι ℝ} (hC : C.PosDef) : (root C).PosDef :=
  hC.posDef_sqrt

lemma root_symm (C : Matrix ι ι ℝ) : (root C).IsSymm := by
  have h := (CFC.sqrt_nonneg C).posSemidef.1
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using h

lemma inverseRoot_symm {C : Matrix ι ι ℝ} (hC : C.PosDef) : (inverseRoot C).IsSymm := by
  have h := (root_posDef hC).inv.1
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using h

lemma root_mul_root {C : Matrix ι ι ℝ} (hC : C.PosSemidef) : root C * root C = C :=
  CFC.sqrt_mul_sqrt_self C hC.nonneg

lemma inverseRoot_mul_root {C : Matrix ι ι ℝ} (hC : C.PosDef) :
    inverseRoot C * root C = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (root_posDef hC).isUnit)

lemma root_mul_inverseRoot {C : Matrix ι ι ℝ} (hC : C.PosDef) :
    root C * inverseRoot C = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (root_posDef hC).isUnit)

lemma inverseRoot_covariance {C : Matrix ι ι ℝ} (hC : C.PosDef) :
    inverseRoot C * C * (inverseRoot C).transpose = 1 := by
  rw [(inverseRoot_symm hC).eq]
  calc
    _ = inverseRoot C * (root C * root C) * inverseRoot C := by
      rw [root_mul_root hC.posSemidef]
    _ = 1 := by
      rw [← Matrix.mul_assoc, inverseRoot_mul_root hC, one_mul, root_mul_inverseRoot hC]

lemma root_norm_sq {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    ‖root C‖ ^ 2 = ‖C‖ := by
  calc
    ‖root C‖ ^ 2 = ‖star (root C) * root C‖ := by
      rw [CStarRing.norm_star_mul_self, pow_two]
    _ = ‖C‖ := by
      rw [show star (root C) = root C from (CFC.sqrt_nonneg C).posSemidef.1,
        root_mul_root hC]

lemma root_norm_le {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ‖C‖ ≤ K ^ 2) : ‖root C‖ ≤ K := by
  have hs := root_norm_sq hC
  nlinarith [norm_nonneg (root C)]

lemma sandwich_symm (B C : Matrix ι ι ℝ) (hB : B.IsSymm) :
    (root C * B * root C).IsSymm := by
  show (root C * B * root C).transpose = root C * B * root C
  rw [transpose_mul, transpose_mul, (root_symm C).eq, hB.eq, Matrix.mul_assoc]

lemma sandwich_trace_square (B : Matrix ι ι ℝ) {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) :
    Matrix.trace ((root C * B * root C) ^ 2) = Matrix.trace ((B * C) ^ 2) := by
  rw [trace_square_sandwich, root_mul_root hC]

lemma matrixQuadratic_mulVec (B A : Matrix ι ι ℝ) (x : ι → ℝ) :
    matrixQuadratic B (A *ᵥ x) = matrixQuadratic (A.transpose * B * A) x := by
  simp only [matrixQuadratic, ← Matrix.mulVec_mulVec]
  rw [dotProduct_mulVec x A.transpose, vecMul_transpose]

lemma quadratic_whitening_identity (B : Matrix ι ι ℝ) {C : Matrix ι ι ℝ}
    (hC : C.PosDef) (x : ι → ℝ) :
    matrixQuadratic (root C * B * root C) (inverseRoot C *ᵥ x) =
      matrixQuadratic B x := by
  have h := matrixQuadratic_mulVec B (root C) (inverseRoot C *ᵥ x)
  rw [(root_symm C).eq] at h
  rw [← h, Matrix.mulVec_mulVec, root_mul_inverseRoot hC, one_mulVec]

/-- The square root defines an actual continuous linear equivalence of the
Euclidean space, with the inverse-square-root map as its inverse. -/
def rootEquiv {C : Matrix ι ι ℝ} (hC : C.PosDef) :
    EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι where
  toLinearEquiv :=
    { toFun := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (root C)
      invFun := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (inverseRoot C)
      map_add' := map_add _
      map_smul' := map_smul _
      left_inv := by
        intro x
        change (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (inverseRoot C) * Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (root C)) x = x
        rw [← map_mul, inverseRoot_mul_root hC, map_one]
        rfl
      right_inv := by
        intro x
        change (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (root C) * Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (inverseRoot C)) x = x
        rw [← map_mul, root_mul_inverseRoot hC, map_one]
        rfl }
  continuous_toFun := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (root C)).continuous
  continuous_invFun := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (inverseRoot C)).continuous

@[simp] lemma rootEquiv_apply {C : Matrix ι ι ℝ} (hC : C.PosDef)
    (x : EuclideanSpace ℝ ι) :
    rootEquiv hC x = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (root C) x := rfl

@[simp] lemma rootEquiv_symm_apply {C : Matrix ι ι ℝ} (hC : C.PosDef)
    (x : EuclideanSpace ℝ ι) :
    (rootEquiv hC).symm x = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (inverseRoot C) x := rfl

end GaussianTilt.Whitening
