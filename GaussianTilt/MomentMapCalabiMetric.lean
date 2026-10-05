import GaussianTilt.MomentMapCalabiTensor

/-! # Genuine affine invariance of Calabi's cubic metric energy

The sixfold contraction is a quadratic form on the third tensor power.
Kronecker multiplication proves its invariance under the actual covariant
transformation of the cubic tensor and contravariant metric transformation.
-/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace GaussianTilt.MomentMapRegularity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cubicKronecker (A : Matrix ι ι ℝ) : Matrix (ι × ι × ι) (ι × ι × ι) ℝ :=
  A ⊗ₖ (A ⊗ₖ A)

def cubicFlatten (T : ι → ι → ι → ℝ) (p : ι × ι × ι) : ℝ := T p.1 p.2.1 p.2.2

def cubicTransform (R : Matrix ι ι ℝ) (T : ι → ι → ι → ℝ) (i j k : ι) : ℝ :=
  ∑ a, ∑ b, ∑ c, R a i * R b j * R c k * T a b c

def cubicMetricEnergy (A : Matrix ι ι ℝ) (T : ι → ι → ι → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ i, ∑ j, ∑ k, A a i * A b j * A c k * T a b c * T i j k

lemma cubicKronecker_mul (A B : Matrix ι ι ℝ) :
    cubicKronecker (A * B) = cubicKronecker A * cubicKronecker B := by
  unfold cubicKronecker
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]

lemma cubicKronecker_transpose (A : Matrix ι ι ℝ) :
    cubicKronecker Aᵀ = (cubicKronecker A)ᵀ := by
  ext ⟨a, b, c⟩ ⟨i, j, k⟩
  rfl

lemma cubicKronecker_one : cubicKronecker (1 : Matrix ι ι ℝ) = 1 := by
  simp [cubicKronecker, Matrix.one_kronecker_one]

lemma cubicFlatten_transform (R : Matrix ι ι ℝ) (T : ι → ι → ι → ℝ) :
    cubicFlatten (cubicTransform R T) = cubicKronecker Rᵀ *ᵥ cubicFlatten T := by
  ext ⟨i, j, k⟩
  simp only [cubicFlatten, cubicTransform, cubicKronecker, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

lemma cubicMetricEnergy_eq_quadratic (A : Matrix ι ι ℝ) (T : ι → ι → ι → ℝ) :
    cubicMetricEnergy A T = GaussianTilt.matrixQuadratic (cubicKronecker A) (cubicFlatten T) := by
  simp only [cubicMetricEnergy, GaussianTilt.matrixQuadratic, cubicKronecker, cubicFlatten,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Calabi's actual sixfold energy is affine invariant. The only metric
premise is the literal matrix conjugation identity. -/
theorem cubicMetricEnergy_affine_invariant
    (A B R : Matrix ι ι ℝ) (T : ι → ι → ι → ℝ)
    (hmetric : R * B * Rᵀ = A) :
    cubicMetricEnergy B (cubicTransform R T) = cubicMetricEnergy A T := by
  rw [cubicMetricEnergy_eq_quadratic, cubicMetricEnergy_eq_quadratic,
    cubicFlatten_transform, GaussianTilt.Whitening.matrixQuadratic_mulVec]
  rw [← cubicKronecker_transpose, Matrix.transpose_transpose,
    ← cubicKronecker_mul, ← cubicKronecker_mul, hmetric]

lemma cubicMetricEnergy_identity (T : ι → ι → ι → ℝ) :
    cubicMetricEnergy (1 : Matrix ι ι ℝ) T = calabiCubicNorm T := by
  rw [cubicMetricEnergy_eq_quadratic, cubicKronecker_one]
  simp only [GaussianTilt.matrixQuadratic, Matrix.one_mulVec, dotProduct,
    cubicFlatten, Fintype.sum_prod_type, ← pow_two, calabiCubicNorm]

end GaussianTilt.MomentMapRegularity
