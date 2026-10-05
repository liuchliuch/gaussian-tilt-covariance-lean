import Mathlib
import GaussianTilt.Reference.PaperStatements

/-!
# Algebra and probability behind the non-centered quadratic estimate

These results are the algebraic part of Section 2.4 of the paper.  They do not
assert the external Letwin inequality for logconcave laws.
-/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory

namespace GaussianTilt

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic form associated with a real matrix. -/
def matrixQuadratic (B : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := x ⬝ᵥ (B *ᵥ x)

/-- Expanding the trace square after adding the barycenter's rank-one matrix.
No definiteness or invertibility assumption is necessary for this identity. -/
theorem trace_square_add_rankOne (B C : Matrix ι ι ℝ) (m : ι → ℝ) :
    Matrix.trace ((B * (C + vecMulVec m m)) ^ 2) =
      Matrix.trace ((B * C) ^ 2) +
        2 * (m ⬝ᵥ ((B * C * B) *ᵥ m)) + (m ⬝ᵥ (B *ᵥ m)) ^ 2 := by
  have hcross : Matrix.trace ((B * C) * (B * vecMulVec m m)) =
      m ⬝ᵥ ((B * C * B) *ᵥ m) := by
    rw [← Matrix.mul_assoc, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
  have hrank : Matrix.trace ((B * vecMulVec m m) * (B * vecMulVec m m)) =
      (m ⬝ᵥ (B *ᵥ m)) ^ 2 := by
    rw [mul_vecMulVec, vecMulVec_mul_vecMulVec, trace_vecMulVec,
      dotProduct_smul, dotProduct_comm]
    simp [sq]
  rw [mul_add, pow_two, add_mul, mul_add, mul_add,
    trace_add, trace_add, trace_add,
    Matrix.trace_mul_comm (B * vecMulVec m m) (B * C), hcross, hrank]
  simp only [pow_two]
  ring

/-- Dropping the nonnegative scalar-square remainder in the preceding identity. -/
theorem trace_square_centered_le (B C : Matrix ι ι ℝ) (m : ι → ℝ) :
    Matrix.trace ((B * C) ^ 2) + 2 * (m ⬝ᵥ ((B * C * B) *ᵥ m)) ≤
      Matrix.trace ((B * (C + vecMulVec m m)) ^ 2) := by
  rw [trace_square_add_rankOne]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Cyclicity removes both matrix square roots from the trace expression. -/
theorem trace_square_sandwich (B R : Matrix ι ι ℝ) :
    Matrix.trace ((R * B * R) ^ 2) = Matrix.trace ((B * (R * R)) ^ 2) := by
  simp only [pow_two]
  calc
    Matrix.trace (R * B * R * (R * B * R)) =
        Matrix.trace (R * (B * (R * R) * B * R)) := by congr 1 <;> noncomm_ring
    _ = Matrix.trace ((B * (R * R) * B * R) * R) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (B * (R * R) * (B * (R * R))) := by congr 1 <;> noncomm_ring

/-- Every real quadratic form is bounded by its genuine Euclidean operator
norm times the squared Euclidean norm of the vector. -/
theorem matrixQuadratic_le_opNorm (B : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) :
    matrixQuadratic B (WithLp.ofLp v) ≤ ‖B‖ * ‖v‖ ^ 2 := by
  have heq : matrixQuadratic B (WithLp.ofLp v) =
      inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) B v) := by
    simp [matrixQuadratic, EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.ofLp_toEuclideanCLM, star_trivial, dotProduct_comm]
  rw [heq]
  calc
    inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) B v) ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) B v‖ :=
      real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖B‖ * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) B).le_opNorm v) (norm_nonneg v)
    _ = ‖B‖ * ‖v‖ ^ 2 := by ring

/-- Expansion of a symmetric quadratic form around an arbitrary center. -/
theorem matrixQuadratic_add (B : Matrix ι ι ℝ) (hB : B.IsSymm) (m y : ι → ℝ) :
    matrixQuadratic B (m + y) = matrixQuadratic B y +
      2 * (m ⬝ᵥ (B *ᵥ y)) + matrixQuadratic B m := by
  have hsym : y ⬝ᵥ (B *ᵥ m) = m ⬝ᵥ (B *ᵥ y) := by
    rw [dotProduct_mulVec, ← hB.eq, vecMul_transpose, dotProduct_comm]
    rw [hB.eq]
  simp only [matrixQuadratic, mulVec_add, add_dotProduct, dotProduct_add]
  rw [hsym]
  ring

section Variance

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The barycenter, defined coordinatewise. -/
def meanVector (μ : Measure Ω) (X : Ω → ι → ℝ) (i : ι) : ℝ := ∫ ω, X ω i ∂μ

/-- The uncentered second-moment matrix. -/
def secondMomentMatrix (μ : Measure Ω) (X : Ω → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∫ ω, X ω i * X ω j ∂μ

/-- The covariance matrix of an actual random vector. -/
def covarianceMatrix (μ : Measure Ω) (X : Ω → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ProbabilityTheory.covariance (fun ω => X ω i) (fun ω => X ω j) μ

/-- Exact decomposition of an uncentered second moment into covariance and
barycenter outer product. -/
theorem secondMomentMatrix_eq_covariance_add_rankOne {X : Ω → ι → ℝ}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    secondMomentMatrix μ X = covarianceMatrix μ X +
      vecMulVec (meanVector μ X) (meanVector μ X) := by
  ext i j
  simp only [secondMomentMatrix, covarianceMatrix, meanVector, Matrix.add_apply,
    vecMulVec_apply, covariance_eq_sub (hX i) (hX j), Pi.mul_apply]
  ring

/-- The variance of a linear functional is its covariance quadratic form. -/
theorem variance_linear_eq_covariance {X : Ω → ι → ℝ}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) (v : ι → ℝ) :
    ProbabilityTheory.variance (fun ω => v ⬝ᵥ X ω) μ =
      matrixQuadratic (covarianceMatrix μ X) v := by
  have hlin : MemLp (fun ω => v ⬝ᵥ X ω) 2 μ := by
    exact memLp_finset_sum _ fun i _ => (hX i).const_mul (v i)
  rw [← covariance_self hlin.aemeasurable]
  simp only [dotProduct] at hlin ⊢
  rw [covariance_fun_sum_left (fun i => (hX i).const_mul (v i)) hlin]
  simp only [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [covariance_fun_sum_right (fun j => (hX j).const_mul (v j))
    ((hX i).const_mul (v i))]
  simp only [covariance_mul_left, covariance_mul_right, covarianceMatrix]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Covariance matrices are positive semidefinite. -/
theorem covarianceMatrix_posSemidef {X : Ω → ι → ℝ}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    (covarianceMatrix μ X).PosSemidef := by
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, covarianceMatrix, star_trivial]
    exact covariance_comm _ _
  · intro v
    have h := variance_nonneg (fun ω => v ⬝ᵥ X ω) μ
    rw [variance_linear_eq_covariance hX] at h
    simpa only [matrixQuadratic, star_trivial] using h

/-- Directional variance is controlled by the actual Euclidean covariance
operator norm. -/
theorem variance_direction_le_covariance_opNorm {X : Ω → ι → ℝ}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) (v : EuclideanSpace ℝ ι) :
    ProbabilityTheory.variance (fun ω => WithLp.ofLp v ⬝ᵥ X ω) μ ≤
      ‖covarianceMatrix μ X‖ * ‖v‖ ^ 2 := by
  rw [variance_linear_eq_covariance hX]
  exact matrixQuadratic_le_opNorm _ _

/-- Unit directional variance is a lower bound for the covariance norm. -/
theorem variance_unit_direction_le_covariance_opNorm {X : Ω → ι → ℝ}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (v : EuclideanSpace ℝ ι) (hv : ‖v‖ = 1) :
    ProbabilityTheory.variance (fun ω => WithLp.ofLp v ⬝ᵥ X ω) μ ≤
      ‖covarianceMatrix μ X‖ := by
  simpa only [hv, one_pow, mul_one] using variance_direction_le_covariance_opNorm hX v

/-- The variance of any coordinate is bounded by the covariance operator norm. -/
theorem variance_coordinate_le_covariance_opNorm {X : Ω → ι → ℝ}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) (i : ι) :
    ProbabilityTheory.variance (fun ω => X ω i) μ ≤ ‖covarianceMatrix μ X‖ := by
  have h := variance_unit_direction_le_covariance_opNorm hX
    (EuclideanSpace.single i 1) (by simp)
  simpa only [EuclideanSpace.ofLp_single, single_dotProduct, one_mul] using h

/-- Uncentered second moments are also positive semidefinite. -/
theorem secondMomentMatrix_posSemidef {X : Ω → ι → ℝ}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    (secondMomentMatrix μ X).PosSemidef := by
  rw [secondMomentMatrix_eq_covariance_add_rankOne hX]
  exact (covarianceMatrix_posSemidef hX).add
    (by simpa only [star_trivial] using posSemidef_vecMulVec_self_star (meanVector μ X))

/-- A weighted variance triangle inequality with the coefficients needed to
obtain the paper's constant 10. It follows just from nonnegativity of
`Var (f - 4g)`, without assuming independence. -/
theorem variance_add_le_weighted {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    variance (fun ω => f ω + g ω) μ ≤
      (5 / 4 : ℝ) * variance f μ + 5 * variance g μ := by
  have hn := variance_nonneg (fun ω => f ω - 4 * g ω) μ
  rw [variance_fun_sub hf (hg.const_mul 4), variance_mul, covariance_mul_right] at hn
  rw [variance_fun_add hf hg]
  nlinarith

/-- The numerical step in the noncentered estimate, for actual scalar random
variables. The premises are moment bounds for the two separate summands. -/
theorem variance_quadratic_plus_linear_le {f g : Ω → ℝ} {a b : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hquadratic : variance f μ ≤ 8 * a)
    (hlinear : variance g μ ≤ 4 * b) :
    variance (fun ω => f ω + g ω) μ ≤ 10 * (a + 2 * b) := by
  have h := variance_add_le_weighted hf hg
  linarith

/-- Reduction of the noncentered quadratic estimate to its centered analytic
input. All random variables, covariances, and moments in this statement are
actual integrals. This theorem does not assert the missing logconcave centered
quadratic inequality. -/
theorem noncentered_variance_of_centered_bound {X : Ω → ι → ℝ}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (B : Matrix ι ι ℝ) (hB : B.IsSymm)
    (hquad : MemLp (fun ω => matrixQuadratic B (X ω - meanVector μ X)) 2 μ)
    (hcenter : ProbabilityTheory.variance
      (fun ω => matrixQuadratic B (X ω - meanVector μ X)) μ ≤
        8 * Matrix.trace ((B * covarianceMatrix μ X) ^ 2)) :
    ProbabilityTheory.variance (fun ω => matrixQuadratic B (X ω)) μ ≤
      10 * Matrix.trace ((B * secondMomentMatrix μ X) ^ 2) := by
  let m := meanVector μ X
  let u := B *ᵥ m
  let f : Ω → ℝ := fun ω => matrixQuadratic B (X ω - m)
  let g : Ω → ℝ := fun ω => 2 * (u ⬝ᵥ (X ω - m))
  have hlin : MemLp (fun ω => u ⬝ᵥ X ω) 2 μ :=
    memLp_finset_sum _ fun i _ => (hX i).const_mul (u i)
  have hlin_center : MemLp (fun ω => u ⬝ᵥ (X ω - m)) 2 μ := by
    simpa only [dotProduct_sub] using hlin.sub (memLp_const (u ⬝ᵥ m))
  have hg : MemLp g 2 μ := hlin_center.const_mul 2
  have hbilinear (y : ι → ℝ) : m ⬝ᵥ (B *ᵥ y) = u ⬝ᵥ y := by
    dsimp [u]
    rw [dotProduct_mulVec, ← hB.eq, vecMul_transpose]
    rw [hB.eq]
  have hexpand : (fun ω => matrixQuadratic B (X ω)) =
      (fun ω => (f ω + g ω) + matrixQuadratic B m) := by
    funext ω
    have hx : X ω = m + (X ω - m) := by abel
    rw [hx, matrixQuadratic_add B hB, hbilinear]
  have hvarlin : ProbabilityTheory.variance g μ =
      4 * (m ⬝ᵥ ((B * covarianceMatrix μ X * B) *ᵥ m)) := by
    dsimp [g]
    rw [variance_mul]
    have heq : (fun ω => u ⬝ᵥ (X ω - m)) =
        (fun ω => u ⬝ᵥ X ω - u ⬝ᵥ m) := by simp only [dotProduct_sub]
    rw [heq, variance_sub_const hlin.aestronglyMeasurable,
      variance_linear_eq_covariance hX]
    simp only [matrixQuadratic]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hbilinear]
    norm_num
    dsimp [u]
    rw [Matrix.mulVec_mulVec]
  have hfg : AEStronglyMeasurable (fun ω => f ω + g ω) μ :=
    (hquad.add hg).aestronglyMeasurable
  rw [hexpand, variance_add_const hfg]
  have hb := variance_quadratic_plus_linear_le hquad hg hcenter hvarlin.le
  have ht := trace_square_centered_le B (covarianceMatrix μ X) m
  rw [secondMomentMatrix_eq_covariance_add_rankOne hX]
  exact hb.trans (mul_le_mul_of_nonneg_left ht (by norm_num))

end Variance
end GaussianTilt

namespace GaussianTilt.Reference

variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

/-- Agreement of the independent paper specification with the standard
probability-theory covariance matrix. -/
theorem covariance_eq_covarianceMatrix
    (hX : ∀ i : Fin n, MemLp (fun x : Space n => x i) 2 μ) :
    covariance μ = GaussianTilt.covarianceMatrix μ (fun x => WithLp.ofLp x) := by
  ext i j
  change (∫ x : Space n, x i * x j ∂μ) -
    (∫ x : Space n, x i ∂μ) * (∫ x : Space n, x j ∂μ) =
      ProbabilityTheory.covariance (fun x : Space n => x i) (fun x : Space n => x j) μ
  exact (covariance_eq_sub (hX i) (hX j)).symm

/-- Positivity for the covariance appearing in the paper's main statement. -/
theorem covariance_posSemidef
    (hX : ∀ i : Fin n, MemLp (fun x : Space n => x i) 2 μ) :
    (covariance μ).PosSemidef := by
  rw [covariance_eq_covarianceMatrix hX]
  exact GaussianTilt.covarianceMatrix_posSemidef hX

/-- The axial variance lower bound passes to the exact operator norm used
in the independent lower-bound specification. -/
theorem coordinate_variance_le_covariance_norm
    (hX : ∀ i : Fin n, MemLp (fun x : Space n => x i) 2 μ) (i : Fin n) :
    ProbabilityTheory.variance (fun x : Space n => x i) μ ≤ ‖covariance μ‖ := by
  rw [covariance_eq_covarianceMatrix hX]
  exact GaussianTilt.variance_coordinate_le_covariance_opNorm hX i

end GaussianTilt.Reference
