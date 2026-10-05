import GaussianTilt.MomentMapLinearDirichletFlatteningChainRule
import GaussianTilt.MomentMapSchauderHessianNorms

/-! # Exact transformed elliptic operator, including curvature drift -/
noncomputable section
set_option maxHeartbeats 2000000
open Matrix Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

def euclideanCLMMatrix (T : KernelSpace n →L[ℝ] KernelSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm T

lemma euclideanCLMMatrix_entry (T : KernelSpace n →L[ℝ] KernelSpace n) (i j : Fin n) :
    euclideanCLMMatrix T i j = (T (EuclideanSpace.basisFun (Fin n) ℝ j)) i := by
  have hh := toEuclideanCLM_basis_apply (euclideanCLMMatrix T) j i
  rw [show Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (euclideanCLMMatrix T) = T from
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply T] at hh
  exact hh.symm

lemma four_sum_matrix_contraction (A J B : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, A i j * (∑ p, ∑ q, J p i * J q j * B p q)) =
      ∑ p, ∑ q, (J * A * Jᵀ) p q * B p q := by
  have he := Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun i : Fin n × Fin n => fun p : Fin n × Fin n => A i.1 i.2 * (J p.1 i.1 * J p.2 i.2 * B p.1 p.2))
  simp only [Fintype.sum_prod_type] at he
  simp only [Finset.mul_sum]
  rw [he, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma elliptic_bilinear_change (A : Matrix (Fin n) (Fin n) ℝ)
    (T : KernelSpace n →L[ℝ] KernelSpace n)
    (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) :
    (∑ i, ∑ j, A i j * B (T (EuclideanSpace.basisFun (Fin n) ℝ i)) (T (EuclideanSpace.basisFun (Fin n) ℝ j))) =
      ∑ p, ∑ q, (euclideanCLMMatrix T * A * (euclideanCLMMatrix T)ᵀ) p q *
        B (EuclideanSpace.basisFun (Fin n) ℝ p) (EuclideanSpace.basisFun (Fin n) ℝ q) := by
  have hb (i j : Fin n) :
      B (T (EuclideanSpace.basisFun (Fin n) ℝ i)) (T (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      ∑ p, ∑ q, euclideanCLMMatrix T p i * euclideanCLMMatrix T q j *
        B (EuclideanSpace.basisFun (Fin n) ℝ p) (EuclideanSpace.basisFun (Fin n) ℝ q) := by
    simpa only [euclideanCLMMatrix_entry] using euclidean_bilinear_expansion B
      (T (EuclideanSpace.basisFun (Fin n) ℝ i)) (T (EuclideanSpace.basisFun (Fin n) ℝ j))
  simp_rw [hb]
  exact four_sum_matrix_contraction A (euclideanCLMMatrix T) (fun p q =>
    B (EuclideanSpace.basisFun (Fin n) ℝ p) (EuclideanSpace.basisFun (Fin n) ℝ q))

def flatteningJacobian (w : KernelSpace n → ℝ) (j : Fin n) (x : KernelSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  euclideanCLMMatrix (boundaryRowLinear (-fderiv ℝ w x) j)

def flatteningCoefficient (A : Matrix (Fin n) (Fin n) ℝ)
    (w : KernelSpace n → ℝ) (j : Fin n) (x : KernelSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  flatteningJacobian w j x * A * (flatteningJacobian w j x)ᵀ

/-- The actual nondivergence operator under the nonlinear regular-level
chart. The curvature term is a genuine first-order drift, displayed explicitly. -/
theorem ellipticOperator_comp_flattening_at (A : Matrix (Fin n) (Fin n) ℝ)
    {u w : KernelSpace n → ℝ} {x : KernelSpace n} (a : KernelSpace n) (j : Fin n)
    (hw : ContDiffAt ℝ 2 w x) (hu : ContDiffAt ℝ 2 u (flatteningMap w a j x)) :
    euclideanEllipticOperator A (u ∘ flatteningMap w a j) x =
      euclideanEllipticOperator (flatteningCoefficient A w j x) u (flatteningMap w a j x) -
        euclideanEllipticOperator A w x *
          fderiv ℝ u (flatteningMap w a j x) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  simp only [euclideanEllipticOperator, secondFrechet_comp_flattening_at a j hw hu,
    mul_sub, Finset.sum_sub_distrib]
  rw [elliptic_bilinear_change]
  congr 1
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma boundaryRow_matrix_right_inverse (L : KernelSpace n →L[ℝ] ℝ) (j : Fin n)
    (hL : L (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) :
    euclideanCLMMatrix (boundaryRowLinear L j) * euclideanCLMMatrix (boundaryRowInverseLinear L j) = 1 := by
  apply (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).injective
  rw [map_mul, map_one]
  change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (euclideanCLMMatrix (boundaryRowLinear L j)) *
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (euclideanCLMMatrix (boundaryRowInverseLinear L j)) = 1
  dsimp only [euclideanCLMMatrix]
  rw [(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply,
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply]
  apply ContinuousLinearMap.ext
  intro v
  exact boundaryRow_right_inverse L j hL v

/-- Ellipticity survives the actual flattening map; the needed inverse
matrix is constructed from the explicit inverse row replacement. -/
theorem flatteningCoefficient_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (w : KernelSpace n → ℝ) (j : Fin n) (x : KernelSpace n)
    (hj : fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) :
    (flatteningCoefficient A w j x).PosDef := by
  have hL : (-fderiv ℝ w x) (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0 := by
    simpa only [ContinuousLinearMap.neg_apply] using neg_ne_zero.mpr hj
  have hi := boundaryRow_matrix_right_inverse (-fderiv ℝ w x) j hL
  have hinj : Function.Injective (flatteningJacobian w j x).vecMul := by
    intro v z hvz
    have hh := congrArg (fun y => y ᵥ* euclideanCLMMatrix (boundaryRowInverseLinear (-fderiv ℝ w x) j)) hvz
    simp only [Matrix.vecMul_vecMul, flatteningJacobian, hi, Matrix.vecMul_one] at hh
    exact hh
  simpa only [flatteningCoefficient, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hA.mul_mul_conjTranspose_same hinj

end GaussianTilt.MomentMapLinearDirichlet
