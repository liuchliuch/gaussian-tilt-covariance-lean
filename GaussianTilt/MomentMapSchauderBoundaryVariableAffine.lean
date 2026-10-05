import GaussianTilt.MomentMapSchauderBoundaryVariableFreezing
import GaussianTilt.MomentMapLinearDirichletBoundaryNormalizationPDE

/-! # Exact variable-coefficient covariance under boundary normalization -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 1800000
open Matrix Set
open scoped ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

lemma matrixContraction_eq_trace_transpose (A B : Matrix (Fin n) (Fin n) ℝ) :
    matrixContraction A B=Matrix.trace (A*Bᵀ) := by
  simp only [matrixContraction,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply]

lemma bilinearEntryMatrix_comp_matrix (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) :
    bilinearEntryMatrix (B.bilinearComp (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P))=Pᵀ*bilinearEntryMatrix B*P := by
  ext i j
  change B (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P (EuclideanSpace.basisFun (Fin n) ℝ i))
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P (EuclideanSpace.basisFun (Fin n) ℝ j))=_
  rw [euclidean_bilinear_expansion]
  simp only [toEuclideanCLM_basis_apply,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  dsimp [bilinearEntryMatrix]
  ring

lemma matrixContraction_bilinearComp (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ)
    (P A : Matrix (Fin n) (Fin n) ℝ) :
    matrixContraction A (bilinearEntryMatrix (B.bilinearComp
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P) (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P)))=
      matrixContraction (P*A*Pᵀ) (bilinearEntryMatrix B) := by
  rw [bilinearEntryMatrix_comp_matrix,matrixContraction_eq_trace_transpose,matrixContraction_eq_trace_transpose]
  rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose]
  calc
    Matrix.trace (A*(Pᵀ*((bilinearEntryMatrix B)ᵀ*P))) =
        Matrix.trace ((A*Pᵀ*(bilinearEntryMatrix B)ᵀ)*P) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (P*(A*Pᵀ*(bilinearEntryMatrix B)ᵀ)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

def euclideanEquivMatrix (P : KernelSpace n ≃L[ℝ] KernelSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm P.toContinuousLinearMap

lemma euclideanEquivMatrix_mul_symm (P : KernelSpace n ≃L[ℝ] KernelSpace n) :
    euclideanEquivMatrix P*euclideanEquivMatrix P.symm=1 := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).injective
  rw [map_mul,map_one]
  change (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (euclideanEquivMatrix P))*
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (euclideanEquivMatrix P.symm))=1
  rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (euclideanEquivMatrix P)=P.toContinuousLinearMap from StarAlgEquiv.apply_symm_apply _ _,
    show Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (euclideanEquivMatrix P.symm)=P.symm.toContinuousLinearMap from StarAlgEquiv.apply_symm_apply _ _]
  apply ContinuousLinearMap.ext
  intro x
  exact P.apply_symm_apply x

lemma euclideanEquivMatrix_symm_mul (P : KernelSpace n ≃L[ℝ] KernelSpace n) :
    euclideanEquivMatrix P.symm*euclideanEquivMatrix P=1 := by
  simpa only [ContinuousLinearEquiv.symm_symm] using euclideanEquivMatrix_mul_symm P.symm

def boundaryPullbackCoefficient (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ) (x : KernelSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  euclideanEquivMatrix P.symm*A (P x)*(euclideanEquivMatrix P.symm)ᵀ

lemma boundaryPullbackCoefficient_at_zero (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hP : euclideanEquivMatrix P*(euclideanEquivMatrix P)ᵀ=A 0) :
    boundaryPullbackCoefficient P A 0=1 := by
  rw [boundaryPullbackCoefficient,map_zero,← hP]
  calc
    _ = (euclideanEquivMatrix P.symm*euclideanEquivMatrix P)*
        (euclideanEquivMatrix P.symm*euclideanEquivMatrix P)ᵀ := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [euclideanEquivMatrix_symm_mul]; simp

lemma boundaryPullbackCoefficient_isSymm (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ) {x : KernelSpace n} (hA : (A (P x)).IsSymm) :
    (boundaryPullbackCoefficient P A x).IsSymm := by
  show (boundaryPullbackCoefficient P A x)ᵀ=boundaryPullbackCoefficient P A x
  simp only [boundaryPullbackCoefficient,Matrix.transpose_mul,Matrix.transpose_transpose,hA.eq,Matrix.mul_assoc]

/-- The actual variable principal coefficient transforms contravariantly,
while the actual Hessian transforms covariantly, giving exactly the original
nondivergence contraction. -/
lemma boundary_pullback_operator_identity (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) (x : KernelSpace n) :
    matrixContraction (boundaryPullbackCoefficient P A x)
      (bilinearEntryMatrix ((B (P x)).bilinearComp P.toContinuousLinearMap P.toContinuousLinearMap))=
      matrixContraction (A (P x)) (bilinearEntryMatrix (B (P x))) := by
  have hPmap : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (euclideanEquivMatrix P)=P.toContinuousLinearMap :=
    StarAlgEquiv.apply_symm_apply _ _
  rw [← hPmap,matrixContraction_bilinearComp]
  have he : euclideanEquivMatrix P*boundaryPullbackCoefficient P A x*(euclideanEquivMatrix P)ᵀ=A (P x) := by
    change euclideanEquivMatrix P*(euclideanEquivMatrix P.symm*A (P x)*(euclideanEquivMatrix P.symm)ᵀ)*
      (euclideanEquivMatrix P)ᵀ=A (P x)
    calc
      _ = (euclideanEquivMatrix P*euclideanEquivMatrix P.symm)*A (P x)*
          (euclideanEquivMatrix P*euclideanEquivMatrix P.symm)ᵀ := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = A (P x) := by rw [euclideanEquivMatrix_mul_symm]; simp
  rw [he]

end GaussianTilt.MomentMapSchauder
