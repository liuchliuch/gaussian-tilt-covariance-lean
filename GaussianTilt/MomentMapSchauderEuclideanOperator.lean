import GaussianTilt.MomentMapSchauderHessianNorms
import GaussianTilt.MomentMapSchauderAffineBounds

/-!
# Actual Euclidean affine reduction of a frozen elliptic operator

The chain rule for the true second Fréchet derivative proves the operator
transfer. The square root of the actual coefficient reduces the equation
to the ordinary Euclidean Laplacian.
-/
noncomputable section
open Matrix Set
open scoped BigOperators ContDiff MatrixOrder
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic

section Bilinear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_bilinearComp_same_le (B : E →L[ℝ] E →L[ℝ] ℝ) (P : E →L[ℝ] E) :
    ‖B.bilinearComp P P‖ ≤ ‖B‖ * ‖P‖ ^ 2 := by
  apply (B.bilinearComp P P).opNorm_le_bound (by positivity)
  intro v
  apply ((B.bilinearComp P P) v).opNorm_le_bound (by positivity)
  intro w
  rw [ContinuousLinearMap.bilinearComp_apply]
  calc
    _ ≤ ‖B (P v)‖ * ‖P w‖ := (B (P v)).le_opNorm _
    _ ≤ (‖B‖ * ‖P v‖) * ‖P w‖ := mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
    _ ≤ (‖B‖ * (‖P‖ * ‖v‖)) * (‖P‖ * ‖w‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (P.le_opNorm v) (norm_nonneg B))
        (P.le_opNorm w) (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma bilinearComp_sub (B C : E →L[ℝ] E →L[ℝ] ℝ) (P : E →L[ℝ] E) :
    (B - C).bilinearComp P P = B.bilinearComp P P - C.bilinearComp P P := by
  ext v w
  simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.sub_apply]

/-- The literal second Fréchet chain rule for a continuous linear map. -/
theorem secondFrechet_comp_linear {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (P : E →L[ℝ] E) (x : E) :
    fderiv ℝ (fderiv ℝ (u ∘ P)) x =
      (fderiv ℝ (fderiv ℝ u) (P x)).bilinearComp P P := by
  have hud := hu.differentiable (by norm_num)
  have hDu : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl
  have he : fderiv ℝ (u ∘ P) = (fun y => (fderiv ℝ u (P y)).comp P) := by
    funext y
    rw [fderiv_comp y (hud _) P.differentiableAt, P.fderiv]
  rw [he, fderiv_clm_comp (c := fun y => fderiv ℝ u (P y)) (d := fun _ => P)
    ((hDu _).comp x P.differentiableAt) (differentiableAt_const P)]
  have hdc : fderiv ℝ (fun y => fderiv ℝ u (P y)) x =
      (fderiv ℝ (fderiv ℝ u) (P x)).comp P :=
    ((hDu (P x)).hasFDerivAt.comp x P.hasFDerivAt).fderiv
  rw [hdc]
  ext v w
  simp [ContinuousLinearMap.bilinearComp_apply]

end Bilinear

variable {n : ℕ}

/-- Literal nondivergence operator in the canonical Euclidean basis. -/
def euclideanEllipticOperator (A : Matrix (Fin n) (Fin n) ℝ)
    (u : KernelSpace n → ℝ) (x : KernelSpace n) : ℝ :=
  ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ u) x
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)

lemma toEuclideanCLM_basis_apply (P : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P (EuclideanSpace.basisFun (Fin n) ℝ i)) j = P j i := by
  change (P *ᵥ (EuclideanSpace.basisFun (Fin n) ℝ i).ofLp) j = _
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.ofLp_single, Matrix.mulVec_single_one]
  rfl

set_option maxHeartbeats 500000 in
/-- Actual constant-coefficient reduction under an arbitrary matrix linear
map: the transformed Laplacian contracts with `P Pᵀ`. -/
theorem kernelLaplacian_comp_matrix {u : KernelSpace n → ℝ} (hu : ContDiff ℝ 2 u)
    (P : Matrix (Fin n) (Fin n) ℝ) (x : KernelSpace n) :
    kernelLaplacian (u ∘ Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P) x =
      euclideanEllipticOperator (P * Pᵀ) u (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P x) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let B := fderiv ℝ (fderiv ℝ u) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P x)
  have huc : ContDiff ℝ 2 (u ∘ Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P) :=
    hu.comp (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P).contDiff
  simp only [kernelLaplacian, directionalHessian_eq_secondFrechet huc,
    secondFrechet_comp_linear hu, ContinuousLinearMap.bilinearComp_apply]
  change (∑ i, B (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P (e i))
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P (e i))) = _
  have hE (i : Fin n) : B (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P (e i))
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P (e i)) =
      ∑ a, ∑ b, P a i * P b i * B (e a) (e b) := by
    have hh := euclidean_bilinear_expansion B
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P (e i))
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P (e i))
    simpa only [e, toEuclideanCLM_basis_apply] using hh
  simp_rw [hE]
  rw [Finset.sum_comm]
  calc
    _ = ∑ a, ∑ b, ∑ i, P a i * P b i * B (e a) (e b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [euclideanEllipticOperator, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, B, e]

/-- The actual positive square root changes a frozen elliptic equation into
a Poisson equation. The quantitative norm bounds are in AffineBounds. -/
theorem kernelLaplacian_comp_coefficient_sqrt {u : KernelSpace n → ℝ} (hu : ContDiff ℝ 2 u)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (x : KernelSpace n) :
    kernelLaplacian (u ∘ Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (CFC.sqrt A)) x =
      euclideanEllipticOperator A u (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (CFC.sqrt A) x) := by
  rw [kernelLaplacian_comp_matrix hu]
  have hs : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.posDef_sqrt.isHermitian.eq
  rw [hs, CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]

end GaussianTilt.MomentMapSchauder
