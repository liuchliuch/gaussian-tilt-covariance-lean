import GaussianTilt.MomentMapLinearDirichletBoundaryNormalizationPDE
import GaussianTilt.MomentMapLinearDirichletH1GradientDecay

/-! # Actual dual-map and energy geometry for frozen-SPD excess transfer -/
noncomputable section
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def boundaryDualMap (P : KernelSpace n ≃L[ℝ] KernelSpace n) : KernelSpace n →L[ℝ] KernelSpace n :=
  ContinuousLinearMap.adjoint P.toContinuousLinearMap

lemma boundaryDualMap_norm (P : KernelSpace n ≃L[ℝ] KernelSpace n) :
    ‖boundaryDualMap P‖=‖P.toContinuousLinearMap‖ := ContinuousLinearMap.adjoint.norm_map _

lemma boundaryDualMap_inverse (P : KernelSpace n ≃L[ℝ] KernelSpace n) :
    (boundaryDualMap P.symm).comp (boundaryDualMap P)=ContinuousLinearMap.id ℝ (KernelSpace n) := by
  unfold boundaryDualMap
  rw [← ContinuousLinearMap.adjoint_comp]
  have he : P.toContinuousLinearMap.comp P.symm.toContinuousLinearMap=ContinuousLinearMap.id ℝ (KernelSpace n) := by
    apply ContinuousLinearMap.ext
    intro x
    exact P.apply_symm_apply x
  rw [he,ContinuousLinearMap.adjoint_id]

lemma boundaryDualMap_norm_bounds (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    {M N : ℝ} (hP : ‖P.toContinuousLinearMap‖ ≤ M) (hI : ‖P.symm.toContinuousLinearMap‖ ≤ N)
    (v : KernelSpace n) : ‖boundaryDualMap P v‖ ≤ M*‖v‖ ∧ ‖v‖ ≤ N*‖boundaryDualMap P v‖ := by
  constructor
  · exact ((boundaryDualMap P).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (by rwa [boundaryDualMap_norm]) (norm_nonneg _))
  · have he := congrArg (fun T : KernelSpace n →L[ℝ] KernelSpace n => T v) (boundaryDualMap_inverse P)
    change boundaryDualMap P.symm (boundaryDualMap P v)=v at he
    calc
      _ = ‖boundaryDualMap P.symm (boundaryDualMap P v)‖ := congrArg norm he.symm
      _ ≤ ‖boundaryDualMap P.symm‖*‖boundaryDualMap P v‖ := (boundaryDualMap P.symm).le_opNorm _
      _ ≤ N*‖boundaryDualMap P v‖ := mul_le_mul_of_nonneg_right (by rwa [boundaryDualMap_norm]) (norm_nonneg _)

lemma normal_vector_eq_coordinate_smul (j : Fin n) {q : KernelSpace n}
    (hq : ∀ i, i ≠ j → q i=0) : q=q j • EuclideanSpace.basisFun (Fin n) ℝ j := by
  ext i
  by_cases hi : i=j
  · subst i
    simp
  · simp [EuclideanSpace.basisFun_apply,EuclideanSpace.single_apply,hi,hq i hi]

lemma boundaryDualMap_normal (P : KernelSpace n ≃L[ℝ] KernelSpace n) (j : Fin n) {c : ℝ}
    (hplane : ∀ x, (P x) j=c*x j) {q : KernelSpace n} (hq : ∀ i, i ≠ j → q i=0) :
    boundaryDualMap P q=c • q := by
  have he : boundaryDualMap P (EuclideanSpace.basisFun (Fin n) ℝ j)=c • EuclideanSpace.basisFun (Fin n) ℝ j := by
    apply ext_inner_left ℝ
    intro x
    rw [boundaryDualMap,ContinuousLinearMap.adjoint_inner_right]
    have hbi (v : KernelSpace n) : inner ℝ v (EuclideanSpace.basisFun (Fin n) ℝ j)=v j := by
      rw [real_inner_comm,EuclideanSpace.basisFun_inner]
    simp only [hbi,inner_smul_right]
    exact hplane x
  rw [normal_vector_eq_coordinate_smul j hq,map_smul,he]
  module

lemma boundaryDualMap_matrix (P : KernelSpace n ≃L[ℝ] KernelSpace n) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((euclideanCLMMatrix P.toContinuousLinearMap)ᵀ)=boundaryDualMap P := by
  have hh := map_star (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (euclideanCLMMatrix P.toContinuousLinearMap)
  simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,euclideanCLMMatrix,
    StarAlgEquiv.apply_symm_apply,ContinuousLinearMap.star_eq_adjoint,boundaryDualMap] using hh

lemma physical_affine_integral_preimage (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    {S : Set (KernelSpace n)} (hS : MeasurableSet S) (f : KernelSpace n → ℝ) :
    |P.toContinuousLinearMap.det| *(∫ z in P ⁻¹' S, f (P z))=∫ x in S, f x := by
  have hi : P '' (P ⁻¹' S)=S := image_preimage_eq _ P.surjective
  have hh := integral_image_eq_integral_abs_det_fderiv_smul volume (hS.preimage P.continuous.measurable)
    (fun x (_:x∈P ⁻¹' S) => P.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt) P.injective.injOn f
  simp only [ContinuousLinearEquiv.coe_coe] at hh
  rw [hi] at hh
  rw [← integral_const_mul]
  exact hh.symm

lemma physical_affine_det_pos (P : KernelSpace n ≃L[ℝ] KernelSpace n) : 0 < |P.toContinuousLinearMap.det| := by
  apply abs_pos.mpr
  exact P.toLinearEquiv.isUnit_det'.ne_zero

end GaussianTilt.MomentMapLinearDirichlet
