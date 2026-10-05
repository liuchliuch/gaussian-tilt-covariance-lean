import GaussianTilt.MomentMapRegularityImprovementNormalization
import GaussianTilt.MomentMapRegularityReferenceQuadratic

/-! # The actual affine normalization of a reference Hessian -/
noncomputable section
open Set Matrix InnerProductSpace
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma secondFDeriv_coordinatePullback_bilinear {u : E n → ℝ} (hu : ContDiff ℝ 2 u)
    (x v w : E n) :
    fderiv ℝ (fderiv ℝ (coordinatePullback u)) (coordinateEquiv n x)
      (coordinateEquiv n v) (coordinateEquiv n w) = fderiv ℝ (fderiv ℝ u) x v w := by
  have hv := secondFDeriv_coordinatePullback hu (coordinateEquiv n x) (coordinateEquiv n v)
  have hw := secondFDeriv_coordinatePullback hu (coordinateEquiv n x) (coordinateEquiv n w)
  have hvw := secondFDeriv_coordinatePullback hu (coordinateEquiv n x) (coordinateEquiv n (v+w))
  simp only [(coordinateEquiv n).symm_apply_apply,map_add,ContinuousLinearMap.add_apply] at hv hw hvw
  have hsr := (contDiff_coordinatePullback hu).contDiffAt.isSymmSndFDerivAt
    (x:=coordinateEquiv n x) (by norm_num) (coordinateEquiv n w) (coordinateEquiv n v)
  have hse := hu.contDiffAt.isSymmSndFDerivAt (x:=x) (by norm_num) w v
  linarith

lemma secondFDeriv_eq_transposed_hessianBilinear {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : ContDiffAt ℝ 2 f x) (v w : CoordinateSpace n) :
    fderiv ℝ (fderiv ℝ f) x v w = w ⬝ᵥ (coordinateHessian f x *ᵥ v) := by
  have hv : (∑ i, v i • (Pi.single i 1 : CoordinateSpace n)) = v := by
    ext j
    simp [Pi.single_apply]
  have hw : (∑ i, w i • (Pi.single i 1 : CoordinateSpace n)) = w := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [← hv, ← hw]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum,
    coordinateHessian_eq_secondFDerivAt hf]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coordinateHessian_toEuclideanCLM_eq_frechetHessian {u : E n → ℝ}
    (hu : ContDiff ℝ 2 u) (x : E n) :
    Matrix.toEuclideanCLM (𝕜:=ℝ) (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)) =
      frechetHessian u x := by
  apply ContinuousLinearMap.ext
  intro v
  apply (toDual ℝ (E n)).injective
  apply ContinuousLinearMap.ext
  intro w
  change inner ℝ (Matrix.toEuclideanCLM (𝕜:=ℝ)
    (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)) v) w =
      inner ℝ (frechetHessian u x v) w
  rw [inner_frechetHessian]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,Matrix.ofLp_toEuclideanCLM,star_trivial]
  change (coordinateEquiv n w) ⬝ᵥ (coordinateHessian (coordinatePullback u) (coordinateEquiv n x) *ᵥ coordinateEquiv n v) = _
  rw [← secondFDeriv_eq_transposed_hessianBilinear (contDiff_coordinatePullback hu).contDiffAt,
    secondFDeriv_coordinatePullback_bilinear hu]

lemma det_toEuclideanCLM (H : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.toEuclideanCLM (𝕜:=ℝ) H).det = H.det := by
  change LinearMap.det (Matrix.toEuclideanLin H) = H.det
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact LinearMap.det_toLin _ H

/-- The actual inverse square root, as an invertible continuous linear map. -/
def referenceNormalization {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) : E n ≃L[ℝ] E n where
  toFun := Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.inverseRoot H)
  invFun := Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.root H)
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv := by
    intro v
    change (Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.root H)*
      Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.inverseRoot H)) v = v
    rw [← map_mul,Whitening.root_mul_inverseRoot hH,map_one]
    rfl
  right_inv := by
    intro v
    change (Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.inverseRoot H)*
      Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.root H)) v = v
    rw [← map_mul,Whitening.inverseRoot_mul_root hH,map_one]
    rfl
  continuous_toFun := (Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.inverseRoot H)).continuous
  continuous_invFun := (Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.root H)).continuous

lemma referenceNormalization_det_one {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hdet : H.det = 1) : (referenceNormalization hH : E n →L[ℝ] E n).det = 1 := by
  change (Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.inverseRoot H)).det = 1
  rw [det_toEuclideanCLM,inverseRoot_det_one hH hdet]

lemma referenceNormalization_near_identity {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) {ε : ℝ} (hε : 0 ≤ ε) (hεhalf : ε ≤ 1/2)
    (hnear : ‖Matrix.toEuclideanCLM (𝕜:=ℝ) H-1‖ ≤ ε) :
    ‖(referenceNormalization hH : E n →L[ℝ] E n)-1‖ ≤ 2*ε ∧
      ‖((referenceNormalization hH).symm : E n →L[ℝ] E n)-1‖ ≤ ε := by
  have hh := matrix_roots_near_identity hH hε hεhalf hnear
  exact ⟨hh.2,hh.1⟩

/-- The transformed quadratic is genuinely the unit quadratic. -/
lemma referenceNormalization_quadratic {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (v : E n) :
    inner ℝ (Matrix.toEuclideanCLM (𝕜:=ℝ) H (referenceNormalization hH v))
      (referenceNormalization hH v) = ‖v‖^2 := by
  have hnorm : (Whitening.inverseRoot H)ᵀ*H*Whitening.inverseRoot H = 1 := by
    simpa only [(Whitening.inverseRoot_symm hH).eq] using Whitening.inverseRoot_covariance hH
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => v.ofLp ⬝ᵥ (A *ᵥ v.ofLp)) hnorm
  simp only [← Matrix.mulVec_mulVec,Matrix.one_mulVec] at he
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose] at he
  rw [← real_inner_self_eq_norm_sq]
  simpa only [referenceNormalization,EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toEuclideanCLM,star_trivial] using he

end GaussianTilt.MomentMapRegularity
