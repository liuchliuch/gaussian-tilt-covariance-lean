import GaussianTilt.MomentMapRegularityAffineHessian
import GaussianTilt.LetwinMomentLaw

/-! # Affine source normalization and genuine moment-law transport -/
noncomputable section
open MeasureTheory Matrix Set
open scoped BigOperators Topology ContDiff ENNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def linearSourcePotential (φ : CoordinateSpace n → ℝ)
    (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (x : CoordinateSpace n) : ℝ :=
  φ (e x) - Real.log |LinearMap.det e.toLinearEquiv.toLinearMap|

lemma map_volume_inverse_linear (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    (volume : Measure (CoordinateSpace n)).map e.symm =
      ENNReal.ofReal |LinearMap.det e.toLinearEquiv.toLinearMap| • volume := by
  ext A hA
  rw [Measure.map_apply e.symm.continuous.measurable hA, Measure.smul_apply, smul_eq_mul]
  exact Measure.addHaar_preimage_linearEquiv volume e.symm.toLinearEquiv A

/-- The normalization constant is the exact source-coordinate Jacobian. -/
theorem potentialMeasure_linearSourcePotential {φ : CoordinateSpace n → ℝ}
    (hφ : Continuous φ) (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    potentialMeasure (linearSourcePotential φ e) = (potentialMeasure φ).map e.symm := by
  let c := |LinearMap.det e.toLinearEquiv.toLinearMap|
  have hc : 0 < c := abs_pos.mpr e.toLinearEquiv.isUnit_det'.ne_zero
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-φ (e x)))) := by fun_prop
  have hmap := GaussianTilt.map_withDensity_comp e.symm.toHomeomorph.measurableEmbedding volume
    (fun x => ENNReal.ofReal (Real.exp (-φ (e x))))
  change Measure.map e.symm (volume.withDensity (fun p => ENNReal.ofReal (Real.exp (-φ (e (e.symm p)))))) =
    (Measure.map e.symm volume).withDensity (fun x => ENNReal.ofReal (Real.exp (-φ (e x)))) at hmap
  simp only [e.apply_symm_apply] at hmap
  rw [map_volume_inverse_linear, withDensity_smul_measure,
    ← withDensity_smul (ENNReal.ofReal c) hm] at hmap
  unfold potentialMeasure
  rw [hmap]
  congr 1
  funext x
  change ENNReal.ofReal (Real.exp (-(φ (e x) - Real.log c))) =
    ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-φ (e x)))
  rw [show -(φ (e x) - Real.log c) = Real.log c + -φ (e x) by ring,
    Real.exp_add, Real.exp_log hc, ENNReal.ofReal_mul hc.le]

lemma linearSourcePotential_contDiff {k : WithTop ℕ∞} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ k φ) (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    ContDiff ℝ k (linearSourcePotential φ e) := (hφ.comp e.contDiff).sub contDiff_const

lemma linearSourcePotential_strictConvex {φ : CoordinateSpace n → ℝ}
    (hc : StrictConvexOn ℝ univ φ) (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    StrictConvexOn ℝ univ (linearSourcePotential φ e) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have h := hc.2 (mem_univ (e x)) (mem_univ (e y)) (fun h => hxy (e.injective h)) ha hb hab
  simp only [linearSourcePotential, map_add, map_smul, smul_eq_mul]
  have he : a * Real.log |LinearMap.det e.toLinearEquiv.toLinearMap| +
      b * Real.log |LinearMap.det e.toLinearEquiv.toLinearMap| =
      Real.log |LinearMap.det e.toLinearEquiv.toLinearMap| := by rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul] at h
  nlinarith

lemma linearSourcePotential_probability {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    IsProbabilityMeasure (potentialMeasure (linearSourcePotential φ e)) := by
  rw [potentialMeasure_linearSourcePotential hφ e]
  exact Measure.isProbabilityMeasure_map e.symm.continuous.measurable.aemeasurable

def transposeSourceEquiv (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.det ≠ 0) :
    CoordinateSpace n ≃L[ℝ] CoordinateSpace n :=
  coordinateMatrixEquiv Tᵀ (by simpa using hT)

@[simp] lemma transposeSourceEquiv_apply (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.det ≠ 0)
    (x : CoordinateSpace n) : transposeSourceEquiv T hT x = Tᵀ *ᵥ x :=
  coordinateMatrixEquiv_apply _ _ _

lemma coordinateMatrixEquiv_det (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.det ≠ 0) :
    LinearMap.det (coordinateMatrixEquiv T hT).toLinearEquiv.toLinearMap = T.det := by
  change LinearMap.det (Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n)) T) = _
  exact LinearMap.det_toLin _ _

lemma transposeSourceEquiv_det (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.det ≠ 0) :
    LinearMap.det (transposeSourceEquiv T hT).toLinearEquiv.toLinearMap = T.det := by
  rw [transposeSourceEquiv, coordinateMatrixEquiv_det, Matrix.det_transpose]

lemma matrix_linearSourcePotential_formula (φ : CoordinateSpace n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.det ≠ 0) (x : CoordinateSpace n) :
    linearSourcePotential φ (transposeSourceEquiv T hT) x =
      φ (Tᵀ *ᵥ x) - Real.log |T.det| := by
  rw [linearSourcePotential, transposeSourceEquiv_apply, transposeSourceEquiv_det]

lemma gradient_linearSourcePotential {φ : CoordinateSpace n → ℝ}
    (hφ : Differentiable ℝ φ) (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.det ≠ 0)
    (x : CoordinateSpace n) :
    coordinateGradient (linearSourcePotential φ (transposeSourceEquiv T hT)) x =
      T *ᵥ coordinateGradient φ (Tᵀ *ᵥ x) := by
  ext i
  change coordinateDerivative i (fun y => φ (transposeSourceEquiv T hT y) - _) x = _
  have he : coordinateDerivative i (fun y => φ (transposeSourceEquiv T hT y) -
      Real.log |LinearMap.det (transposeSourceEquiv T hT).toLinearEquiv.toLinearMap|) x =
      coordinateDerivative i (φ ∘ (transposeSourceEquiv T hT).toContinuousLinearMap) x := by
    unfold coordinateDerivative
    rw [fderiv_sub_const]
    rfl
  rw [he, coordinateDerivative_comp_linear hφ]
  change (∑ a, transposeSourceEquiv T hT (Pi.single i 1) a *
      coordinateDerivative a φ (transposeSourceEquiv T hT x)) = _
  simp [transposeSourceEquiv_apply, Matrix.mulVec, dotProduct, Pi.single_apply, coordinateGradient]

/-- Whitening the target by T is implemented by the actual normalized source
φ(Tᵀx)−log|detT|. Its moment measure is exactly the linearly transported law. -/
theorem momentMeasure_linearSourcePotential {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.det ≠ 0) :
    momentMeasure (linearSourcePotential φ (transposeSourceEquiv T hT)) =
      (momentMeasure φ).map (coordinateMatrixMap T) := by
  let e := transposeSourceEquiv T hT
  have hd := hφ.differentiable le_rfl
  rw [momentMeasure, potentialMeasure_linearSourcePotential hφ.continuous e,
    Measure.map_map (continuous_coordinateGradient (linearSourcePotential_contDiff hφ e)).measurable
      e.symm.continuous.measurable, momentMeasure,
    Measure.map_map (coordinateMatrixMap T).continuous.measurable (continuous_coordinateGradient hφ).measurable]
  congr 1
  funext x
  change coordinateGradient (linearSourcePotential φ e) (e.symm x) = T *ᵥ coordinateGradient φ x
  rw [gradient_linearSourcePotential hd T hT]
  have he : Tᵀ *ᵥ e.symm x = x := e.apply_symm_apply x
  rw [he]

lemma linearSourcePotential_hessian_bound {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    {S : ℝ} (hS : ∀ x i j, |coordinateHessian φ x i j| ≤ S) :
    ∀ x i j, |coordinateHessian (linearSourcePotential φ e) x i j| ≤
      (n : ℝ)^2 * max S 0 * ‖e.toContinuousLinearMap‖^2 :=
  hessian_bound_comp_linear hφ e.toContinuousLinearMap hS _

/-- Every invertible linear target image has a constructed smooth, strictly
convex normalized moment source with bounded Hessian, whenever the original
law has one. This is the actual whitening step in the approximation. -/
theorem exists_linear_image_moment_source {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hc : StrictConvexOn ℝ univ φ)
    {S : ℝ} (hS : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.det ≠ 0) :
    ∃ ψ : CoordinateSpace n → ℝ, IsProbabilityMeasure (potentialMeasure ψ) ∧
      ContDiff ℝ ∞ ψ ∧ StrictConvexOn ℝ univ ψ ∧
      (∃ B : ℝ, ∀ x i j, |coordinateHessian ψ x i j| ≤ B) ∧
      momentMeasure ψ = (momentMeasure φ).map (coordinateMatrixMap T) := by
  let e := transposeSourceEquiv T hT
  refine ⟨linearSourcePotential φ e, linearSourcePotential_probability hφ.continuous e,
    linearSourcePotential_contDiff hφ e, linearSourcePotential_strictConvex hc e,
    ⟨_, linearSourcePotential_hessian_bound (contDiff_infty.mp hφ 2) e hS⟩, ?_⟩
  exact momentMeasure_linearSourcePotential (contDiff_infty.mp hφ 1) T hT

end GaussianTilt.MomentMapRegularity
