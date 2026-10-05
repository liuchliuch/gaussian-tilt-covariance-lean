import GaussianTilt.MomentMapLinearDirichletVariableWeakAffineCoordinates

/-! # Literal L² energies under the actual frozen affine normalization -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 1000

/-- Exact set-integral covariance, with the true constant Jacobian. It
applies to the literal squared weak-gradient error without differentiating it. -/
lemma affine_integral_preimage (P:CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    {S:Set (CoordinateSpace n)} (hS:MeasurableSet S) (f:CoordinateSpace n → ℝ) :
    |P.toContinuousLinearMap.det| * (∫ z in P ⁻¹' S, f (P z))=∫ x in S,f x := by
  have hi : P '' (P ⁻¹' S)=S := image_preimage_eq _ P.surjective
  have hh := integral_image_eq_integral_abs_det_fderiv_smul volume (hS.preimage P.continuous.measurable)
    (fun x (_:x∈P ⁻¹' S)=>P.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt) P.injective.injOn f
  simp only [ContinuousLinearEquiv.coe_coe] at hh
  rw [hi] at hh
  rw [← integral_const_mul]
  exact hh.symm

lemma affine_gradient_energy_change (P:CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    {S:Set (CoordinateSpace n)} (hS:MeasurableSet S)
    (G:CoordinateSpace n → CoordinateSpace n) (q:CoordinateSpace n) :
    |P.toContinuousLinearMap.det| * (∫ z in P ⁻¹' S,
      ‖(coordinateEquiv n).symm ((LinearMap.toMatrix' P.toLinearMap)ᵀ *ᵥ (G (P z)-q))‖^2)=
      ∫ x in S,‖(coordinateEquiv n).symm ((LinearMap.toMatrix' P.toLinearMap)ᵀ *ᵥ (G x-q))‖^2 :=
  affine_integral_preimage P hS (fun x => ‖(coordinateEquiv n).symm ((LinearMap.toMatrix' P.toLinearMap)ᵀ *ᵥ (G x-q))‖^2)

lemma affine_normal_slope (P:CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (j:Fin n) {c:ℝ} (hplane:∀x,(P x) j=c*x j) (t:ℝ) :
    (LinearMap.toMatrix' P.toLinearMap)ᵀ *ᵥ (Pi.single j t)=Pi.single j (c*t) := by
  ext i
  simp only [Matrix.mulVec_single,Matrix.transpose_apply]
  have hh := hplane (Pi.single i 1)
  change LinearMap.toMatrix' P.toLinearMap j i=c*((Pi.single i (1:ℝ)):CoordinateSpace n) j at hh
  change LinearMap.toMatrix' P.toLinearMap j i*t=(Pi.single j (c*t) : CoordinateSpace n) i
  rw [hh]
  by_cases hij:i=j
  · subst i
    simp
  · have hji:j≠i := Ne.symm hij
    simp [Pi.single_eq_of_ne hij,Pi.single_eq_of_ne hji]

/-- The transformed error is the actual matrix transform of the physical
weak-gradient error. Normal slopes remain normal because the map truly
preserves the boundary hyperplane. -/
lemma affine_gradient_error_normal (P:CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (j:Fin n) {c:ℝ} (hplane:∀x,(P x) j=c*x j) (t:ℝ) (g:CoordinateSpace n) :
    (LinearMap.toMatrix' P.toLinearMap)ᵀ *ᵥ g-Pi.single j (c*t)=
      (LinearMap.toMatrix' P.toLinearMap)ᵀ *ᵥ (g-Pi.single j t) := by
  rw [Matrix.mulVec_sub,affine_normal_slope P j hplane]

end GaussianTilt.MomentMapLinearDirichlet
