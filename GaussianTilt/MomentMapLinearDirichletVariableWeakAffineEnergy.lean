import GaussianTilt.MomentMapLinearDirichletVariableWeakAffine

/-! # Exact weak frozen-SPD energy covariance under an actual affine map -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 1000

lemma dotProduct_transpose_mulVec (P:Matrix (Fin n) (Fin n) ℝ) (u q:CoordinateSpace n) :
    (Pᵀ *ᵥ u) ⬝ᵥ q=u ⬝ᵥ (P *ᵥ q) := by
  rw [dotProduct_comm,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,dotProduct_comm]

lemma affine_covariance_energy_algebra {P Q B:Matrix (Fin n) (Fin n) ℝ}
    (hQP:Q*P=1) (hB:P*Pᵀ=B) (u q:CoordinateSpace n) :
    u ⬝ᵥ (B *ᵥ (Qᵀ *ᵥ q))=(Pᵀ *ᵥ u) ⬝ᵥ q := by
  rw [← hB,Matrix.mulVec_mulVec,dotProduct_transpose_mulVec]
  have hm : P*Pᵀ*Qᵀ=P := by
    rw [Matrix.mul_assoc,← Matrix.transpose_mul,hQP,Matrix.transpose_one,mul_one]
  rw [hm]

lemma chartJacobian_linearEquiv (P:CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (x:CoordinateSpace n) :
    chartJacobian P x=LinearMap.toMatrix' P.toLinearMap := by
  simp only [chartJacobian,P.fderiv]
  rfl

/-- Constant-Jacobian change of variables for the actual weak gradient
and the transformed smooth compact test. -/
lemma frozen_affine_energy_change (P:CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    {B:Matrix (Fin n) (Fin n) ℝ}
    (hB:LinearMap.toMatrix' P.toLinearMap*(LinearMap.toMatrix' P.toLinearMap)ᵀ=B)
    (G:CoordinateSpace n → CoordinateSpace n) (τ:smoothCompactCore n) :
    (∫ x,G x ⬝ᵥ (B *ᵥ coordinateGradient (τ.1 ∘ P.symm) x))=
      |P.toContinuousLinearMap.det| *(∫ z,((LinearMap.toMatrix' P.toLinearMap)ᵀ *ᵥ G (P z)) ⬝ᵥ coordinateGradient τ.1 z) := by
  have harea := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
    (fun x (_:x∈(univ:Set (CoordinateSpace n)))=>P.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt)
    P.injective.injOn (fun x=>G x ⬝ᵥ (B *ᵥ coordinateGradient (τ.1 ∘ P.symm) x))
  have him : P '' (univ:Set (CoordinateSpace n))=univ := by rw [image_univ,P.surjective.range_eq]
  simp only [ContinuousLinearEquiv.coe_coe] at harea
  rw [him,setIntegral_univ,setIntegral_univ] at harea
  rw [harea,← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only
  rw [coordinateGradient_comp_chart P.symm.differentiable (τ.2.1.differentiable (by simp)),P.symm_apply_apply,
    chartJacobian_linearEquiv]
  change |P.toContinuousLinearMap.det| *(G (P z) ⬝ᵥ (B *ᵥ ((LinearMap.toMatrix' P.symm.toLinearMap)ᵀ *ᵥ coordinateGradient τ.1 z)))=_
  rw [affine_covariance_energy_algebra (P:=LinearMap.toMatrix' P.toLinearMap)
    (Q:=LinearMap.toMatrix' P.symm.toLinearMap) ?_ hB]
  have hi := chartJacobian_inverse_of_left_inverse isOpen_univ P.differentiable
    P.symm.differentiable.differentiableOn (fun x _=>P.apply_symm_apply x) (mem_univ (0:CoordinateSpace n))
  simpa only [chartJacobian_linearEquiv] using hi

/-- Every compact transformed test is a genuine admissible physical test;
there is no assumed weak-to-classical derivative of the unknown. -/
theorem frozen_affine_weak_harmonic {D D':Set (CoordinateSpace n)}
    (P:CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (hPD:MapsTo P D' D) {B:Matrix (Fin n) (Fin n) ℝ}
    (hB:LinearMap.toMatrix' P.toLinearMap*(LinearMap.toMatrix' P.toLinearMap)ᵀ=B)
    (G:CoordinateSpace n → CoordinateSpace n)
    (heq:∀ξ:smoothCompactCore n,tsupport ξ.1⊆D →
      (∫ x,G x ⬝ᵥ (B *ᵥ coordinateGradient ξ.1 x))=0)
    (τ:smoothCompactCore n) (hτ:tsupport τ.1⊆D') :
    (∫ z,((LinearMap.toMatrix' P.toLinearMap)ᵀ *ᵥ G (P z)) ⬝ᵥ coordinateGradient τ.1 z)=0 := by
  let ξ:smoothCompactCore n := ⟨τ.1 ∘ P.symm,τ.2.1.comp P.symm.contDiff,τ.2.2.comp_homeomorph P.symm.toHomeomorph⟩
  have hξ:tsupport ξ.1⊆D := by
    intro x hx
    have hi := tsupport_comp_subset_preimage P.symm.continuous τ.1 hx
    have hp := hPD (hτ hi)
    simpa only [P.apply_symm_apply] using hp
  have hh := heq ξ hξ
  change (∫ x,G x ⬝ᵥ (B *ᵥ coordinateGradient (τ.1 ∘ P.symm) x))=0 at hh
  rw [frozen_affine_energy_change P hB G τ] at hh
  exact (mul_eq_zero.mp hh).resolve_left (abs_ne_zero.mpr (continuousLinearEquiv_det_ne_zero P))

end GaussianTilt.MomentMapLinearDirichlet
