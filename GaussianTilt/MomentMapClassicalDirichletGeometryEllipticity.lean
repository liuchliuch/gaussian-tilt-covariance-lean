import GaussianTilt.MomentMapClassicalDirichletGeometryCoordinates

/-! # Quantitative coordinate ellipticity of the actual defining potential -/
noncomputable section
open Set Matrix
open scoped BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateEuclidean_norm_sq (v : CoordinateSpace n) :
    ‖(coordinateEquiv n).symm v‖^2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ i, ‖v i‖^2) = ∑ i, v i*v i
  simp only [Real.norm_eq_abs, ← pow_two, sq_abs]

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

lemma coordinate_hessian_quadratic_lower (x v : CoordinateSpace n) :
    d.modulus * (v ⬝ᵥ v) ≤ matrixQuadratic (coordinateHessian d.coordinateDefining x) v := by
  have hh := d.hessian_lower ((coordinateEquiv n).symm x) ((coordinateEquiv n).symm v)
  rw [coordinateEuclidean_norm_sq, ← secondFDeriv_coordinatePullback (contDiff_infty.mp d.smooth 2)] at hh
  change d.modulus * (v ⬝ᵥ v) ≤ fderiv ℝ (fderiv ℝ d.coordinateDefining) x v v at hh
  rwa [secondFDeriv_eq_hessianQuadratic (contDiff_infty.mp d.coordinateDefining_smooth 2).contDiffAt] at hh

/-- The constructed lower bound is exactly a scalar-matrix lower bound in
ordinary coordinates, with the same strictly positive modulus. -/
lemma coordinate_hessian_sub_modulus_posSemidef (x : CoordinateSpace n) :
    (coordinateHessian d.coordinateDefining x - d.modulus • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  refine ⟨(d.coordinateDefining_hessian_posDef x).isHermitian.sub
    ((Matrix.PosSemidef.one.smul d.modulus_pos.le).isHermitian), ?_⟩
  intro v
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul]
  exact sub_nonneg.mpr (d.coordinate_hessian_quadratic_lower x v)

/-- The boundary barrier's coercive operator bound follows from the actual
coordinate Hessian; uniform ellipticity is not supplied as an assumption. -/
lemma modulus_mul_trace_le_hessian_trace (x : CoordinateSpace n)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    d.modulus * B.trace ≤ (B * coordinateHessian d.coordinateDefining x).trace := by
  have hh := trace_mul_nonneg_of_posSemidef B _ hB (d.coordinate_hessian_sub_modulus_posSemidef x)
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul] at hh
  linarith

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
