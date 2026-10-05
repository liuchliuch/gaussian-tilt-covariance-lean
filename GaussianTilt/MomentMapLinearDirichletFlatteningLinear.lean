import GaussianTilt.MomentMapSchauderMatrixCalculus

/-! # Actual invertible row-replacement maps for boundary flattening -/
noncomputable section
open Set
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def flatteningCoordinate (j : Fin n) : KernelSpace n →L[ℝ] ℝ :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j

def boundaryRowLinear (L : KernelSpace n →L[ℝ] ℝ) (j : Fin n) : KernelSpace n →L[ℝ] KernelSpace n :=
  ContinuousLinearMap.id ℝ _ + (L - flatteningCoordinate j).smulRight (EuclideanSpace.basisFun (Fin n) ℝ j)

def boundaryRowInverseLinear (L : KernelSpace n →L[ℝ] ℝ) (j : Fin n) : KernelSpace n →L[ℝ] KernelSpace n :=
  ContinuousLinearMap.id ℝ _ + ((L (EuclideanSpace.basisFun (Fin n) ℝ j))⁻¹ •
    (flatteningCoordinate j - L)).smulRight (EuclideanSpace.basisFun (Fin n) ℝ j)

@[simp] lemma boundaryRowLinear_apply (L : KernelSpace n →L[ℝ] ℝ) (j : Fin n) (x : KernelSpace n) :
    boundaryRowLinear L j x = x + (L x - x j) • (EuclideanSpace.basisFun (Fin n) ℝ j) := rfl

@[simp] lemma boundaryRowInverseLinear_apply (L : KernelSpace n →L[ℝ] ℝ) (j : Fin n) (x : KernelSpace n) :
    boundaryRowInverseLinear L j x = x + ((x j - L x) / L (EuclideanSpace.basisFun (Fin n) ℝ j)) •
      (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  simp only [boundaryRowInverseLinear, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    flatteningCoordinate, PiLp.proj_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

@[simp] lemma boundaryRowLinear_normal (L : KernelSpace n →L[ℝ] ℝ) (j : Fin n) (x : KernelSpace n) :
    (boundaryRowLinear L j x) j = L x := by
  simp [boundaryRowLinear_apply, EuclideanSpace.basisFun_apply]

lemma boundaryRow_left_inverse (L : KernelSpace n →L[ℝ] ℝ) (j : Fin n)
    (hL : L (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) (x : KernelSpace n) :
    boundaryRowInverseLinear L j (boundaryRowLinear L j x) = x := by
  rw [boundaryRowInverseLinear_apply, boundaryRowLinear_normal, boundaryRowLinear_apply]
  simp only [map_add, map_smul, smul_eq_mul]
  have he : (L x - (L x + (L x - x j) * L (EuclideanSpace.basisFun (Fin n) ℝ j))) /
      L (EuclideanSpace.basisFun (Fin n) ℝ j) = -(L x - x j) := by field_simp; ring
  rw [he]
  module

lemma boundaryRow_right_inverse (L : KernelSpace n →L[ℝ] ℝ) (j : Fin n)
    (hL : L (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) (x : KernelSpace n) :
    boundaryRowLinear L j (boundaryRowInverseLinear L j x) = x := by
  rw [boundaryRowLinear_apply, boundaryRowInverseLinear_apply]
  have hb : (EuclideanSpace.basisFun (Fin n) ℝ j) j = 1 := by simp [EuclideanSpace.basisFun_apply]
  simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hb, mul_one]
  have he : (L x + (x j - L x) / L (EuclideanSpace.basisFun (Fin n) ℝ j) * L (EuclideanSpace.basisFun (Fin n) ℝ j)) -
      (x j + (x j - L x) / L (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      -((x j - L x) / L (EuclideanSpace.basisFun (Fin n) ℝ j)) := by field_simp; ring
  rw [he]
  module

/-- The derivative row replacement is an actual continuous linear
isomorphism, with its inverse explicitly constructed. -/
def boundaryRowEquiv (L : KernelSpace n →L[ℝ] ℝ) (j : Fin n)
    (hL : L (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) : KernelSpace n ≃L[ℝ] KernelSpace n where
  toFun := boundaryRowLinear L j
  invFun := boundaryRowInverseLinear L j
  left_inv := boundaryRow_left_inverse L j hL
  right_inv := boundaryRow_right_inverse L j hL
  map_add' := (boundaryRowLinear L j).map_add
  map_smul' := (boundaryRowLinear L j).map_smul
  continuous_toFun := (boundaryRowLinear L j).continuous
  continuous_invFun := (boundaryRowInverseLinear L j).continuous

end GaussianTilt.MomentMapLinearDirichlet
