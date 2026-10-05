import GaussianTilt.MomentMapSchauderInteriorFirstJet

/-! # Actual coefficient-entry control from the ellipticity upper bound -/
noncomputable section
open Matrix
open scoped MatrixOrder
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma norm_coefficient_operator_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hupper : ∀ v : KernelSpace n, euclideanQuadratic A v ≤ Λ*‖v‖^2) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A‖ ≤ Λ := by
  let P := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (CFC.sqrt A)
  have hP : ‖P‖ ≤ Real.sqrt Λ := norm_coefficient_sqrt_le hA hΛ hupper
  have hP2 : ‖P‖^2 ≤ Λ := by
    have hh := (sq_le_sq₀ (norm_nonneg P) (Real.sqrt_nonneg Λ)).mpr hP
    rwa [Real.sq_sqrt hΛ] at hh
  have he : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A=P*P := by
    dsimp [P]
    rw [← map_mul,CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
  rw [he]
  exact (norm_mul_le P P).trans (by nlinarith only [hP2])

lemma abs_coefficient_entry_le_upper {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hupper : ∀ v : KernelSpace n, euclideanQuadratic A v ≤ Λ*‖v‖^2)
    (i k : Fin n) : |A i k| ≤ Λ := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A
  have he := toEuclideanCLM_basis_apply A k i
  rw [← he]
  apply (PiLp.norm_apply_le (L (EuclideanSpace.basisFun (Fin n) ℝ k)) i).trans
  have hb := L.le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ k)
  rw [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one] at hb
  exact hb.trans (norm_coefficient_operator_le hA hΛ hupper)

end GaussianTilt.MomentMapSchauder
