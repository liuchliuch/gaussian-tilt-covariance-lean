import GaussianTilt.MomentMapCalabiAffine

/-! # Individual cubic coefficients from the actual metric energy -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma coordinate_square_le_factored_metric
    (R S : Matrix ι ι ℝ) (hRS : R * S = 1) (v : ι → ℝ) (i : ι) :
    (v i)^2 ≤ (R * Rᵀ) i i * GaussianTilt.matrixQuadratic (Sᵀ * S) v := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun j => R i j) (g := fun j => (S *ᵥ v) j)
  have hv : (∑ j, R i j * (S *ᵥ v) j) = v i := by
    change (R *ᵥ (S *ᵥ v)) i = v i
    rw [Matrix.mulVec_mulVec, hRS, Matrix.one_mulVec]
  have hR : (∑ j, R i j ^ 2) = (R * Rᵀ) i i := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  have hS : (∑ j, (S *ᵥ v) j ^ 2) = GaussianTilt.matrixQuadratic (Sᵀ * S) v := by
    have he := GaussianTilt.Whitening.matrixQuadratic_mulVec (1 : Matrix ι ι ℝ) S v
    simpa only [GaussianTilt.matrixQuadratic, Matrix.one_mulVec, dotProduct, ← pow_two,
      Matrix.mul_one] using he
  rwa [hv, hR, hS] at hCS

/-- Exact tensor-coordinate coercivity: no tensor spectral theorem or
assumed lower bound is needed. -/
theorem cubic_coefficient_square_le_metric_energy
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (T : ι → ι → ι → ℝ) (i j k : ι) :
    T i j k ^ 2 ≤ (H i i * H j j * H k k) * cubicMetricEnergy H⁻¹ T := by
  let R := Whitening.root H
  let S := Whitening.inverseRoot H
  have hRs : Rᵀ = R := (Whitening.root_symm H).eq
  have hSs : Sᵀ = S := (Whitening.inverseRoot_symm hH).eq
  have hRS : R * S = 1 := Whitening.root_mul_inverseRoot hH
  have hRR : R * R = H := Whitening.root_mul_root hH.posSemidef
  have hSS : S * S = H⁻¹ := by
    dsimp [S, Whitening.inverseRoot]
    rw [← Matrix.mul_inv_rev, Whitening.root_mul_root hH.posSemidef]
  have hRS₃ : cubicKronecker R * cubicKronecker S = 1 := by
    rw [← cubicKronecker_mul, hRS, cubicKronecker_one]
  have hR₃ : cubicKronecker R * (cubicKronecker R)ᵀ = cubicKronecker H := by
    rw [← cubicKronecker_transpose, hRs, ← cubicKronecker_mul, hRR]
  have hS₃ : (cubicKronecker S)ᵀ * cubicKronecker S = cubicKronecker H⁻¹ := by
    rw [← cubicKronecker_transpose, hSs, ← cubicKronecker_mul, hSS]
  have he := coordinate_square_le_factored_metric (cubicKronecker R) (cubicKronecker S)
    hRS₃ (cubicFlatten T) (i, j, k)
  rw [hR₃, hS₃, ← cubicMetricEnergy_eq_quadratic] at he
  simpa only [cubicFlatten, cubicKronecker, Matrix.kronecker_apply, mul_assoc] using he

end GaussianTilt.MomentMapRegularity
