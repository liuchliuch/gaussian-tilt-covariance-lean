import GaussianTilt.MomentMapRegularityImprovementReferenceNormalization
import GaussianTilt.MomentMapRegularityConstantDensityCalabiBounds

/-! # Uniform initial normalization before source near-quadraticity -/
noncomputable section
open Matrix
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000

def initialInverseNormalizationBound (n : ℕ) (K : ℝ) : ℝ :=
  Real.sqrt ((n:ℝ)^2*(n.factorial:ℝ)*(max K 1)^n)

lemma referenceNormalization_norm_bound {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hdet : H.det=1) {K : ℝ} (hK : ∀ i j, |H i j|≤K) :
    ‖(referenceNormalization hH : E n →L[ℝ] E n)‖≤ initialInverseNormalizationBound n K := by
  let I : ℝ := (n.factorial:ℝ)*(max K 1)^n
  have hI : 0≤I := by dsimp [I]; positivity
  have hentry := inverse_entry_bound_of_det_one hdet hK
  have hquad (v : E n) : euclideanQuadratic H⁻¹ v≤((n:ℝ)^2*I)*‖v‖^2 := by
    have hh := quadraticForm_upper_of_entry_bound hI hentry (coordinateEquiv n v)
    simpa only [(coordinateEquiv n).symm_apply_apply] using hh
  have hroot : (Whitening.inverseRoot H)ᵀ*Whitening.inverseRoot H=H⁻¹ := by
    rw [(Whitening.inverseRoot_symm hH).eq]
    dsimp [Whitening.inverseRoot]
    rw [← Matrix.mul_inv_rev,Whitening.root_mul_root hH.posSemidef]
  have hΛ : 0≤(n:ℝ)^2*I := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  change ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.inverseRoot H) v‖^2≤_
  rw [norm_toEuclideanCLM_sq,hroot,mul_pow]
  rw [Real.sq_sqrt (by positivity : 0≤(n:ℝ)^2*(n.factorial:ℝ)*(max K 1)^n)]
  convert hquad v using 1 <;> dsimp [I] <;> ring

lemma referenceNormalization_inverse_norm_bound {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) {K : ℝ} (hK0 : 0≤K) (hK : ∀ i j, |H i j|≤K) :
    ‖((referenceNormalization hH).symm : E n →L[ℝ] E n)‖≤Real.sqrt ((n:ℝ)^2*K) := by
  apply norm_coefficient_sqrt_le hH (by positivity)
  intro v
  have hh := quadraticForm_upper_of_entry_bound hK0 hK (coordinateEquiv n v)
  simpa only [(coordinateEquiv n).symm_apply_apply] using hh

end GaussianTilt.MomentMapRegularity
