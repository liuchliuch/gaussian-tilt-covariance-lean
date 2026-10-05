import GaussianTilt.MomentMapRegularityImprovementCoefficients
import GaussianTilt.MomentMapCalabiAffine
import GaussianTilt.MomentMapSchauderAffineBounds

/-! # Quantitative control of the actual positive-root normalization

The square root and inverse square root are constructed matrix functions.
Their proximity to the identity follows from positivity and the exact
square/inverse identities, without a spectral regularity assumption.
-/
noncomputable section
open Set Matrix
open scoped Topology BigOperators
namespace GaussianTilt.MomentMapRegularity

section Hilbert
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

lemma norm_le_positive_add_identity (R : X →L[ℝ] X)
    (hR : ∀ v, 0 ≤ inner ℝ (R v) v) (v : X) : ‖v‖ ≤ ‖R v+v‖ := by
  have hsq := norm_add_sq_real (R v) v
  nlinarith [hR v,sq_nonneg ‖R v‖,norm_nonneg v,norm_nonneg (R v+v)]

lemma positive_square_root_sub_identity_norm_le (R H : X →L[ℝ] X)
    (hR : ∀ v, 0 ≤ inner ℝ (R v) v) (hRsq : R*R=H) :
    ‖R-1‖ ≤ ‖H-1‖ := by
  apply (R-1).opNorm_le_bound (norm_nonneg _)
  intro v
  have hprod : (R+1)*(R-1)=H-1 := by
    rw [mul_sub,add_mul,add_mul,hRsq]
    simp only [one_mul,mul_one,one_mul]
    abel
  calc
    ‖(R-1) v‖ ≤ ‖R ((R-1) v)+(R-1) v‖ := norm_le_positive_add_identity R hR _
    _ = ‖(H-1) v‖ := by
      change ‖((R+1)*(R-1)) v‖ = _
      rw [hprod]
    _ ≤ ‖H-1‖*‖v‖ := (H-1).le_opNorm v

lemma inverse_norm_le_two_of_root_near_identity (R L : X →L[ℝ] X)
    (hRL : R*L=1) {ε : ℝ} (hε : ε ≤ 1/2) (hnear : ‖R-1‖ ≤ ε) : ‖L‖ ≤ 2 := by
  apply L.opNorm_le_bound (by norm_num)
  intro v
  have he : R (L v)=v := congrArg (fun T : X →L[ℝ] X => T v) hRL
  have hh : ‖L v‖ ≤ ‖R (L v)‖+‖(R-1) (L v)‖ := by
    have h := norm_sub_le (R (L v)) ((R-1) (L v))
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_sub_cancel] using h
  have hb := ((R-1).le_opNorm (L v)).trans (mul_le_mul_of_nonneg_right hnear (norm_nonneg _))
  rw [he] at hh
  nlinarith [norm_nonneg (L v)]

lemma inverse_sub_identity_norm_le_two_mul (R L : X →L[ℝ] X)
    (hLR : L*R=1) (hRL : R*L=1) {ε : ℝ} (hε : 0 ≤ ε) (hεhalf : ε ≤ 1/2)
    (hnear : ‖R-1‖ ≤ ε) : ‖L-1‖ ≤ 2*ε := by
  have hL := inverse_norm_le_two_of_root_near_identity R L hRL hεhalf hnear
  have he : L*(1-R)=L-1 := by rw [mul_sub,mul_one,hLR]
  rw [← he]
  exact (norm_mul_le _ _).trans (mul_le_mul hL (by simpa only [norm_sub_rev] using hnear)
    (norm_nonneg _) (by norm_num))

end Hilbert

variable {n : ℕ}

/-- Quantitative control of both actual affine normalization factors. -/
theorem matrix_roots_near_identity {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    {ε : ℝ} (hε : 0 ≤ ε) (hεhalf : ε ≤ 1/2)
    (hnear : ‖Matrix.toEuclideanCLM (𝕜:=ℝ) H-1‖ ≤ ε) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.root H)-1‖ ≤ ε ∧
      ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.inverseRoot H)-1‖ ≤ 2*ε := by
  let R := Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.root H)
  let L := Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.inverseRoot H)
  let A := Matrix.toEuclideanCLM (𝕜:=ℝ) H
  have hR : ∀ v : E n, 0 ≤ inner ℝ (R v) v := by
    intro v
    change 0 ≤ inner ℝ (Matrix.toEuclideanCLM (𝕜:=ℝ) (Whitening.root H) v) v
    simp only [EuclideanSpace.inner_eq_star_dotProduct,Matrix.ofLp_toEuclideanCLM,star_trivial]
    simpa only [star_trivial] using (Whitening.root_posDef hH).posSemidef.2 v.ofLp
  have hRsq : R*R=A := by
    dsimp [R,A]
    rw [← map_mul,Whitening.root_mul_root hH.posSemidef]
  have hLR : L*R=1 := by
    dsimp [L,R]
    rw [← map_mul,Whitening.inverseRoot_mul_root hH,map_one]
  have hRL : R*L=1 := by
    dsimp [L,R]
    rw [← map_mul,Whitening.root_mul_inverseRoot hH,map_one]
  have hRnear := (positive_square_root_sub_identity_norm_le R A hR hRsq).trans hnear
  exact ⟨hRnear,inverse_sub_identity_norm_le_two_mul R L hLR hRL hε hεhalf hRnear⟩

end GaussianTilt.MomentMapRegularity
