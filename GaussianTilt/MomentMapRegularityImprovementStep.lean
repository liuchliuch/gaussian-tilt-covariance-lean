import GaussianTilt.MomentMapRegularityImprovementCoefficients
import GaussianTilt.MomentMapRegularityImprovementRescaling

/-! # The actual reference-driven quadratic improvement step

The normalization map is constructed from the real Hessian of the reference.
The source is only convex: its next value error and affine distortion are
consequences of comparison and Taylor's theorem.
-/
noncomputable section
open Set InnerProductSpace
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapSchauder
variable {n : ℕ}

 theorem actual_reference_improvement_step {u v : E n → ℝ}
    (huc : Continuous u) (hconv : ConvexOn ℝ univ u) (hv : ContDiff ℝ 2 v)
    (hPD : (coordinateHessian (coordinatePullback v) 0).PosDef)
    (hdet : (coordinateHessian (coordinatePullback v) 0).det=1)
    {a : ℝ} {p : E n} {R r ρ S σ ε C θ : ℝ}
    (hr : 0 < r) (hrR : r≤R) (hρ : 0<ρ) (hS : 0≤S)
    (hσ : 0≤σ) (hε : 0≤ε) (hC : 0≤C) (hθ : 0≤θ) (hθhalf : θ≤1/2)
    (hcoef : 4*(σ+ε)/r^2+4*C*r≤θ) (hregion : ρ*(1+2*θ)*S≤R)
    (hnear : ∀ y, ‖y‖≤R → |u y-‖y‖^2/2|≤σ)
    (hcompare : ∀ y, ‖y‖≤R → |u y-v y|≤ε)
    (hTaylor : ∀ y, ‖y‖≤R →
      |v y-quadraticJet a p 0 (frechetHessian v 0) y|≤C*‖y‖^3) :
    ∃ L : E n ≃L[ℝ] E n,
      (L : E n →L[ℝ] E n).det=1 ∧
      ‖(L : E n →L[ℝ] E n)-1‖≤2*θ ∧
      ‖(L.symm : E n →L[ℝ] E n)-1‖≤θ ∧
      Continuous (improvementRescale u p L ρ) ∧
      ConvexOn ℝ univ (improvementRescale u p L ρ) ∧
      improvementRescale u p L ρ 0=0 ∧
      ∀ x, ‖x‖≤S → |improvementRescale u p L ρ x-‖x‖^2/2|≤
        2*ε/ρ^2+C*ρ*(1+2*θ)^3*S^3 := by
  let H := coordinateHessian (coordinatePullback v) 0
  have hH : Matrix.toEuclideanCLM (𝕜:=ℝ) H=frechetHessian v 0 := by
    simpa only [map_zero] using coordinateHessian_toEuclideanCLM_eq_frechetHessian hv 0
  have hvnear : ∀ y, ‖y‖≤R → |v y-‖y‖^2/2|≤σ+ε := by
    intro y hy
    exact (abs_sub_le (v y) (u y) (‖y‖^2/2)).trans
      (by have hh:=hcompare y hy; rw [abs_sub_comm] at hh; linarith [hnear y hy])
  have hbound := (quadratic_coefficients_near_identity (frechetHessian_symmetric hv 0)
    hr hrR (add_nonneg hσ hε) hC hvnear hTaylor).1.trans hcoef
  have hroots := referenceNormalization_near_identity hPD hθ hθhalf (by
    change ‖Matrix.toEuclideanCLM (𝕜:=ℝ) H-1‖≤θ
    rw [hH]
    exact hbound)
  let L := referenceNormalization hPD
  have hnorm : ‖(L : E n →L[ℝ] E n)‖≤1+2*θ := by
    have hh := norm_add_le ((L : E n →L[ℝ] E n)-1) (1 : E n →L[ℝ] E n)
    rw [sub_add_cancel] at hh
    have h1 : ‖(1 : E n →L[ℝ] E n)‖≤1 := ContinuousLinearMap.norm_id_le
    linarith [hroots.1]
  refine ⟨L,referenceNormalization_det_one hPD hdet,hroots.1,hroots.2,
    improvementRescale_continuous huc p L ρ,improvementRescale_convex hconv p L ρ,
    improvementRescale_zero u p L ρ,?_⟩
  apply improvementRescale_error hρ (hr.le.trans hrR) hS (by positivity) hε hC hnorm hregion
    (H:=frechetHessian v 0) _ hcompare hTaylor
  intro x
  rw [← hH]
  exact referenceNormalization_quadratic hPD x

end GaussianTilt.MomentMapRegularity
