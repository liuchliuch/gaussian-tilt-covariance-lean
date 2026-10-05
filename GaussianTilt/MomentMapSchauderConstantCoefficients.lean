import GaussianTilt.MomentMapSchauderPoissonEstimate
import GaussianTilt.MomentMapSchauderEuclideanOperator

/-!
# Genuine Schauder estimate for every constant elliptic coefficient

The actual matrix square root and its actual inverse reduce the operator
to the proved Poisson estimate. Bounds are uniform over coefficients with
the displayed Euclidean ellipticity constants.
-/
noncomputable section
open Matrix Set MeasureTheory
open scoped BigOperators ContDiff MatrixOrder
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic

variable {n : ℕ}

def positiveMatrixEquiv {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    KernelSpace n ≃L[ℝ] KernelSpace n where
  toFun := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A
  invFun := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv := by
    intro v
    change (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ *
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) v = v
    rw [← map_mul, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), map_one]
    rfl
  right_inv := toEuclideanCLM_inv_cancel hA
  continuous_toFun := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A).continuous
  continuous_invFun := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹).continuous

@[simp] lemma positiveMatrixEquiv_apply {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (x : KernelSpace n) : positiveMatrixEquiv hA x = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A x := rfl

@[simp] lemma positiveMatrixEquiv_symm_apply {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (x : KernelSpace n) : (positiveMatrixEquiv hA).symm x =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ x := rfl

set_option maxHeartbeats 1200000 in
/-- A quantitative constant-coefficient Schauder theorem with no elliptic
regularity premise. The constant is chosen before the matrix or solution,
and depends only on dimension, exponent, and lower/upper ellipticity. -/
theorem exists_compact_constant_elliptic_schauder [NeZero n]
    {α lam Λ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef →
      (∀ v : KernelSpace n, lam * ‖v‖ ^ 2 ≤ euclideanQuadratic A v) →
      (∀ v : KernelSpace n, euclideanQuadratic A v ≤ Λ * ‖v‖ ^ 2) →
      ∀ u : KernelSpace n → ℝ, ContDiff ℝ 2 u → HasCompactSupport u → ∀ U F H : ℝ,
      0 ≤ U → 0 ≤ F → 0 ≤ H → (∀ x, |u x| ≤ U) →
      (∀ x, |euclideanEllipticOperator A u x| ≤ F) →
      (∀ x y, |euclideanEllipticOperator A u x - euclideanEllipticOperator A u y| ≤ H * ‖x - y‖ ^ α) →
      (∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C * (U + F + H)) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * (U + F + H) * ‖x - y‖ ^ α) := by
  obtain ⟨Cp, hCp, hp⟩ := exists_compact_poisson_schauder (n := n) hα hα1
  let a : ℝ := Real.sqrt Λ
  let b : ℝ := (Real.sqrt lam)⁻¹
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := inv_nonneg.mpr (Real.sqrt_nonneg _)
  let Q : ℝ := 1 + a ^ α
  let R : ℝ := 1 + b ^ 2
  let S : ℝ := 1 + b ^ α
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  let C : ℝ := Cp * Q * R * S
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro A hA hlower hupper u hu huc U F H hU hF hH hub hfb hfh
  let e : KernelSpace n ≃L[ℝ] KernelSpace n := positiveMatrixEquiv hA.posDef_sqrt
  let P : KernelSpace n →L[ℝ] KernelSpace n := e.toContinuousLinearMap
  let J : KernelSpace n →L[ℝ] KernelSpace n := e.symm.toContinuousLinearMap
  have hP : ‖P‖ ≤ a := norm_coefficient_sqrt_le hA hΛ hupper
  have hJ : ‖J‖ ≤ b := norm_inverse_coefficient_sqrt_le hA hlam hlower
  have hJ2 : ‖J‖ ^ 2 ≤ b ^ 2 := (sq_le_sq₀ (norm_nonneg _) hb).mpr hJ
  let w : KernelSpace n → ℝ := u ∘ e
  have hw : ContDiff ℝ 2 w := hu.comp e.contDiff
  have hwc : HasCompactSupport w := huc.comp_homeomorph e.toHomeomorph
  have heq : w ∘ J = u := by funext x; exact congrArg u (e.apply_symm_apply x)
  have hLap (x : KernelSpace n) : kernelLaplacian w x = euclideanEllipticOperator A u (e x) :=
    kernelLaplacian_comp_coefficient_sqrt hu hA x
  have hwp : ∀ x y, |kernelLaplacian w x - kernelLaplacian w y| ≤ (H * a ^ α) * ‖x - y‖ ^ α := by
    intro x y
    rw [hLap, hLap]
    have hd : ‖e x - e y‖ ≤ a * ‖x - y‖ := by
      rw [← map_sub]
      exact (P.le_opNorm (x-y)).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
    have hrp := Real.rpow_le_rpow (norm_nonneg _) hd hα.le
    rw [Real.mul_rpow ha (norm_nonneg _)] at hrp
    exact (hfh (e x) (e y)).trans ((mul_le_mul_of_nonneg_left hrp hH).trans_eq (by ring))
  obtain ⟨hws, hwh⟩ := hp w hw hwc U F (H * a ^ α) hU hF (by positivity)
    (fun x => hub (e x)) (fun x => by rw [hLap]; exact hfb (e x)) hwp
  let T : ℝ := U + F + H
  let T₀ : ℝ := U + F + H * a ^ α
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hT₀ : 0 ≤ T₀ := by dsimp [T₀]; positivity
  have hTle : T₀ ≤ Q * T := by
    dsimp [T₀, Q, T]
    nlinarith [mul_nonneg (Real.rpow_nonneg ha α) hU, mul_nonneg (Real.rpow_nonneg ha α) hF]
  have hbR : b ^ 2 ≤ R := by dsimp [R]; linarith
  have hbS : b ^ α ≤ S := by dsimp [S]; linarith
  have hS1 : 1 ≤ S := by dsimp [S]; linarith [Real.rpow_nonneg hb α]
  have htrans (x : KernelSpace n) : fderiv ℝ (fderiv ℝ u) x =
      (fderiv ℝ (fderiv ℝ w) (J x)).bilinearComp J J := by
    have hh := secondFrechet_comp_linear hw J x
    rwa [heq] at hh
  constructor
  · intro x
    rw [htrans]
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ w) (J x)‖ * ‖J‖ ^ 2 := norm_bilinearComp_same_le _ _
      _ ≤ (Cp * T₀) * b ^ 2 := mul_le_mul (hws (J x)) hJ2 (sq_nonneg _) (by positivity)
      _ ≤ (Cp * (Q * T)) * R := mul_le_mul
        (mul_le_mul_of_nonneg_left hTle hCp.le) hbR (sq_nonneg _) (by positivity)
      _ ≤ (Cp * (Q * T)) * R * S := le_mul_of_one_le_right (by positivity) hS1
      _ = _ := by dsimp [C, T]; ring
  · intro x y
    rw [htrans x, htrans y, ← bilinearComp_sub]
    have hd : ‖J x - J y‖ ≤ b * ‖x - y‖ := by
      rw [← map_sub]
      exact (J.le_opNorm _).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
    have hdp := Real.rpow_le_rpow (norm_nonneg _) hd hα.le
    rw [Real.mul_rpow hb (norm_nonneg _)] at hdp
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ w) (J x) - fderiv ℝ (fderiv ℝ w) (J y)‖ * ‖J‖ ^ 2 :=
        norm_bilinearComp_same_le _ _
      _ ≤ (Cp * T₀ * ‖J x - J y‖ ^ α) * b ^ 2 :=
        mul_le_mul (hwh (J x) (J y)) hJ2 (sq_nonneg _) (by positivity)
      _ ≤ (Cp * (Q * T) * (b ^ α * ‖x - y‖ ^ α)) * R :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hTle hCp.le) hdp
          (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)) hbR (sq_nonneg _) (by positivity)
      _ ≤ (Cp * (Q * T) * (S * ‖x - y‖ ^ α)) * R :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hbS (Real.rpow_nonneg (norm_nonneg _) _)) (by positivity)) hR.le
      _ = _ := by dsimp [C, T]; ring

end GaussianTilt.MomentMapSchauder
