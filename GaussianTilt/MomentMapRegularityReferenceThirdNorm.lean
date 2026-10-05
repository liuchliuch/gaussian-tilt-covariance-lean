import GaussianTilt.MomentMapRegularityReferenceTaylor
import GaussianTilt.MomentMapRegularityReferenceInterior

/-! # Actual third-coordinate tensors control the full derivative norm -/
noncomputable section
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxSize 1000

lemma coordinateThirdDerivative_eq_thirdFrechet {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : ContDiffAt ℝ 3 f x) (i j k : Fin n) :
    coordinateThirdDerivative f x i j k =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x
        (Pi.single k 1) (Pi.single j 1) (Pi.single i 1) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    ((hf.fderiv_right (m:=2) (by norm_num)).fderiv_right (m:=1) (by norm_num)).differentiableAt le_rfl
  have he : (fun y => coordinateHessian f y i j) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (fderiv ℝ f) y (Pi.single j 1) (Pi.single i 1)) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact coordinateHessian_eq_secondFDerivAt (hy.of_le (by norm_num)) i j
  unfold coordinateThirdDerivative
  rw [coordinateDerivative_congr_nhds he]
  unfold coordinateDerivative
  rw [fderiv_clm_apply (hD.clm_apply (differentiableAt_const _)) (differentiableAt_const _),
    fderiv_clm_apply hD (differentiableAt_const _)]
  simp

lemma coordinate_trilinear_expansion
    (B : CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ)
    (v w z : CoordinateSpace n) :
    B v w z = ∑ i, ∑ j, ∑ k, v i*w j*z k * B (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) := by
  have hv : (∑ i, v i • (Pi.single i 1 : CoordinateSpace n)) = v := by ext i; simp [Pi.single_apply]
  have hw : (∑ i, w i • (Pi.single i 1 : CoordinateSpace n)) = w := by ext i; simp [Pi.single_apply]
  have hz : (∑ i, z i • (Pi.single i 1 : CoordinateSpace n)) = z := by ext i; simp [Pi.single_apply]
  calc
    B v w z = ∑ i, v i * B (Pi.single i 1) w z := by
      conv_lhs => rw [← hv]
      simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hwi : B (Pi.single i 1) w z = ∑ j, w j * B (Pi.single i 1) (Pi.single j 1) z := by
        conv_lhs => rw [← hw]
        simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
      rw [hwi,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hzij : B (Pi.single i 1) (Pi.single j 1) z =
          ∑ k, z k * B (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) := by
        conv_lhs => rw [← hz]
        simp only [map_sum,map_smul,smul_eq_mul]
      rw [hzij,Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

lemma coordinate_trilinear_norm_bound
    (B : CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ i j k, |B (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)| ≤ C) :
    ‖B‖ ≤ (n : ℝ)^3*C := by
  apply B.opNorm_le_bound (by positivity)
  intro v
  apply (B v).opNorm_le_bound (by positivity)
  intro w
  apply (B v w).opNorm_le_bound (by positivity)
  intro z
  rw [Real.norm_eq_abs,coordinate_trilinear_expansion]
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, |v i*w j*z k*B (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _))))
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ∑ _k : Fin n, ‖v‖*‖w‖*‖z‖*C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      simp only [abs_mul]
      exact mul_le_mul (mul_le_mul (mul_le_mul
        (by simpa using norm_le_pi_norm v i) (by simpa using norm_le_pi_norm w j)
        (abs_nonneg _) (norm_nonneg _)) (by simpa using norm_le_pi_norm z k)
        (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        (hB i j k) (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

/-- Literal third coordinate bounds imply a full Fréchet-operator bound,
with an explicit dimension factor and no norm-equivalence premise. -/
lemma thirdFrechet_norm_le_coordinate_bound {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : ContDiffAt ℝ 3 f x) {C : ℝ} (hC : 0 ≤ C)
    (hthird : ∀ i j k, |coordinateThirdDerivative f x i j k| ≤ C) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ ≤ (n : ℝ)^3*C := by
  apply coordinate_trilinear_norm_bound _ hC
  intro i j k
  simpa only [coordinateThirdDerivative_eq_thirdFrechet hf] using hthird k j i

end GaussianTilt.MomentMapRegularity
