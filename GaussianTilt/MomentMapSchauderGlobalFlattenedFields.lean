import GaussianTilt.MomentMapSchauderGlobalBoundaryChart
import GaussianTilt.MomentMapSchauderGlobalCoefficientBounds
import GaussianTilt.MomentMapLinearDirichletFlatteningOperator

/-! # Actual principal and curvature-drift fields in the fixed smooth chart -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2400000
open Set Matrix
open scoped ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.HolderSpace
variable {n : ℕ}

def scaledChartJacobian (w : KernelSpace n → ℝ) (a : KernelSpace n) (j : Fin n) (s : ℝ)
    (ψ : KernelSpace n → KernelSpace n) (z : KernelSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  euclideanCLMMatrix (fderiv ℝ (scaledFlatteningMap w a j s) (ψ z))

def scaledChartCurvature (w : KernelSpace n → ℝ) (s : ℝ) (ψ : KernelSpace n → KernelSpace n)
    (z : KernelSpace n) : Matrix (Fin n) (Fin n) ℝ := s⁻¹ • euclideanHessianMatrix w (ψ z)

def flattenedPrincipal (w : KernelSpace n → ℝ) (a : KernelSpace n) (j : Fin n) (s : ℝ)
    (ψ : KernelSpace n → KernelSpace n) (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (z : KernelSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  scaledChartJacobian w a j s ψ z*A (ψ z)*(scaledChartJacobian w a j s ψ z)ᵀ

def flattenedDrift (w : KernelSpace n → ℝ) (j : Fin n) (s : ℝ)
    (ψ : KernelSpace n → KernelSpace n) (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (z : KernelSpace n) : KernelSpace n :=
  (-matrixContraction (A (ψ z)) (scaledChartCurvature w s ψ z)) • EuclideanSpace.basisFun (Fin n) ℝ j

lemma contDiff_scaledChartJacobian_entry {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n) (s : ℝ) {ψ : KernelSpace n → KernelSpace n}
    (hψ : ContDiff ℝ ∞ ψ) (i k : Fin n) :
    ContDiff ℝ ∞ (fun z => scaledChartJacobian w a j s ψ z i k) := by
  have hh := ((contDiff_scaledFlatteningMap hw a j s).fderiv_right (m := ∞) (by simp)).comp hψ
  have hp := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).contDiff.comp (hh.clm_apply (contDiff_const (c := EuclideanSpace.basisFun (Fin n) ℝ k)))
  simpa only [scaledChartJacobian,euclideanCLMMatrix_entry] using hp

lemma contDiff_scaledChartCurvature_entry {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (s : ℝ) {ψ : KernelSpace n → KernelSpace n} (hψ : ContDiff ℝ ∞ ψ) (i k : Fin n) :
    ContDiff ℝ ∞ (fun z => scaledChartCurvature w s ψ z i k) := by
  have hh := (((hw.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).comp hψ).clm_apply (contDiff_const (c := EuclideanSpace.basisFun (Fin n) ℝ i)) |>.clm_apply (contDiff_const (c := EuclideanSpace.basisFun (Fin n) ℝ k))
  exact contDiff_const.mul hh

lemma scaledChartJacobian_eq {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n) (s : ℝ) (ψ : KernelSpace n → KernelSpace n) (z : KernelSpace n) :
    scaledChartJacobian w a j s ψ z=s⁻¹ • flatteningJacobian w j (ψ z) := by
  ext i k
  rw [scaledChartJacobian,euclideanCLMMatrix_entry]
  have he : fderiv ℝ (scaledFlatteningMap w a j s) (ψ z)=s⁻¹ • fderiv ℝ (flatteningMap w a j) (ψ z) :=
    fderiv_const_smul ((contDiff_flatteningMap hw a j).differentiable (by simp) (ψ z)) s⁻¹
  rw [he,(hasFDerivAt_flatteningMap (hw.differentiable (by simp) (ψ z)) a j).fderiv]
  simp only [Matrix.smul_apply,smul_eq_mul,flatteningJacobian,euclideanCLMMatrix_entry,
    ContinuousLinearMap.smul_apply,PiLp.smul_apply]

lemma flattenedPrincipal_eq {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n) (s : ℝ) (ψ : KernelSpace n → KernelSpace n)
    (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ) (z : KernelSpace n) :
    flattenedPrincipal w a j s ψ A z=(s⁻¹)^2 • flatteningCoefficient (A (ψ z)) w j (ψ z) := by
  rw [flattenedPrincipal,scaledChartJacobian_eq hw,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul]
  simp only [flatteningCoefficient,pow_two]

lemma flattenedPrincipal_posDef_at_zero {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n) {s : ℝ} (hs : 0 < s) (ψ : KernelSpace n → KernelSpace n)
    (hψ0 : ψ 0=a) (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hA : (A a).PosDef) (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0) :
    (flattenedPrincipal w a j s ψ A 0).PosDef := by
  rw [flattenedPrincipal_eq hw,hψ0]
  exact (flatteningCoefficient_posDef hA w j a hj).smul (sq_pos_of_pos (inv_pos.mpr hs))

/-- All flattened coefficient and drift bounds are chosen before the
unknown coefficient member or test jet, using fixed smooth chart bounds. -/
theorem exists_uniform_flattened_field_bounds {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n) (s : ℝ) {ψ : KernelSpace n → KernelSpace n} (hψ : ContDiff ℝ ∞ ψ)
    {S T : Set (KernelSpace n)} (hmap : MapsTo ψ T S) (hT : IsCompact T) (hTc : Convex ℝ T)
    {α M K : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hM : 0 ≤ M) (hK : 0 ≤ K) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ,
      (∀ x ∈ S, ∀ i k, |A x i k| ≤ M) →
      (∀ x ∈ S, ∀ y ∈ S, ∀ i k, |A x i k-A y i k| ≤ K*‖x-y‖^α) →
      (∀ z ∈ T, ∀ i k, |flattenedPrincipal w a j s ψ A z i k| ≤ C) ∧
      (∀ z ∈ T, ∀ y ∈ T, ∀ i k, |flattenedPrincipal w a j s ψ A z i k-flattenedPrincipal w a j s ψ A y i k| ≤ C*‖z-y‖^α) ∧
      (∀ z ∈ T, ‖flattenedDrift w j s ψ A z‖ ≤ L) ∧
      (∀ z ∈ T, ∀ y ∈ T, ‖flattenedDrift w j s ψ A z-flattenedDrift w j s ψ A y‖ ≤ L*‖z-y‖^α) := by
  obtain ⟨P,hP1,hP⟩ := exists_smoothChartBounds hT hTc hα hα1 ψ hψ
  let K' := K*P^α
  have hK' : 0 ≤ K' := by dsimp [K']; positivity
  obtain ⟨B,hB1,hBb,hBH⟩ := exists_smooth_matrix_entry_holder_bound hT hTc hα hα1
    (scaledChartJacobian w a j s ψ) (fun i k => contDiff_infty.mp (contDiff_scaledChartJacobian_entry hw a j s hψ i k) 1)
  obtain ⟨E,hE1,hEb,hEH⟩ := exists_smooth_matrix_entry_holder_bound hT hTc hα hα1
    (scaledChartCurvature w s ψ) (fun i k => contDiff_infty.mp (contDiff_scaledChartCurvature_entry hw s hψ i k) 1)
  have hB : 0 ≤ B := by linarith
  have hE : 0 ≤ E := by linarith
  let C := (n:ℝ)^2*B^2*M+(n:ℝ)^2*B^2*(K'+2*M)+1
  let L := (n:ℝ)^2*M*E+(n:ℝ)^2*(M*E+K'*E)+1
  refine ⟨C,L,by dsimp [C]; positivity,by dsimp [L]; positivity,?_⟩
  intro A hAb hAH
  have hAb' : ∀ x ∈ T, ∀ i k, |A (ψ x) i k| ≤ M := fun x hx => hAb _ (hmap hx)
  have hAH' : ∀ x ∈ T, ∀ y ∈ T, ∀ i k, |A (ψ x) i k-A (ψ y) i k| ≤ K'*‖x-y‖^α := by
    intro x hx y hy i k
    have hh := (hAH _ (hmap hx) _ (hmap hy) i k).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) (hP.lipschitz x hx y hy) hα) hK)
    rw [Real.mul_rpow hP.nonneg (norm_nonneg _)] at hh
    exact hh.trans_eq (by dsimp [K']; ring)
  obtain ⟨hPb,hPH⟩ := matrix_sandwich_holder_bounds hB hM hK' hBb hBH hAb' hAH'
  obtain ⟨hcb,hcH⟩ := matrixContraction_holder_bounds_on hM hK' hE hAb' hAH' hEb hEH
  have hPC : (n:ℝ)^2*B^2*M ≤ C := by
    dsimp [C]
    have hh : 0 ≤ (n:ℝ)^2*B^2*(K'+2*M) := by positivity
    linarith
  have hPHC : (n:ℝ)^2*B^2*(K'+2*M) ≤ C := by
    dsimp [C]
    have hh : 0 ≤ (n:ℝ)^2*B^2*M := by positivity
    linarith
  have hcL : (n:ℝ)^2*M*E ≤ L := by
    dsimp [L]
    have hh : 0 ≤ (n:ℝ)^2*(M*E+K'*E) := by positivity
    linarith
  have hcHL : (n:ℝ)^2*(M*E+K'*E) ≤ L := by
    dsimp [L]
    have hh : 0 ≤ (n:ℝ)^2*M*E := by positivity
    linarith
  refine ⟨fun x hx i k => (hPb x hx i k).trans hPC,
    fun x hx y hy i k => (hPH x hx y hy i k).trans (mul_le_mul_of_nonneg_right hPHC (Real.rpow_nonneg (norm_nonneg _) α)),?_,?_⟩
  · intro x hx
    rw [flattenedDrift,norm_smul,Real.norm_eq_abs,abs_neg,(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one]
    exact (hcb x hx).trans hcL
  · intro x hx y hy
    rw [flattenedDrift,flattenedDrift,← sub_smul,norm_smul,Real.norm_eq_abs,
      (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one,neg_sub_neg,abs_sub_comm]
    exact (hcH x hx y hy).trans (mul_le_mul_of_nonneg_right hcHL (Real.rpow_nonneg (norm_nonneg _) α))

end GaussianTilt.MomentMapSchauder
