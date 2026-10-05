import GaussianTilt.MomentMapSchauderBoundaryVariableAbsorption
import GaussianTilt.MomentMapSchauderScaledCoefficients

/-! # Actual small-radius boundary normalization of Hölder coefficients -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 1400000
open Set Matrix
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

lemma smul_mem_flatClosedPatch {j : Fin n} {r R : ℝ} (hr : 0 ≤ r)
    {x : KernelSpace n} (hx : x ∈ flatClosedPatch j R) : r • x ∈ flatClosedPatch j (r*R) := by
  constructor
  · rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left (flat_patch_norm hx) hr
  · change 0 ≤ r*x j
    exact mul_nonneg hr hx.2

/-- The normalized oscillation and normalized Hölder seminorm both become
small on a constructed positive radius. They are derived from the actual
identity value at the flat center and the original coefficient modulus. -/
theorem exists_normalized_boundary_coefficient_radius {α K R ε : ℝ}
    (hα : 0 < α) (hK : 0 ≤ K) (hR : 0 < R) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ 4*r ≤ R ∧ ∀ (j : Fin n)
      (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ), A 0=1 →
      (∀ x ∈ flatClosedPatch j R, ∀ y ∈ flatClosedPatch j R, ∀ i k,
        |A x i k-A y i k| ≤ K*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j 2, ∀ i k, |(1 : Matrix (Fin n) (Fin n) ℝ) i k-A (r • x) i k| ≤ ε) ∧
      (∀ x ∈ flatClosedPatch j 2, ∀ y ∈ flatClosedPatch j 2, ∀ i k,
        |A (r • x) i k-A (r • y) i k| ≤ ε*‖x-y‖^α) := by
  obtain ⟨r,hr,hrR,hsmall⟩ := exists_small_holder_radius hα hK hR hε
  refine ⟨r,hr,hrR,?_⟩
  intro j A hA0 hAH
  have hmap : ∀ x ∈ flatClosedPatch j 2, r • x ∈ flatClosedPatch j R := by
    intro x hx
    have hh := smul_mem_flatClosedPatch hr.le hx
    exact ⟨Metric.closedBall_subset_closedBall (by linarith) hh.1,hh.2⟩
  have h0 : (0 : KernelSpace n) ∈ flatClosedPatch j R := ⟨Metric.mem_closedBall_self hR.le,by simp⟩
  have hKr : K*r^α ≤ ε := (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hr.le (by linarith : r ≤ 4*r) hα.le) hK).trans hsmall
  constructor
  · intro x hx i k
    have hh := hAH 0 h0 (r • x) (hmap x hx) i k
    rw [hA0,zero_sub,norm_neg] at hh
    have hn : ‖r • x‖ ≤ 4*r := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      have hx' := flat_patch_norm hx
      nlinarith
    exact hh.trans ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hn hα.le) hK).trans hsmall)
  · intro x hx y hy i k
    have hh := hAH (r • x) (hmap x hx) (r • y) (hmap y hy) i k
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hr,Real.mul_rpow hr.le (norm_nonneg _)] at hh
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hKr (Real.rpow_nonneg (norm_nonneg (x-y)) α)])

/-- Exact scalar dilation of a closure Hessian preserves the literal
nondivergence PDE with the expected quadratic factor. -/
lemma boundary_matrixContraction_rescale (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ)
    (r : ℝ) (x : KernelSpace n) :
    matrixContraction (A (r • x)) (bilinearEntryMatrix (r^2 • B (r • x)))=
      r^2*matrixContraction (A (r • x)) (bilinearEntryMatrix (B (r • x))) := by
  simp only [matrixContraction,bilinearEntryMatrix,ContinuousLinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

end GaussianTilt.MomentMapSchauder
