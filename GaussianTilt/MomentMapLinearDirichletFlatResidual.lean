import GaussianTilt.MomentMapLinearDirichletFlatData

/-!
# Actual admissible polynomial residuals on a flat half-ball

The harmonic polynomial is subtracted only through an explicitly
constructed compact upper-half-space cutoff. This preserves actual L²
membership and the zero lower extension, while agreeing exactly with the
polynomial throughout the test domain. Its weak Laplacian is therefore
zero there, and the residual remains in the literal normalized problem.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def flatResidualBump (n : ℕ) : ContDiffBump (0 : KernelSpace n) :=
  ⟨2, 3, by norm_num, by norm_num⟩

def flatPolynomialCutoff (j : Fin n) (P : KernelSpace n → ℝ) : KernelSpace n → ℝ :=
  {x | 0 < x j}.indicator (fun x => flatResidualBump n x * P x)

def flatResidual (j : Fin n) (u P : KernelSpace n → ℝ) (x : KernelSpace n) : ℝ :=
  u x - flatPolynomialCutoff j P x

lemma flatPolynomialCutoff_memLp (j : Fin n) {P : KernelSpace n → ℝ} (hP : Continuous P) :
    MemLp (flatPolynomialCutoff j P) 2 volume := by
  have hm : MemLp (fun x => flatResidualBump n x * P x) 2 (volume : Measure (KernelSpace n)) :=
    ((flatResidualBump n).continuous.mul hP).memLp_of_hasCompactSupport (flatResidualBump n).hasCompactSupport.mul_right
  exact hm.indicator (isOpen_lt continuous_const (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous).measurableSet

lemma flatPolynomialCutoff_zero_lower (j : Fin n) (P : KernelSpace n → ℝ) {x : KernelSpace n}
    (hx : x j ≤ 0) : flatPolynomialCutoff j P x = 0 := by
  unfold flatPolynomialCutoff
  exact indicator_of_notMem (show x ∉ {y : KernelSpace n | 0 < y j} from not_lt.mpr hx) _

lemma flatPolynomialCutoff_eq (j : Fin n) (P : KernelSpace n → ℝ) {x : KernelSpace n}
    (hx : x ∈ flatUpperBall j 2) : flatPolynomialCutoff j P x = P x := by
  rw [flatPolynomialCutoff, indicator_of_mem hx.2,
    (flatResidualBump n).one_of_mem_closedBall (Metric.ball_subset_closedBall hx.1), one_mul]

lemma flatPolynomialCutoff_continuousOn (j : Fin n) {P : KernelSpace n → ℝ} (hP : Continuous P) :
    ContinuousOn (flatPolynomialCutoff j P) (flatUpperBall j 2) :=
  hP.continuousOn.congr (fun _ hx => flatPolynomialCutoff_eq j P hx)

lemma integral_harmonic_mul_kernelLaplacian {P ψ : KernelSpace n → ℝ}
    (hP : ContDiff ℝ 2 P) (hPlap : ∀ x, kernelLaplacian P x = 0)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, P x * kernelLaplacian ψ x) = 0 := by
  have hh := integral_mul_kernelLaplacian_swap hψ hP hψc
  have he : (∫ x, P x * kernelLaplacian ψ x) = ∫ x, kernelLaplacian ψ x * P x := by
    apply integral_congr_ae; exact ae_of_all _ (fun x => mul_comm _ _)
  rw [he, ← hh]
  simp only [hPlap, mul_zero, integral_zero]

/-- The concrete cutoff residual is an actual weak solution with the
same forcing, and retains a genuine finite boundary height bound. -/
theorem FlatWeakPoisson.subtractHarmonic {j : Fin n} {u f P : KernelSpace n → ℝ}
    (h : FlatWeakPoisson j u f) (hP : ContDiff ℝ ∞ P)
    (hP0 : ∀ x, x j = 0 → P x = 0) (hPlap : ∀ x, kernelLaplacian P x = 0) :
    FlatWeakPoisson j (flatResidual j u P) f := by
  have hpLp := flatPolynomialCutoff_memLp j hP.continuous
  refine ⟨h.memLp.sub hpLp, ?_, h.continuous.sub (flatPolynomialCutoff_continuousOn j hP.continuous), ?_, ?_⟩
  · intro x hx
    simp only [flatResidual, h.zero_lower x hx, flatPolynomialCutoff_zero_lower j P hx, sub_self]
  · obtain ⟨C, hC, hg⟩ := h.growth
    have hψ : ContDiff ℝ ∞ (fun x => flatResidualBump n x * P x) := (flatResidualBump n).contDiff.mul hP
    have hψc : HasCompactSupport (fun x => flatResidualBump n x * P x) := (flatResidualBump n).hasCompactSupport.mul_right
    obtain ⟨D, M, hD, _, hψg, _, _⟩ := exists_flat_test_bounds j hψ hψc (fun x hx => by rw [hP0 x hx, mul_zero])
    refine ⟨C+D, add_nonneg hC hD, ?_⟩
    intro x hx
    have hcut : |flatPolynomialCutoff j P x| ≤ D*|x j| := by
      by_cases hj : 0 < x j
      · rw [flatPolynomialCutoff, indicator_of_mem (show x ∈ {y : KernelSpace n | 0 < y j} from hj)]
        exact hψg x
      · rw [flatPolynomialCutoff, indicator_of_notMem (show x ∉ {y : KernelSpace n | 0 < y j} from hj), abs_zero]
        positivity
    exact (abs_sub _ _).trans ((add_le_add (hg x hx) hcut).trans_eq (by ring))
  · intro ψ hψ hψc hψs
    have huI := integrable_locally_mul_laplacian (h.memLp.locallyIntegrable (by norm_num)) (contDiff_infty.mp hψ 2) hψc
    have hpI := integrable_locally_mul_laplacian (hpLp.locallyIntegrable (by norm_num)) (contDiff_infty.mp hψ 2) hψc
    have hpcut : (∫ x, flatPolynomialCutoff j P x * kernelLaplacian ψ x) = 0 := by
      rw [← integral_harmonic_mul_kernelLaplacian (contDiff_infty.mp hP 2) hPlap (contDiff_infty.mp hψ 2) hψc]
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        dsimp only
        by_cases hx : x ∈ tsupport ψ
        · rw [flatPolynomialCutoff_eq j P (hψs hx)]
        · rw [kernelLaplacian_zero_off_tsupport ψ hx, mul_zero, mul_zero])
    simp only [flatResidual, sub_mul]
    rw [integral_sub huI hpI, hpcut, sub_zero]
    exact h.equation ψ hψ hψc hψs

lemma flatResidual_eq (j : Fin n) (u P : KernelSpace n → ℝ) {x : KernelSpace n}
    (hx : x ∈ flatUpperBall j 2) : flatResidual j u P x = u x - P x := by
  rw [flatResidual, flatPolynomialCutoff_eq j P hx]

lemma flatResidual_bound {j : Fin n} {u P : KernelSpace n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hu0 : ∀ x, x j ≤ 0 → u x = 0)
    (hError : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, 0 ≤ x j → |u x-P x| ≤ B) :
    ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |flatResidual j u P x| ≤ B := by
  intro x hx
  by_cases hj : 0 < x j
  · rw [flatResidual_eq j u P ⟨hx,hj⟩]
    exact hError x hx hj.le
  · simp only [flatResidual, hu0 x (le_of_not_gt hj), flatPolynomialCutoff_zero_lower j P (le_of_not_gt hj), sub_self, abs_zero]
    exact hB

end GaussianTilt.MomentMapLinearDirichlet
