import GaussianTilt.MomentMapSchauderKernelCriteria
import GaussianTilt.MomentMapEllipticFundamentalSolutionCutoff

/-!
# The actual cutoff Newtonian Hessian is Hölder bounded

A fixed genuine C∞ radial bump supplies the compact cutoff. Its weighted
first derivative is bounded by compactness. Every hypothesis of the proved
singular-integral estimate is then discharged for the actual Newtonian
Hessian, including in the logarithmic two-dimensional case.
-/
noncomputable section
open MeasureTheory Set Filter Module
open scoped ENNReal Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic

/-- A fixed actual smooth radial cutoff: one on [-1,1], zero outside [-2,2]. -/
def standardRadialCutoff : ℝ → ℝ := (default : ContDiffBump (0 : ℝ))

lemma standardRadialCutoff_contDiff : ContDiff ℝ ∞ standardRadialCutoff :=
  (default : ContDiffBump (0 : ℝ)).contDiff

lemma standardRadialCutoff_abs_le_one (t : ℝ) : |standardRadialCutoff t| ≤ 1 := by
  change |(default : ContDiffBump (0 : ℝ)) t| ≤ 1
  rw [abs_of_nonneg (default : ContDiffBump (0 : ℝ)).nonneg]
  exact (default : ContDiffBump (0 : ℝ)).le_one

lemma standardRadialCutoff_zero {t : ℝ} (ht : 2 < t) : standardRadialCutoff t = 0 := by
  apply (default : ContDiffBump (0 : ℝ)).zero_of_le_dist
  change (2 : ℝ) ≤ dist t 0
  rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < t)]
  exact ht.le

lemma exists_standardRadialCutoff_deriv_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t → t * |deriv standardRadialCutoff t| ≤ B := by
  have hc : Continuous (fun t : ℝ => t * deriv standardRadialCutoff t) :=
    continuous_id.mul ((contDiff_infty.mp standardRadialCutoff_contDiff 1).continuous_deriv le_rfl)
  have hs : HasCompactSupport (fun t : ℝ => t * deriv standardRadialCutoff t) :=
    (default : ContDiffBump (0 : ℝ)).hasCompactSupport.deriv.mul_left
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous hc
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro t ht
  have hb := hB t
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos ht] at hb
  exact hb.trans (le_max_left _ _)

/-- The actual compensated local Newtonian Hessian operator. -/
def standardNewtonianSingularIntegral {n : ℕ} (f : KernelSpace n → ℝ)
    (i j : Fin n) (x : KernelSpace n) : ℝ :=
  compensatedSingularIntegral volume (cutoffNewtonianHessian standardRadialCutoff i j) f x

/-- A dimension/exponent-only bound for the actual Newtonian Hessian
singular integral. No kernel condition, cancellation identity, integrability
claim, or singular-integral theorem is left as a hypothesis. -/
theorem exists_standardNewtonianSingularIntegral_holder_bound {n : ℕ} [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : KernelSpace n → ℝ, Measurable f →
      ∀ H : ℝ, 0 ≤ H → (∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) →
      ∀ (i j : Fin n) (x y : KernelSpace n),
        |standardNewtonianSingularIntegral f i j x - standardNewtonianSingularIntegral f i j y| ≤
          C * H * ‖x - y‖ ^ α := by
  obtain ⟨B, hB, hχB⟩ := exists_standardRadialCutoff_deriv_bound
  let M : ℝ := 2 * ((n : ℝ) + 1)
  let D : ℝ := 2 * (n : ℝ) * ((n : ℝ) + 5) + B * (2 * ((n : ℝ) + 1))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C₀ : ℝ := singularHolderConstant (volume : Measure (KernelSpace n)) M
    (D * (2 : ℝ) ^ ((n : ℝ) + 1)) α
  have hC₀ : 0 ≤ C₀ := singularHolderConstant_nonneg hM (by positivity)
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro f hfm H hH hf i j x y
  have hχd : Differentiable ℝ standardRadialCutoff :=
    (contDiff_infty.mp standardRadialCutoff_contDiff 1).differentiable le_rfl
  have hχA : ∀ t : ℝ, 0 ≤ t → |standardRadialCutoff t| ≤ 1 :=
    fun t _ => standardRadialCutoff_abs_le_one t
  have hdim : α < (finrank ℝ (KernelSpace n) : ℝ) := by
    simp only [KernelSpace, finrank_euclideanSpace, Fintype.card_fin]
    exact hα1.trans_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
  have hb := compensatedSingularIntegral_holder_of_kernel_derivative
    (μ := (volume : Measure (KernelSpace n))) (K := cutoffNewtonianHessian standardRadialCutoff i j)
    hM hD hH hα hα1 hdim (R := 2) (by norm_num)
    (measurable_cutoffNewtonianHessian standardRadialCutoff_contDiff.continuous i j) hfm
    (fun z hz => by simpa only [KernelSpace, finrank_euclideanSpace, Fintype.card_fin, one_mul, M] using
      cutoffNewtonianHessian_bound (A := 1) (by norm_num) hχA hz i j)
    (fun z hz => differentiableAt_cutoffNewtonianHessian hχd hz i j)
    (fun z hz => by simpa only [KernelSpace, finrank_euclideanSpace, Fintype.card_fin, one_mul, D] using
      norm_fderiv_cutoffNewtonianHessian_le hχd (A := 1) (by norm_num) hB hχA hχB hz i j)
    (cutoffNewtonianHessian_support (fun _ ht => standardRadialCutoff_zero ht) i j)
    (fun r hr => cutoffNewtonianHessian_closedBall_tail_zero standardRadialCutoff_contDiff.continuous
      (fun _ ht => standardRadialCutoff_zero ht) hr i j) hf x y
  change |standardNewtonianSingularIntegral f i j x - standardNewtonianSingularIntegral f i j y| ≤ _ at hb
  simp only [KernelSpace, finrank_euclideanSpace, Fintype.card_fin] at hb
  change _ ≤ C₀ * H * ‖x - y‖ ^ α at hb
  apply hb.trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hH)
    (Real.rpow_nonneg (norm_nonneg _) _)

end GaussianTilt.MomentMapSchauder
