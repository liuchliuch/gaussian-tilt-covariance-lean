import GaussianTilt.MomentMapSchauderNewtonianOperator
import GaussianTilt.MomentMapSchauderSmoothTail

/-!
# The actual complementary Newtonian Hessian convolution

The singularity is removed by the same constructed radial cutoff used in
the local singular integral. Its complement is differentiable everywhere,
with a global derivative bound and an integrable derivative tail. Thus its
convolution with bounded compactly supported data is locally Lipschitz,
with a dimension-only constant and no support-radius dependence.
-/
noncomputable section
open MeasureTheory Set Filter Module
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def standardNewtonianTail (i j : Fin n) : KernelSpace n → ℝ :=
  cutoffNewtonianHessian (fun t => 1 - standardRadialCutoff t) i j

lemma standardNewtonianTail_eq_zero {x : KernelSpace n} (hx : ‖x‖ ≤ 1) (i j : Fin n) :
    standardNewtonianTail i j x = 0 := by
  have hc : standardRadialCutoff ‖x‖ = 1 := by
    apply (default : ContDiffBump (0 : ℝ)).one_of_mem_closedBall
    change dist ‖x‖ 0 ≤ 1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg x)]
    exact hx
  simp only [standardNewtonianTail, cutoffNewtonianHessian, hc, sub_self, zero_mul]

lemma standardNewtonianTail_eventually_zero {x : KernelSpace n} (hx : ‖x‖ < 1) (i j : Fin n) :
    standardNewtonianTail i j =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
  have hxball : x ∈ Metric.ball (0 : KernelSpace n) 1 := by simpa using hx
  filter_upwards [Metric.isOpen_ball.mem_nhds hxball] with z hz
  apply standardNewtonianTail_eq_zero (i := i) (j := j)
  exact (show ‖z‖ < 1 by simpa using hz).le

lemma differentiable_standardNewtonianTail (i j : Fin n) :
    Differentiable ℝ (standardNewtonianTail i j) := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq
      (standardNewtonianTail_eventually_zero (by simp) i j)
  · apply differentiableAt_cutoffNewtonianHessian _ hx i j
    exact (differentiable_const (1 : ℝ)).sub
      ((contDiff_infty.mp standardRadialCutoff_contDiff 1).differentiable le_rfl)

/-- Both the global derivative bound and true far-field derivative decay
are derived for the actual complementary Newtonian Hessian kernel. -/
theorem exists_standardNewtonianTail_derivative_bounds [NeZero n] :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ i j : Fin n,
      (∀ x : KernelSpace n, ‖fderiv ℝ (standardNewtonianTail i j) x‖ ≤ D) ∧
      (∀ x : KernelSpace n, x ≠ 0 → ‖fderiv ℝ (standardNewtonianTail i j) x‖ ≤
        D * ‖x‖ ^ (-(n : ℝ) - 1)) := by
  obtain ⟨B, hB, hχB⟩ := exists_standardRadialCutoff_deriv_bound
  let D : ℝ := 2 * (n : ℝ) * ((n : ℝ) + 5) + B * (2 * ((n : ℝ) + 1))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hdχ : Differentiable ℝ (fun t : ℝ => 1 - standardRadialCutoff t) :=
    (differentiable_const (1 : ℝ)).sub
      ((contDiff_infty.mp standardRadialCutoff_contDiff 1).differentiable le_rfl)
  have hχA : ∀ t : ℝ, 0 ≤ t → |1 - standardRadialCutoff t| ≤ 1 := by
    intro t _
    have hn : 0 ≤ standardRadialCutoff t := (default : ContDiffBump (0 : ℝ)).nonneg
    have hl : standardRadialCutoff t ≤ 1 := (default : ContDiffBump (0 : ℝ)).le_one
    rw [abs_of_nonneg (sub_nonneg.mpr hl)]
    linarith
  have hχB' : ∀ t : ℝ, 0 < t → t * |deriv (fun s => 1 - standardRadialCutoff s) t| ≤ B := by
    intro t ht
    simpa only [deriv_const_sub, abs_neg] using hχB t ht
  have hdecay (i j : Fin n) (x : KernelSpace n) (hx : x ≠ 0) :
      ‖fderiv ℝ (standardNewtonianTail i j) x‖ ≤ D * ‖x‖ ^ (-(n : ℝ) - 1) := by
    simpa only [standardNewtonianTail, D, one_mul] using
      norm_fderiv_cutoffNewtonianHessian_le hdχ (A := 1) (by norm_num) hB hχA hχB' hx i j
  refine ⟨D, hD, fun i j => ⟨?_, hdecay i j⟩⟩
  intro x
  by_cases hx : ‖x‖ < 1
  · rw [(standardNewtonianTail_eventually_zero hx i j).fderiv_eq]
    simpa using hD
  · have hn : 1 ≤ ‖x‖ := le_of_not_gt hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hn)
    have hp : ‖x‖ ^ (-(n : ℝ) - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
    exact (hdecay i j x hx0).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hD)

/-- The genuine smooth tail has a dimension-only local Lipschitz convolution
bound for bounded continuous compact data, regardless of its support radius. -/
theorem exists_standardNewtonianTail_convolution_lipschitz [NeZero n] :
    ∃ C : ℝ, 0 < C ∧ ∀ f : KernelSpace n → ℝ, Continuous f → HasCompactSupport f →
      ∀ F : ℝ, 0 ≤ F → (∀ z, |f z| ≤ F) → ∀ (i j : Fin n) (x y : KernelSpace n),
        ‖x - y‖ ≤ 1 →
        |scalarKernelConvolution volume (standardNewtonianTail i j) f x -
          scalarKernelConvolution volume (standardNewtonianTail i j) f y| ≤ C * F * ‖x - y‖ := by
  obtain ⟨D, hD, hbounds⟩ := exists_standardNewtonianTail_derivative_bounds (n := n)
  let L : ℝ := D * (2 : ℝ) ^ ((n : ℝ) + 1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let C₀ : ℝ := smoothTailLipschitzConstant (volume : Measure (KernelSpace n)) D L
  have hC₀ : 0 ≤ C₀ := smoothTailLipschitzConstant_nonneg hD hL
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro f hfc hfs F hF hf i j x y hxy
  have hcomp : ∀ x : KernelSpace n,
      Integrable (fun z => standardNewtonianTail i j (x - z) * f z) := by
    intro x
    exact (((differentiable_standardNewtonianTail i j).continuous.comp
      (continuous_const.sub continuous_id)).mul hfc).integrable_of_hasCompactSupport hfs.mul_left
  have hdiff : ∀ a b : KernelSpace n, a ≠ 0 → ‖a - b‖ ≤ ‖a‖ / 2 →
      |standardNewtonianTail i j a - standardNewtonianTail i j b| ≤
        L * ‖a - b‖ * ‖a‖ ^ (-(finrank ℝ (KernelSpace n) : ℝ) - 1) := by
    intro a b ha hab
    simpa only [KernelSpace, finrank_euclideanSpace, Fintype.card_fin, L] using
      kernel_difference_of_derivative_decay hD
        (fun z _ => differentiable_standardNewtonianTail i j z)
        (by simpa only [KernelSpace, finrank_euclideanSpace, Fintype.card_fin] using (hbounds i j).2) a b ha hab
  have hb := scalarKernelConvolution_local_lipschitz hD hL hF
    (kernel_global_lipschitz_of_deriv_bound (differentiable_standardNewtonianTail i j) (hbounds i j).1)
    hdiff hf hcomp x y hxy
  apply hb.trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hF) (norm_nonneg _)

end GaussianTilt.MomentMapSchauder
