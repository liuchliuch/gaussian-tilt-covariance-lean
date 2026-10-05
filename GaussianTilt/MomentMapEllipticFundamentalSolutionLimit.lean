import GaussianTilt.MomentMapEllipticFundamentalSolutionGreen
import GaussianTilt.MomentMapSchauderRadialIntegrals

/-!
# The actual distributional fundamental-solution identity

Local integrability of the power and logarithmic singularities is proved by
the radial-integral lane. Dominated convergence identifies the regularized
Green limit with the literal singular-kernel integral. Thus the delta source
and its normalization are conclusions, rather than premises.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- The literal singular Newtonian kernel, with its logarithmic n=2 case. -/
def newtonianKernel (n : ℕ) (x : KernelSpace n) : ℝ := regularizedNewtonian n 0 x

set_option maxHeartbeats 1000000 in
lemma integrableOn_newtonianKernel_closedBall (n : ℕ) (R : ℝ) :
    IntegrableOn (newtonianKernel n) (Metric.closedBall 0 R) := by
  by_cases hn : n = 2
  · subst n
    have hi := GaussianTilt.MomentMapSchauder.integrableOn_log_norm_sq_closedBall
      (μ := (volume : Measure (KernelSpace 2))) (by simp [KernelSpace]) R
    have he : newtonianKernel 2 = fun x : KernelSpace 2 => Real.log (‖x‖ ^ 2) := by
      funext x
      simp [newtonianKernel, regularizedNewtonian, newtonianProfile]
    rw [he]
    exact hi
  · by_cases hlarge : 2 < n
    · have hk : 0 < (n : ℝ) - 2 := by
        have hnreal : (2 : ℝ) < (n : ℝ) := by exact_mod_cast hlarge
        linarith
      have hkn : (n : ℝ) - 2 < Module.finrank ℝ (KernelSpace n) := by simp [KernelSpace]
      have hi := GaussianTilt.MomentMapSchauder.integrableOn_norm_neg_rpow_closedBall
        (μ := (volume : Measure (KernelSpace n))) hk hkn R
      have he : newtonianKernel n = fun x : KernelSpace n =>
          ‖x‖ ^ (-((n : ℝ) - 2)) / ((2 - (n : ℝ)) / 2) := by
        funext x
        simp only [newtonianKernel, regularizedNewtonian, newtonianProfile, if_neg hn, zero_add,
          squaredNorm_rpow]
        congr 2
        ring
      rw [he]
      exact hi.div_const _
    · have hsmall : n ≤ 1 := by omega
      have hb : 0 ≤ (2 - (n : ℝ)) / 2 := by
        have hnreal : (n : ℝ) ≤ 1 := by exact_mod_cast hsmall
        linarith
      have hh : Continuous (newtonianKernel n) := by
        change Continuous (fun x : KernelSpace n => newtonianProfile n (0 + ‖x‖ ^ 2))
        simp only [newtonianProfile, if_neg hn, zero_add]
        exact ((continuous_norm.pow 2).rpow_const (fun _ => Or.inr hb)).div_const _
      exact hh.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)

lemma locallyIntegrable_newtonianKernel (n : ℕ) : LocallyIntegrable (newtonianKernel n) := by
  intro x
  refine ⟨Metric.closedBall 0 (‖x‖ + 1), ?_, integrableOn_newtonianKernel_closedBall n _⟩
  apply Metric.closedBall_mem_nhds_of_mem
  simpa only [Metric.mem_ball, dist_zero_right] using (lt_add_one ‖x‖)

lemma strictMonoOn_newtonianProfile (n : ℕ) : StrictMonoOn (newtonianProfile n) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun t ht => (hasDerivAt_newtonianProfile n ht).continuousAt.continuousWithinAt)
  intro t ht
  rw [interior_Ioi] at ht
  rw [(hasDerivAt_newtonianProfile n ht).deriv]
  exact Real.rpow_pos_of_pos ht _

/-- Monotonicity of the true scalar profile gives a common integrable
dominator for all positive regularization parameters at most one. -/
lemma regularizedNewtonian_abs_bound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {x : KernelSpace n} (hx : x ≠ 0) :
    |regularizedNewtonian n a x| ≤ |newtonianKernel n x| + |regularizedNewtonian n 1 x| := by
  have hS : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hm := (strictMonoOn_newtonianProfile n).monotoneOn
  have hlo : newtonianKernel n x ≤ regularizedNewtonian n a x := by
    change newtonianProfile n (0 + ‖x‖ ^ 2) ≤ newtonianProfile n (a + ‖x‖ ^ 2)
    exact hm (by simpa using hS) (mem_Ioi.mpr (by positivity)) (by linarith)
  have hhi : regularizedNewtonian n a x ≤ regularizedNewtonian n 1 x :=
    hm (mem_Ioi.mpr (by positivity)) (mem_Ioi.mpr (by positivity)) (by linarith)
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (newtonianKernel n x), abs_nonneg (regularizedNewtonian n 1 x)]
  · linarith [le_abs_self (regularizedNewtonian n 1 x), abs_nonneg (newtonianKernel n x)]

lemma tendsto_inv_sq_atTop : Tendsto (fun c : ℝ => (c ^ 2)⁻¹) atTop (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (max 1 b)] with c hc
  have h1 : 1 ≤ c := (le_max_left _ _).trans hc
  have hb : b ≤ c := (le_max_right _ _).trans hc
  nlinarith

lemma tendsto_regularizedNewtonian {x : KernelSpace n} (hx : x ≠ 0) :
    Tendsto (fun c : ℝ => regularizedNewtonian n ((c ^ 2)⁻¹) x) atTop
      (𝓝 (newtonianKernel n x)) := by
  have hS : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have ht : Tendsto (fun c : ℝ => (c ^ 2)⁻¹ + ‖x‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) := by
    simpa only [zero_add] using tendsto_inv_sq_atTop.add_const (‖x‖ ^ 2)
  simpa only [regularizedNewtonian, newtonianKernel, zero_add] using
    (hasDerivAt_newtonianProfile n hS).continuousAt.tendsto.comp ht

/-- The regularizations converge in all compact continuous test pairings.
Both the power singularity and the logarithmic singularity are controlled
by actual locally integrable functions. -/
theorem tendsto_regularizedNewtonian_test_pairing [NeZero n]
    {g : KernelSpace n → ℝ} (hg : Continuous g) (hs : HasCompactSupport g) :
    Tendsto (fun c : ℝ => ∫ x, regularizedNewtonian n ((c ^ 2)⁻¹) x * g x)
      atTop (𝓝 (∫ x, newtonianKernel n x * g x)) := by
  let M : KernelSpace n → ℝ := fun x =>
    (‖newtonianKernel n x‖ + ‖regularizedNewtonian n 1 x‖) * ‖g x‖
  have hG : Continuous (regularizedNewtonian n 1) :=
    (contDiff_regularizedNewtonian (n := n) (k := 1) zero_lt_one).continuous
  have hMl0 : LocallyIntegrable (fun x : KernelSpace n => ‖newtonianKernel n x‖) := by
    intro x
    obtain ⟨A, hA, hi⟩ := locallyIntegrable_newtonianKernel n x
    exact ⟨A, hA, hi.norm⟩
  have hMl : LocallyIntegrable (fun x : KernelSpace n =>
      ‖newtonianKernel n x‖ + ‖regularizedNewtonian n 1 x‖) :=
    hMl0.add hG.norm.locallyIntegrable
  have hMi : Integrable M := by
    simpa only [M, smul_eq_mul] using hMl.integrable_smul_right_of_hasCompactSupport hg.norm hs.norm
  have hne : ∀ᵐ x : KernelSpace n ∂volume, x ≠ 0 := by
    apply ae_iff.mpr
    simp
  apply tendsto_integral_filter_of_dominated_convergence M
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact ((contDiff_regularizedNewtonian (n := n) (k := 1) (by positivity)).continuous.mul hg).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
    filter_upwards [hne] with x hx
    have hca : 0 < (c ^ 2)⁻¹ := by positivity
    have hca1 : (c ^ 2)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      nlinarith
    have hh := regularizedNewtonian_abs_bound hca hca1 hx
    simpa only [M, Real.norm_eq_abs, abs_mul] using mul_le_mul_of_nonneg_right hh (abs_nonneg (g x))
  · exact hMi
  · filter_upwards [hne] with x hx
    exact (tendsto_regularizedNewtonian hx).mul_const (g x)

lemma continuous_kernelLaplacian {f : KernelSpace n → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (kernelLaplacian f) :=
  continuous_finset_sum _ (fun i _ => continuous_directionalHessian hf _ _)

lemma hasCompactSupport_kernelLaplacian {f : KernelSpace n → ℝ} (hs : HasCompactSupport f) :
    HasCompactSupport (kernelLaplacian f) := by
  classical
  have hh (S : Finset (Fin n)) : HasCompactSupport (fun x => ∑ i ∈ S,
      directionalHessian f x (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
    induction S using Finset.induction_on with
    | empty => simpa using (HasCompactSupport.zero : HasCompactSupport (0 : KernelSpace n → ℝ))
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact ((hs.fderiv_apply ℝ _).fderiv_apply ℝ _).add ih
  exact hh Finset.univ

/-- Genuine distributional fundamental-solution identity for the literal
power/logarithmic kernel. The exact nonzero normalization comes from the
proved finite integral of the approximate identity. -/
theorem newtonian_green_identity [NeZero n] {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    (∫ x, newtonianKernel n x * kernelLaplacian f x) =
      (2 * (n : ℝ) * fundamentalApproxMass n) * f 0 := by
  exact tendsto_nhds_unique
    (tendsto_regularizedNewtonian_test_pairing (continuous_kernelLaplacian hf)
      (hasCompactSupport_kernelLaplacian hs)) (tendsto_regularized_green_pairing hf hs)

lemma directionalHessian_comp_add_right (f : KernelSpace n → ℝ)
    (a x v w : KernelSpace n) :
    directionalHessian (fun y => f (y + a)) x v w = directionalHessian f (x + a) v w := by
  unfold directionalHessian
  have he : (fun y => fderiv ℝ (fun z => f (z + a)) y v) =
      (fun y => fderiv ℝ f (y + a) v) := by
    funext y
    rw [fderiv_comp_add_right]
  rw [he]
  change fderiv ℝ (fun y => (fun z => fderiv ℝ f z v) (y + a)) x w = _
  exact congrArg (fun l : KernelSpace n →L[ℝ] ℝ => l w)
    (fderiv_comp_add_right (𝕜 := ℝ) (f := fun y => fderiv ℝ f y v) (x := x) a)

lemma kernelLaplacian_comp_add_right (f : KernelSpace n → ℝ) (a x : KernelSpace n) :
    kernelLaplacian (fun y => f (y + a)) x = kernelLaplacian f (x + a) := by
  simp only [kernelLaplacian, directionalHessian_comp_add_right]

lemma hasCompactSupport_kernel_translate {f : KernelSpace n → ℝ}
    (hs : HasCompactSupport f) (a : KernelSpace n) : HasCompactSupport (fun x => f (x + a)) := by
  have hK : IsCompact ((fun y : KernelSpace n => y - a) '' tsupport f) :=
    hs.image (continuous_id.sub continuous_const)
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro x hx
  refine ⟨x + a, ?_, ?_⟩
  · exact subset_tsupport f hx
  · module

lemma newtonianKernel_neg (x : KernelSpace n) : newtonianKernel n (-x) = newtonianKernel n x := by
  simp only [newtonianKernel, regularizedNewtonian, norm_neg]

/-- The genuine translated Poisson representation for every compactly
supported C² function, in every positive dimension. -/
theorem newtonian_poisson_representation [NeZero n] {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) (x : KernelSpace n) :
    f x = (2 * (n : ℝ) * fundamentalApproxMass n)⁻¹ *
      ∫ y, newtonianKernel n (x - y) * kernelLaplacian f y := by
  have htrans : ContDiff ℝ 2 (fun y => f (y + x)) :=
    hf.comp (contDiff_id.add contDiff_const)
  have hh := newtonian_green_identity htrans (hasCompactSupport_kernel_translate hs x)
  simp only [kernelLaplacian_comp_add_right, zero_add] at hh
  have htranslate : (∫ z, newtonianKernel n z * kernelLaplacian f (z + x)) =
      ∫ y, newtonianKernel n (y - x) * kernelLaplacian f y := by
    simpa only [add_sub_cancel_right] using integral_add_right_eq_self
      (fun y => newtonianKernel n (y - x) * kernelLaplacian f y) x
  rw [htranslate] at hh
  have heven : (fun y => newtonianKernel n (y - x) * kernelLaplacian f y) =
      (fun y => newtonianKernel n (x - y) * kernelLaplacian f y) := by
    funext y
    rw [show y - x = -(x - y) by module, newtonianKernel_neg]
  rw [heven] at hh
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hC : (2 * (n : ℝ) * fundamentalApproxMass n) ≠ 0 := by
    exact (mul_pos (mul_pos (by norm_num) hn) (fundamentalApproxMass_pos n)).ne'
  rw [hh, inv_mul_cancel_left₀ hC]

end GaussianTilt.MomentMapElliptic
