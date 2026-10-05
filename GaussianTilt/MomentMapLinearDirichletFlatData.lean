import GaussianTilt.MomentMapLinearDirichletFlatRescaling

/-!
# Literal flat weak Poisson data and its actual rescaling

This package contains only the concrete L², zero-extension, continuity,
linear-height, and compact-test identities already proved for the weak
Dirichlet solution. Its dilation closure is derived from the true Haar and
second-derivative formulas, for use in the boundary iteration.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def flatUpperBall (j : Fin n) (R : ℝ) : Set (KernelSpace n) :=
  Metric.ball 0 R ∩ {x | 0 < x j}

structure FlatWeakPoisson (j : Fin n) (u f : KernelSpace n → ℝ) : Prop where
  memLp : MemLp u 2 volume
  zero_lower : ∀ x, x j ≤ 0 → u x = 0
  continuous : ContinuousOn u (flatUpperBall j 2)
  growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ C*|x j|
  equation : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ flatUpperBall j 2 → (∫ x, u x * kernelLaplacian ψ x) = -(∫ x, f x * ψ x)

lemma smul_mem_flatUpperBall (j : Fin n) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {x : KernelSpace n} (hx : x ∈ flatUpperBall j 2) : r • x ∈ flatUpperBall j 2 := by
  constructor
  · have hn : ‖x‖ < 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx.1
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_right hr1 (norm_nonneg x)).trans_lt (by simpa using hn)
  · change 0 < r*x j
    exact mul_pos hr hx.2

/-- Every concrete requirement of the normalized weak problem survives
an actual positive dilation and amplitude change. -/
theorem FlatWeakPoisson.rescale {j : Fin n} {u f : KernelSpace n → ℝ}
    (h : FlatWeakPoisson j u f) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (s : ℝ) :
    FlatWeakPoisson j (fun x => s*u (r • x)) (fun x => s*r^2*f (r • x)) := by
  have hmaps : MapsTo (fun x : KernelSpace n => r • x) (flatUpperBall j 2) (flatUpperBall j 2) :=
    fun _ hx => smul_mem_flatUpperBall j hr hr1 hx
  refine ⟨(memLp_comp_smul_dirichlet h.memLp hr.ne').const_mul s, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [h.zero_lower (r • x) (by change r*x j ≤ 0; exact mul_nonpos_of_nonneg_of_nonpos hr.le hx), mul_zero]
  · exact continuousOn_const.mul (h.continuous.comp (continuous_const.smul continuous_id).continuousOn hmaps)
  · obtain ⟨C, hC, hg⟩ := h.growth
    refine ⟨|s| * C*r, by positivity, ?_⟩
    intro x hx
    have hxball : r • x ∈ Metric.ball (0 : KernelSpace n) 2 := by
      have hn : ‖x‖ < 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_right hr1 (norm_nonneg x)).trans_lt (by simpa using hn)
    have hb := mul_le_mul_of_nonneg_left (hg (r • x) hxball) (abs_nonneg s)
    rw [abs_mul]
    convert hb using 1 <;> simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hr] <;> ring
  · intro ψ hψ hψc hψs
    exact distribution_poisson_smul h.equation hr s ψ hψ hψc
      (fun x hx => hmaps (hψs hx))

/-- A scalar amplitude change is a special case of the actual dilation law. -/
theorem FlatWeakPoisson.amplitude {j : Fin n} {u f : KernelSpace n → ℝ}
    (h : FlatWeakPoisson j u f) (s : ℝ) :
    FlatWeakPoisson j (fun x => s*u x) (fun x => s*f x) := by
  simpa only [one_smul, one_pow, mul_one] using h.rescale (r := 1) zero_lt_one le_rfl s

end GaussianTilt.MomentMapLinearDirichlet
