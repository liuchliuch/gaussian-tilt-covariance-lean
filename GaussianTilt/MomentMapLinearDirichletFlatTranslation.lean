import GaussianTilt.MomentMapLinearDirichletFlatExpansion

/-! # Genuine weak translation and recentering along the flat boundary -/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma tsupport_comp_add_right {ψ : KernelSpace n → ℝ} (a : KernelSpace n) :
    tsupport (fun y => ψ (y+a)) ⊆ (fun y : KernelSpace n => y+a) ⁻¹' tsupport ψ := by
  apply closure_minimal _ ((isClosed_tsupport ψ).preimage (continuous_id.add continuous_const))
  intro y hy
  exact subset_tsupport ψ hy

/-- Translation of the literal distributional equation through actual Haar
measure invariance and the exact translation rule for the Laplacian. -/
theorem distribution_poisson_translate {Ω : Set (KernelSpace n)} {u f : KernelSpace n → ℝ}
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y*kernelLaplacian ψ y) = -(∫ y, f y*ψ y)) (a : KernelSpace n) :
    ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (fun y : KernelSpace n => y+a) ⁻¹' Ω →
      (∫ y, u (y+a)*kernelLaplacian ψ y) = -(∫ y, f (y+a)*ψ y) := by
  intro ψ hψ hψc hψs
  let φ := fun y => ψ (y+(-a))
  have hφ : ContDiff ℝ ∞ φ := hψ.comp (contDiff_id.add contDiff_const)
  have hφc : HasCompactSupport φ := hasCompactSupport_kernel_translate hψc (-a)
  have hφs : tsupport φ ⊆ Ω := by
    intro y hy
    have hh := hψs (tsupport_comp_add_right (-a) hy)
    simpa only [mem_preimage,neg_add_cancel_right] using hh
  have ht := heq φ hφ hφc hφs
  have hchange : (∫ y, u (y+a)*kernelLaplacian φ (y+a)) = -(∫ y, f (y+a)*φ (y+a)) := by
    rw [integral_add_right_eq_self (fun y => u y*kernelLaplacian φ y) a,
      integral_add_right_eq_self (fun y => f y*φ y) a]
    exact ht
  have hφlap (y : KernelSpace n) : kernelLaplacian φ (y+a) = kernelLaplacian ψ y := by
    rw [kernelLaplacian_comp_add_right]
    simp only [add_neg_cancel_right]
  simpa only [hφlap,φ,add_neg_cancel_right] using hchange

lemma flat_recenter_mem_ball {r : ℝ} (hr : 0 < r) {a : KernelSpace n}
    (har : ‖a‖+2*r ≤ 2) {x : KernelSpace n} (hx : x ∈ Metric.ball (0 : KernelSpace n) 2) :
    r • x+a ∈ Metric.ball (0 : KernelSpace n) 2 := by
  have hn : ‖x‖ < 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  rw [Metric.mem_ball,dist_zero_right]
  have hb := norm_add_le (r • x) a
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hb
  nlinarith

/-- An actual tangential recentering and positive dilation of weak data.
The containing-ball condition is checked directly, including the genuine
L² class, zero extension, height bound, and distributional equation. -/
theorem FlatWeakPoisson.recenter {j : Fin n} {u f : KernelSpace n → ℝ}
    (h : FlatWeakPoisson j u f) (a : KernelSpace n) (ha : a j = 0)
    {r : ℝ} (hr : 0 < r) (har : ‖a‖+2*r ≤ 2) :
    FlatWeakPoisson j (fun x => u (r • x+a)) (fun x => r^2*f (r • x+a)) := by
  have hmaps : MapsTo (fun x : KernelSpace n => r • x+a) (flatUpperBall j 2) (flatUpperBall j 2) := by
    intro x hx
    refine ⟨flat_recenter_mem_ball hr har hx.1,?_⟩
    simpa only [mem_setOf_eq,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,ha,add_zero] using mul_pos hr hx.2
  have hLp : MemLp (fun x => u (x+a)) 2 volume :=
    h.memLp.comp_measurePreserving (measurePreserving_add_right volume a)
  refine ⟨memLp_comp_smul_dirichlet hLp hr.ne',?_,?_,?_,?_⟩
  · intro x hx
    apply h.zero_lower
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,ha,add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hr.le hx
  · exact h.continuous.comp ((continuous_const.smul continuous_id).add continuous_const).continuousOn hmaps
  · obtain ⟨C,hC,hg⟩ := h.growth
    refine ⟨C*r,by positivity,?_⟩
    intro x hx
    have hh := hg (r • x+a) (flat_recenter_mem_ball hr har hx)
    simpa only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,ha,add_zero,abs_mul,abs_of_pos hr,mul_assoc] using hh
  · intro ψ hψ hψc hψs
    have heq := distribution_poisson_translate h.equation a
    have hh := distribution_poisson_smul heq hr 1 ψ hψ hψc (fun x hx => hmaps (hψs hx))
    simpa only [one_mul] using hh

end GaussianTilt.MomentMapLinearDirichlet
