import GaussianTilt.MomentMapSchauderBoundaryValueField
import GaussianTilt.MomentMapSchauderCutoffHolder
import GaussianTilt.MomentMapLinearDirichletHolderInterior

/-! # The actual continuous flat weak solution is genuinely C² inside -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- Compactness of the forcing is obtained by a constructed cutoff. The
canonical weak-to-classical representative equals the original continuous
solution everywhere in the open upper half-ball. -/
theorem flatWeakPoisson_classical [NeZero n] {j : Fin n} {u f : KernelSpace n → ℝ}
    (hu : FlatWeakPoisson j u f) (hf : Continuous f) {α H : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H)
    (hfH : ∀ x y, |f x-f y| ≤ H*‖x-y‖^α) :
    ContDiffOn ℝ 2 u (flatUpperBall j 2) ∧
      (∀ x ∈ flatUpperBall j 2, kernelLaplacian u x= -f x) := by
  let χ := scaledInteriorCutoff (0 : KernelSpace n) 2
  let g := fun x => -(χ x*f x)
  have hχc : ContDiff ℝ ∞ χ := scaledInteriorCutoff_contDiff 0 2
  have hχs : HasCompactSupport χ := scaledInteriorCutoff_compact 0 (by norm_num)
  have hg : Continuous g := (hχc.continuous.mul hf).neg
  have hgs : HasCompactSupport g := (hχs.mul_right).neg
  obtain ⟨B₁,B₂,B₃,hB₁,hB₂,hB₃,hcut⟩ :=
    exists_scaled_cutoff_jet_holder_bounds (E := KernelSpace n) hα.le hα1.le
  let L := (B₁+2)*(2:ℝ)^(-α)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hχH : ∀ x y, |χ x-χ y| ≤ L*‖x-y‖^α := (hcut 0 2 (by norm_num)).2.2.1
  have hχB : ∀ x, |χ x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (scaledInteriorCutoff_nonneg 0 x 2)]
    exact scaledInteriorCutoff_le_one 0 x 2
  have hχ0 : ∀ x ∉ Metric.ball (0 : KernelSpace n) 4, χ x=0 := by
    intro x hx
    apply scaledInteriorCutoff_zero (by norm_num : (0:ℝ)<2)
    simpa only [Metric.mem_ball,dist_zero_right,not_lt,sub_zero,show (2:ℝ)*2=4 by norm_num] using hx
  let F := |f 0|+H*4^α
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hfB : ∀ x ∈ Metric.ball (0 : KernelSpace n) 4, |f x| ≤ F := by
    intro x hx
    have ht := hfH x 0
    simp only [sub_zero] at ht
    have hn : ‖x‖ ≤ 4 := (show ‖x‖ < 4 by simpa only [Metric.mem_ball,dist_zero_right] using hx).le
    have hh := ht.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hn hα.le) hH)
    have habs : |f x| ≤ |f x-f 0|+|f 0| := by
      simpa only [sub_add_cancel] using abs_add_le (f x-f 0) (f 0)
    dsimp [F]
    linarith
  have hgH : ∀ x y, |g x-g y| ≤ (H+F*L)*‖x-y‖^α := by
    have hh := global_holder_cutoff_product zero_le_one hF hL hH hχB hfB hχH
      (fun x _ y _ => hfH x y) hχ0
    intro x y
    simpa only [g,neg_sub_neg,abs_sub_comm,one_mul] using hh x y
  have hgeq : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, g x= -f x := by
    intro x hx
    dsimp [g]
    rw [show χ x=1 from scaledInteriorCutoff_one (by norm_num) (by
      simpa only [sub_zero] using (show ‖x‖ < 2 by simpa only [Metric.mem_ball,dist_zero_right] using hx).le),one_mul]
  have hΩ : IsOpen (flatUpperBall j 2) := isOpen_flatUpperBall j 2
  have hΩb : Bornology.IsBounded (flatUpperBall j 2) := (Metric.isBounded_ball (x := (0 : KernelSpace n)) (r := 2)).subset inter_subset_left
  obtain ⟨A,hA,huA⟩ := hu.growth
  have huB : ∀ x ∈ flatUpperBall j 2, |u x| ≤ 2*A := by
    intro x hx
    have hc : |x j| ≤ ‖x‖ := PiLp.norm_apply_le x j
    have hn : ‖x‖ < 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hx.1
    exact (huA x hx.1).trans ((mul_le_mul_of_nonneg_left (by linarith : |x j| ≤ 2) hA).trans_eq (mul_comm A 2))
  have heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ flatUpperBall j 2 →
      (∫ x, u x*kernelLaplacian ψ x)=∫ x, g x*ψ x := by
    intro ψ hψ hψs hψsupp
    rw [hu.equation ψ hψ hψs hψsupp]
    have hi : (∫ x, g x*ψ x)=∫ x, -(f x*ψ x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport ψ
      · rw [hgeq x (hψsupp hx).1]
        ring
      · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero,mul_zero,neg_zero]
    rw [hi,integral_neg]
  have hi := hu.memLp.locallyIntegrable (by norm_num)
  have hc := harmonicRepresentative_classical_of_holder_distribution_poisson hΩ hΩb hi huB hg hgs
    hα hα1 (by positivity : 0 ≤ H+F*L) hgH heq
  have hrepC : ContinuousOn (harmonicRepresentative u) (flatUpperBall j 2) :=
    hΩ.continuousOn_iff.mpr (fun x hx => (hc.1 x hx).continuousAt)
  have hrepeq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae (harmonicRepresentative_ae_eq hi)) hΩ hrepC hu.continuous
  have hn : ∀ x ∈ flatUpperBall j 2, harmonicRepresentative u =ᶠ[𝓝 x] u :=
    fun x hx => eventually_of_mem (hΩ.mem_nhds hx) (fun y hy => hrepeq hy)
  constructor
  · intro x hx
    exact ((hc.1 x hx).congr_of_eventuallyEq (hn x hx).symm).contDiffWithinAt
  · intro x hx
    rw [← kernelLaplacian_congr_nhds (hn x hx),hc.2 x hx,hgeq x hx.1]

end GaussianTilt.MomentMapSchauder
