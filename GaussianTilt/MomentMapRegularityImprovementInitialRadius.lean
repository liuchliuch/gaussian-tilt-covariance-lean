import GaussianTilt.MomentMapRegularityImprovementBudget

/-! # Constructing the small initial scale required by the closed recurrence -/
noncomputable section
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapRegularity

lemma exists_improvement_initial_radius {α c γ d A B K : ℝ}
    (hα : 0 < α) (hc : 0 < c) (hγ : 0 < γ) (hd : 0 < d) :
    ∃ R : ℝ, 0 < R ∧ R<1 ∧ A*R^γ≤1/16 ∧ B*R^α<1 ∧ R^d≤1/8 ∧
      K*R^d≤1/2 ∧ R^c≤1/16 ∧ 2*K*R^d/(1-R^(c*d))≤Real.log 2 := by
  have hsmall (e M b : ℝ) (he : 0 < e) (hb : 0 < b) :
      ∀ᶠ r : ℝ in 𝓝 0, M*r^e<b := by
    have hh : Continuous (fun r : ℝ=>M*r^e) := continuous_const.mul (Real.continuous_rpow_const he.le)
    exact hh.continuousAt.eventually (gt_mem_nhds (by simpa [Real.zero_rpow he.ne'] using hb))
  have hbcont : ContinuousAt (fun r : ℝ=>2*K*r^d/(1-r^(c*d))) 0 := by
    apply (continuous_const.mul (Real.continuous_rpow_const hd.le)).continuousAt.div
      ((continuous_const.sub (Real.continuous_rpow_const (mul_pos hc hd).le)).continuousAt)
    simp [Real.zero_rpow (mul_pos hc hd).ne']
  have hbsmall : ∀ᶠ r : ℝ in 𝓝 0, 2*K*r^d/(1-r^(c*d))<Real.log 2 :=
    hbcont.eventually (gt_mem_nhds (by
      simpa [Real.zero_rpow hd.ne',Real.zero_rpow (mul_pos hc hd).ne'] using
        Real.log_pos (by norm_num : (1:ℝ)<2)))
  have hv : ∀ᶠ r : ℝ in 𝓝 0, r<1 ∧ A*r^γ≤1/16 ∧ B*r^α<1 ∧ r^d≤1/8 ∧
      K*r^d≤1/2 ∧ r^c≤1/16 ∧ 2*K*r^d/(1-r^(c*d))≤Real.log 2 := by
    filter_upwards [gt_mem_nhds (by norm_num : (0:ℝ)<1),
      hsmall γ A (1/16) hγ (by norm_num),hsmall α B 1 hα (by norm_num),
      hsmall d 1 (1/8) hd (by norm_num),hsmall d K (1/2) hd (by norm_num),
      hsmall c 1 (1/16) hc (by norm_num),hbsmall] with r hr h1 h2 h3 h4 h5 h6
    exact ⟨hr,h1.le,h2,by simpa using h3.le,h4.le,by simpa using h5.le,h6.le⟩
  obtain ⟨η,hη,hsub⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨η/2,half_pos hη,hsub ?_⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hη)]
  linarith

end GaussianTilt.MomentMapRegularity
