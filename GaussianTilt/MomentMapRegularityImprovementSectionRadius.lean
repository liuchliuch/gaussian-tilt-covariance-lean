import GaussianTilt.MomentMapRegularityImprovementSectionDensity
import GaussianTilt.MomentMapRegularityImprovementSeedTransfer

/-! # Choosing actual source sections with the required small normalized density -/
noncomputable section
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapRegularity

lemma exists_small_improvement_section_radius {r rin F m α ρ N R δ : ℝ}
    (hr : 0 < r) (hrin : 0 < rin) (hm : 0 < m) (hα : 0 < α) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε≤r/2 ∧ ε≤1 ∧ F*ε^α/m≤δ ∧
      (F*(ε/rin)^α/m)*(ρ*N/R)^α≤1 := by
  have hc1 : Continuous (fun ε:ℝ=>F*ε^α/m) :=
    (continuous_const.mul (Real.continuous_rpow_const hα.le)).div_const m
  have hc2 : Continuous (fun ε:ℝ=>(F*(ε/rin)^α/m)*(ρ*N/R)^α) :=
    ((continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
      (continuous_id.div_const rin))).div_const m).mul continuous_const
  have h1 : ∀ᶠ ε:ℝ in 𝓝 0, F*ε^α/m<δ :=
    hc1.continuousAt.eventually (gt_mem_nhds (by simpa [Real.zero_rpow hα.ne'] using hδ))
  have h2 : ∀ᶠ ε:ℝ in 𝓝 0, (F*(ε/rin)^α/m)*(ρ*N/R)^α<1 :=
    hc2.continuousAt.eventually (gt_mem_nhds (by simp [Real.zero_rpow hα.ne']))
  have he : ∀ᶠ ε:ℝ in 𝓝 0, ε≤r/2 ∧ ε≤1 ∧ F*ε^α/m≤δ ∧
      (F*(ε/rin)^α/m)*(ρ*N/R)^α≤1 := by
    filter_upwards [gt_mem_nhds (half_pos hr),gt_mem_nhds (by norm_num : (0:ℝ)<1),h1,h2]
      with ε hεr hε1 hεf hεg
    exact ⟨hεr.le,hε1.le,hεf.le,hεg.le⟩
  obtain ⟨s,hs,hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨s/2,half_pos hs,hsub ?_⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hs)]
  linarith

end GaussianTilt.MomentMapRegularity
