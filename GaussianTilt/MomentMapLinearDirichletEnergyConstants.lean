import GaussianTilt.MomentMapLinearDirichletEnergyIteration

/-! # Constructed contraction constants for boundary energy and excess -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapLinearDirichlet

/-- A true sufficiently small scale and coefficient oscillation are
constructed by continuity of positive powers at zero. These give room
for both the energy exponent and the subsequent excess exponent. -/
theorem exists_energy_excess_contraction_constants (n : ℕ) {K β : ℝ}
    (hK : 0 < K) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ θ ε : ℝ, 0 < θ ∧ θ ≤ 1/2 ∧ 0 < ε ∧
      K*θ^n+K*ε^2 ≤ θ^((n:ℝ)-β/2)/2 ∧
      K*θ^((n:ℝ)+2) ≤ θ^((n:ℝ)+β)/2 := by
  have hb : 0 < β/2 := half_pos hβ
  have hc : 0 < 2-β := by linarith
  have hcont1 : Continuous (fun r : ℝ => 4*K*r^(β/2)) :=
    continuous_const.mul (Real.continuous_rpow_const hb.le)
  have hcont2 : Continuous (fun r : ℝ => 2*K*r^(2-β)) :=
    continuous_const.mul (Real.continuous_rpow_const hc.le)
  have hU : {r : ℝ | 4*K*r^(β/2)<1 ∧ 2*K*r^(2-β)<1} ∈ 𝓝 (0:ℝ) :=
    ((isOpen_lt hcont1 continuous_const).inter (isOpen_lt hcont2 continuous_const)).mem_nhds
      (by simp [Real.zero_rpow hb.ne',Real.zero_rpow hc.ne'])
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hU
  let θ := min (δ/2) (1/4 : ℝ)
  have hθ : 0 < θ := lt_min (half_pos hδ) (by norm_num)
  have hθ2 : θ ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  have hθδ : θ < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hs := hδU (show θ ∈ Metric.ball 0 δ by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hθ]; exact hθδ)
  let ε := Real.sqrt (θ^((n:ℝ)-β/2)/(4*K))
  have hε : 0 < ε := Real.sqrt_pos.2 (div_pos (Real.rpow_pos_of_pos hθ _) (by positivity))
  have hεsq : ε^2 = θ^((n:ℝ)-β/2)/(4*K) := Real.sq_sqrt (by positivity)
  have he : K*ε^2 = θ^((n:ℝ)-β/2)/4 := by rw [hεsq]; field_simp
  have hpowE : θ^n = θ^((n:ℝ)-β/2)*θ^(β/2) := by
    rw [← Real.rpow_add hθ]
    simp only [sub_add_cancel,Real.rpow_natCast]
  have hpowX : θ^((n:ℝ)+2) = θ^((n:ℝ)+β)*θ^(2-β) := by
    rw [← Real.rpow_add hθ]
    congr 1
    ring
  refine ⟨θ,ε,hθ,hθ2,hε,?_,?_⟩
  · have ht := mul_le_mul_of_nonneg_left hs.1.le (Real.rpow_pos_of_pos hθ ((n:ℝ)-β/2)).le
    rw [hpowE,he]
    nlinarith
  · have ht := mul_le_mul_of_nonneg_left hs.2.le (Real.rpow_pos_of_pos hθ ((n:ℝ)+β)).le
    rw [hpowX]
    nlinarith

/-- Exact exponent comparisons for the two-stage construction. The final
mean-square excess exponent is n+β, hence the reconstructed gradient
exponent is the genuine positive β/2. -/
theorem energy_excess_power_parameters {n : ℕ} (hn : 0 < n) {θ β : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    0 < θ^((n:ℝ)-β/2) ∧ θ^((n:ℝ)-β/2)<1 ∧
    0 < θ^((n:ℝ)+β) ∧ θ^((n:ℝ)+β)<1 ∧
    θ^((n:ℝ)+2*β) ≤ θ^((n:ℝ)-β/2) ∧
    θ^((n:ℝ)+2*β) ≤ θ^((n:ℝ)+β) ∧
    θ^(2*β)*θ^((n:ℝ)-β/2) ≤ θ^((n:ℝ)+β) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨Real.rpow_pos_of_pos hθ _,Real.rpow_lt_one hθ.le hθ1 (by linarith),
    Real.rpow_pos_of_pos hθ _,Real.rpow_lt_one hθ.le hθ1 (by linarith),?_,?_,?_⟩
  · exact Real.rpow_le_rpow_of_exponent_ge hθ hθ1.le (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_ge hθ hθ1.le (by linarith)
  · rw [← Real.rpow_add hθ]
    exact Real.rpow_le_rpow_of_exponent_ge hθ hθ1.le (by linarith)

end GaussianTilt.MomentMapLinearDirichlet
