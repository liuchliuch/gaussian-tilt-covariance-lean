import GaussianTilt.MomentMapLinearDirichletEnergyConstants

/-! # Energy iteration scales can respect a genuine elliptic chart threshold -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapLinearDirichlet

lemma exists_small_scale_two_powers {a b A B τ : ℝ} (ha : 0 < a) (hb : 0 < b) (hτ : 0 < τ) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1/2 ∧ θ ≤ τ ∧ A*θ^a ≤ 1 ∧ B*θ^b ≤ 1 := by
  have hca : Continuous (fun r : ℝ => A*r^a) := continuous_const.mul (Real.continuous_rpow_const ha.le)
  have hcb : Continuous (fun r : ℝ => B*r^b) := continuous_const.mul (Real.continuous_rpow_const hb.le)
  have hU : {r : ℝ | A*r^a<1 ∧ B*r^b<1} ∈ 𝓝 (0:ℝ) :=
    ((isOpen_lt hca continuous_const).inter (isOpen_lt hcb continuous_const)).mem_nhds
      (by simp [Real.zero_rpow ha.ne',Real.zero_rpow hb.ne'])
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hU
  let θ := min (δ/2) (min (1/4:ℝ) (τ/2))
  have hθ : 0 < θ := lt_min (half_pos hδ) (lt_min (by norm_num) (half_pos hτ))
  have hs := hδU (show θ ∈ Metric.ball 0 δ by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hθ]
    exact (min_le_left _ _).trans_lt (half_lt_self hδ))
  exact ⟨θ,hθ,(min_le_right _ _).trans ((min_le_left _ _).trans (by norm_num)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith)),hs.1.le,hs.2.le⟩

/-- The energy and excess contractions are constructed below any genuine
positive radius ratio supplied by frozen-SPD normalization. -/
theorem exists_energy_excess_contraction_constants_below (n : ℕ) {K β τ : ℝ}
    (hK : 0 < K) (hβ : 0 < β) (hβ1 : β ≤ 1) (hτ : 0 < τ) :
    ∃ θ ε : ℝ, 0 < θ ∧ θ ≤ 1/2 ∧ θ ≤ τ ∧ 0 < ε ∧
      K*θ^n+K*ε^2 ≤ θ^((n:ℝ)-β/2)/2 ∧
      K*θ^((n:ℝ)+2) ≤ θ^((n:ℝ)+β)/2 := by
  obtain ⟨θ,hθ,hθ2,hθτ,hE,hX⟩ := exists_small_scale_two_powers
    (A := 4*K) (B := 2*K) (half_pos hβ) (by linarith : 0 < 2-β) hτ
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
  refine ⟨θ,ε,hθ,hθ2,hθτ,hε,?_,?_⟩
  · have ht := mul_le_mul_of_nonneg_left hE (Real.rpow_pos_of_pos hθ ((n:ℝ)-β/2)).le
    rw [hpowE,he]
    nlinarith
  · have ht := mul_le_mul_of_nonneg_left hX (Real.rpow_pos_of_pos hθ ((n:ℝ)+β)).le
    rw [hpowX]
    nlinarith

end GaussianTilt.MomentMapLinearDirichlet
