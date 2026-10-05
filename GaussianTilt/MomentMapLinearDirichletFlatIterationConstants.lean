import GaussianTilt.MomentMapLinearDirichletFlatResidual

/-!
# Genuine numerical constants for flat quadratic improvement

The harmonic cubic remainder is strictly better than order 2+α. A real
small-radius argument therefore chooses a positive contraction radius and
forcing threshold. The resulting estimate is a theorem, not an assumed
improvement-of-flatness or contraction statement.
-/
noncomputable section
set_option maxHeartbeats 1000000
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapLinearDirichlet

/-- Actual numerical choice of the scale and small forcing threshold
needed to turn the proved cubic-plus-forcing estimate into 2+α decay. -/
theorem exists_flat_quadratic_improvement_constants {K α : ℝ}
    (hK : 0 < K) (hα : 0 < α) (hα1 : α < 1) :
    ∃ θ ε : ℝ, 0 < θ ∧ θ ≤ 1/8 ∧ 0 < ε ∧ ε ≤ 1/4 ∧
      ∀ B F t : ℝ, 0 ≤ B → B ≤ 1 → 0 ≤ F → F ≤ ε → 0 ≤ t → t ≤ 2*θ →
        K*(B+4*F)*t^3+4*F ≤ θ^(2+α) := by
  have hβ : 0 < 1-α := sub_pos.mpr hα1
  have hc : Continuous (fun r : ℝ => 32*K*r^(1-α)) :=
    continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr hβ.le))
  have hU : {r : ℝ | 32*K*r^(1-α) < 1} ∈ 𝓝 (0 : ℝ) :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp [Real.zero_rpow hβ.ne'])
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hU
  let θ := min (δ/2) (1/16 : ℝ)
  have hθ : 0 < θ := lt_min (half_pos hδ) (by norm_num)
  have hθ8 : θ ≤ 1/8 := (min_le_right _ _).trans (by norm_num)
  have hθ1 : θ ≤ 1 := hθ8.trans (by norm_num)
  have hθδ : θ < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hsmall : 32*K*θ^(1-α) ≤ 1 := (hδU (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hθ]
    exact hθδ)).le
  let ε := θ^(2+α)/8
  have hp : 0 < θ^(2+α) := Real.rpow_pos_of_pos hθ _
  have hε : 0 < ε := div_pos hp (by norm_num)
  have hp1 : θ^(2+α) ≤ 1 := Real.rpow_le_one hθ.le hθ1 (by linarith)
  have hε4 : ε ≤ 1/4 := by dsimp [ε]; linarith
  refine ⟨θ,ε,hθ,hθ8,hε,hε4,?_⟩
  intro B F t hB hB1 hF hFε ht htθ
  have hBF : B+4*F ≤ 2 := by linarith
  have hBF0 : 0 ≤ B+4*F := by positivity
  have ht3 : t^3 ≤ (2*θ)^3 := pow_le_pow_left₀ ht htθ 3
  have hmain : K*(B+4*F)*t^3 ≤ 16*K*θ^3 := by
    calc
      _ ≤ K*2*(2*θ)^3 := mul_le_mul (mul_le_mul_of_nonneg_left hBF hK.le) ht3
        (pow_nonneg ht 3) (by positivity)
      _ = _ := by ring
  have hexp : θ^(2+α)*θ^(1-α) = θ^3 := by
    rw [← Real.rpow_add hθ]
    norm_num [show (2+α)+(1-α) = (3 : ℝ) by ring]
  have hscale := mul_le_mul_of_nonneg_left hsmall hp.le
  have hmainhalf : 16*K*θ^3 ≤ θ^(2+α)/2 := by
    rw [← hexp]
    nlinarith
  have hforce : 4*F ≤ θ^(2+α)/2 := by
    change F ≤ θ^(2+α)/8 at hFε
    linarith
  linarith

end GaussianTilt.MomentMapLinearDirichlet
