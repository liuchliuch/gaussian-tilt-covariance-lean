import GaussianTilt.MomentMapLinearDirichletEnergyDecay

/-! # Recovering the full Hölder exponent after the genuine first-order bound -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapLinearDirichlet

theorem exists_full_excess_contraction_scale (n : ℕ) {K β : ℝ}
    (hK : 0 < K) (hβ1 : β < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1/2 ∧ K*θ^((n:ℝ)+2) ≤ θ^((n:ℝ)+2*β)/2 := by
  have he : 0 < 2-2*β := by linarith
  have hc : Continuous (fun r : ℝ => 2*K*r^(2-2*β)) :=
    continuous_const.mul (Real.continuous_rpow_const he.le)
  have hU : {r : ℝ | 2*K*r^(2-2*β)<1} ∈ 𝓝 (0:ℝ) :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp [Real.zero_rpow he.ne'])
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hU
  let θ := min (δ/2) (1/4:ℝ)
  have hθ : 0 < θ := lt_min (half_pos hδ) (by norm_num)
  have hs : 2*K*θ^(2-2*β) ≤ 1 := (hδU (show θ ∈ Metric.ball 0 δ by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hθ]
    exact (min_le_left _ _).trans_lt (half_lt_self hδ))).le
  refine ⟨θ,hθ,(min_le_right _ _).trans (by norm_num),?_⟩
  have hp : θ^((n:ℝ)+2) = θ^((n:ℝ)+2*β)*θ^(2-2*β) := by
    rw [← Real.rpow_add hθ]
    congr 1
    ring
  have ht := mul_le_mul_of_nonneg_left hs (Real.rpow_pos_of_pos hθ ((n:ℝ)+2*β)).le
  rw [hp]
  nlinarith

/-- Once the genuine gradient is bounded, its actual energy has order rⁿ.
The excess iteration then returns the full forcing Hölder exponent β,
rather than repeatedly losing an exponent at each differentiation. -/
theorem excess_decay_of_bounded_energy (n : ℕ) {K β : ℝ}
    (hK : 0 < K) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1/2 ∧ ∀ (E X : ℕ → ℝ) (M F L : ℝ),
      0 ≤ M → 0 ≤ F → 0 ≤ L → 0 ≤ X 0 →
      (∀ k, E k ≤ M*(θ^n)^k) →
      (∀ k, X (k+1) ≤ K*θ^((n:ℝ)+2)*X k+
        L*(θ^(2*β))^k*E k+F*(θ^((n:ℝ)+2*β))^k) →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ k, X k ≤ B*(θ^k)^((n:ℝ)+2*β) := by
  obtain ⟨θ,hθ,hθ2,hcont⟩ := exists_full_excess_contraction_scale n hK hβ1
  let q := θ^((n:ℝ)+2*β)
  let b := K*θ^((n:ℝ)+2)
  have hq : 0 < q := Real.rpow_pos_of_pos hθ _
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hbq : b < q := hcont.trans_lt (half_lt_self hq)
  refine ⟨θ,hθ,hθ2,?_⟩
  intro E X M F L hM hF hL hX0 hE hX
  let B := X 0+(L*M+F)/(q-b)
  have hB : 0 ≤ B := add_nonneg hX0 (div_nonneg (by positivity) (sub_pos.mpr hbq).le)
  have hstep : ∀ k, X (k+1) ≤ b*X k+(L*M+F)*q^k := by
    intro k
    have ht := mul_le_mul_of_nonneg_left (hE k) (by positivity : 0 ≤ L*(θ^(2*β))^k)
    have he : L*(θ^(2*β))^k*(M*(θ^n)^k) = (L*M)*q^k := by
      rw [show θ^n = θ^(n:ℝ) from (Real.rpow_natCast θ n).symm]
      have hp : (θ^(2*β))^k*(θ^(n:ℝ))^k = q^k := by
        rw [← mul_pow,← Real.rpow_add hθ]
        dsimp [q]
        rw [add_comm (2*β) (n:ℝ)]
      calc
        _ = (L*M)*((θ^(2*β))^k*(θ^(n:ℝ))^k) := by ring
        _ = _ := by rw [hp]
    rw [he] at ht
    nlinarith [hX k]
  have hh := geometric_sequence_bound_of_forcing X hX0 hb hq hq.le le_rfl hbq
    (by positivity : 0 ≤ L*M+F) hstep
  refine ⟨B,hB,?_⟩
  intro k
  simpa only [q,Real.rpow_pow_comm hθ.le] using hh k

end GaussianTilt.MomentMapLinearDirichlet
