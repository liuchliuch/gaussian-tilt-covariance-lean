import GaussianTilt.MomentMapLinearDirichletEnergyConstants

/-! # Dimensionally correct simultaneous decay of energy and boundary excess -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapLinearDirichlet

/-- The two-stage construction gives actual n−β/2 energy decay and n+β
excess decay, from the specified one-step estimates. Its scale and small
coefficient threshold are constructed before the sequences or forcing. -/
theorem exists_two_stage_energy_excess_decay_constants (n : ℕ) (hn : 0 < n) {K β : ℝ}
    (hK : 0 < K) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ θ ε : ℝ, 0 < θ ∧ θ ≤ 1/2 ∧ 0 < ε ∧
      ∀ (E X : ℕ → ℝ) (F L : ℝ), 0 ≤ F → 0 ≤ L → (∀ k, 0 ≤ E k) → (∀ k, 0 ≤ X k) →
        (∀ k, E (k+1) ≤ (K*θ^n+K*ε^2)*E k+F*(θ^((n:ℝ)+2*β))^k) →
        (∀ k, X (k+1) ≤ K*θ^((n:ℝ)+2)*X k+L*(θ^(2*β))^k*E k+F*(θ^((n:ℝ)+2*β))^k) →
        ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
          (∀ k, E k ≤ A*(θ^k)^((n:ℝ)-β/2)) ∧
          (∀ k, X k ≤ B*(θ^k)^((n:ℝ)+β)) := by
  obtain ⟨θ,ε,hθ,hθ2,hε,hEc,hXc⟩ := exists_energy_excess_contraction_constants n hK hβ hβ1
  have hθ1 : θ < 1 := hθ2.trans_lt (by norm_num)
  obtain ⟨hqE,hqE1,hqX,hqX1,htE,htX,hdq⟩ := energy_excess_power_parameters hn hθ hθ1 hβ hβ1
  let a := K*θ^n+K*ε^2
  let b := K*θ^((n:ℝ)+2)
  let qE := θ^((n:ℝ)-β/2)
  let qX := θ^((n:ℝ)+β)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have haq : a < qE := hEc.trans_lt (half_lt_self hqE)
  have hbq : b < qX := hXc.trans_lt (half_lt_self hqX)
  refine ⟨θ,ε,hθ,hθ2,hε,?_⟩
  intro E X F L hF hL hE hX hEstep hXstep
  let A := E 0+F/(qE-a)
  let B := X 0+(L*A+F)/(qX-b)
  have hA : 0 ≤ A := add_nonneg (hE 0) (div_nonneg hF (sub_pos.mpr haq).le)
  have hB : 0 ≤ B := add_nonneg (hX 0) (div_nonneg (by positivity) (sub_pos.mpr hbq).le)
  have hdec := two_stage_energy_excess_decay E X (hE 0) (hX 0) ha hb hqE hqX
    (Real.rpow_pos_of_pos hθ (2*β)).le (Real.rpow_pos_of_pos hθ ((n:ℝ)+2*β)).le
    haq hbq htE htX hdq hF hL hEstep hXstep
  refine ⟨A,B,hA,hB,?_,?_⟩
  · intro k
    simpa only [qE,Real.rpow_pow_comm hθ.le] using hdec.1 k
  · intro k
    simpa only [qX,Real.rpow_pow_comm hθ.le] using hdec.2 k

end GaussianTilt.MomentMapLinearDirichlet
