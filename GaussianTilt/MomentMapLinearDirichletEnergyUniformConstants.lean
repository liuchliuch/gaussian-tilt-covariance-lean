import GaussianTilt.MomentMapLinearDirichletEnergyIteration

/-! # Data-linear constants for the actual two-stage geometric iteration -/
noncomputable section
set_option maxHeartbeats 1000000
namespace GaussianTilt.MomentMapLinearDirichlet

/-- The inhomogeneous recurrence preserves a single data factor Q. -/
theorem geometric_sequence_bound_with_data_factor (u : ℕ → ℝ) {a q t F Q : ℝ}
    (hu0 : 0 ≤ u 0) (hQ : 0 ≤ Q) (huQ : u 0 ≤ Q) (ha : 0 ≤ a) (hq : 0 < q)
    (ht : 0 ≤ t) (htq : t ≤ q) (haq : a < q) (hF : 0 ≤ F)
    (hstep : ∀ k, u (k+1) ≤ a*u k+(F*Q)*t^k) :
    ∀ k, u k ≤ (1+F/(q-a))*Q*q^k := by
  have hb := geometric_sequence_bound_of_forcing u hu0 ha hq ht htq haq (mul_nonneg hF hQ) hstep
  intro k
  apply (hb k).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq.le _)
  calc
    u 0+(F*Q)/(q-a) ≤ Q+(F*Q)/(q-a) := add_le_add_right huQ _
    _ = _ := by ring

/-- Both stage constants depend on the recurrence data, while the input
energy and load share one explicit multiplicative size factor. -/
theorem two_stage_energy_excess_decay_with_data_factor (E X : ℕ → ℝ)
    {a b qE qX d t F K Q : ℝ}
    (hE0 : 0 ≤ E 0) (hX0 : 0 ≤ X 0) (hQ : 0 ≤ Q) (hEQ : E 0 ≤ Q) (hXQ : X 0 ≤ Q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hqE : 0 < qE) (hqX : 0 < qX) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (haq : a < qE) (hbq : b < qX) (htE : t ≤ qE) (htX : t ≤ qX) (hdq : d*qE ≤ qX)
    (hF : 0 ≤ F) (hK : 0 ≤ K)
    (hEstep : ∀ k, E (k+1) ≤ a*E k+(F*Q)*t^k)
    (hXstep : ∀ k, X (k+1) ≤ b*X k+K*d^k*E k+(F*Q)*t^k) :
    let A := 1+F/(qE-a)
    let B := 1+(K*A+F)/(qX-b)
    (∀ k,E k ≤ A*Q*qE^k) ∧ (∀ k,X k ≤ B*Q*qX^k) := by
  dsimp only
  let A := 1+F/(qE-a)
  have hA : 0 ≤ A := add_nonneg zero_le_one (div_nonneg hF (sub_pos.mpr haq).le)
  have hEb := geometric_sequence_bound_with_data_factor E hE0 hQ hEQ ha hqE ht htE haq hF hEstep
  refine ⟨hEb,?_⟩
  apply geometric_sequence_bound_with_data_factor X hX0 hQ hXQ hb hqX hqX.le le_rfl hbq (by positivity : 0 ≤ K*A+F)
  intro k
  have hpowD : (d*qE)^k ≤ qX^k := pow_le_pow_left₀ (mul_nonneg hd hqE.le) hdq k
  have hpowT : t^k ≤ qX^k := pow_le_pow_left₀ ht htX k
  have henergy := mul_le_mul_of_nonneg_left (hEb k) (mul_nonneg hK (pow_nonneg hd k))
  have hproduct : K*d^k*(A*Q*qE^k) = (K*A*Q)*(d*qE)^k := by rw [mul_pow]; ring
  have herr : K*d^k*E k ≤ (K*A*Q)*qX^k := by
    apply henergy.trans
    rw [hproduct]
    exact mul_le_mul_of_nonneg_left hpowD (by positivity)
  have hf := mul_le_mul_of_nonneg_left hpowT (mul_nonneg hF hQ)
  nlinarith [hXstep k]

end GaussianTilt.MomentMapLinearDirichlet
