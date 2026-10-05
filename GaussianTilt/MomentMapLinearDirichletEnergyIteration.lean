import GaussianTilt.MomentMapLinearDirichletCampanatoL2Local

/-! # Quantitative two-stage energy and excess decay -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapLinearDirichlet

/-- A genuine inhomogeneous discrete recurrence, with its explicit initial
and forcing constant. The contraction leaves enough room for the forcing
at the requested geometric exponent. -/
theorem geometric_sequence_bound_of_forcing (u : ℕ → ℝ) {a q t M : ℝ}
    (hu0 : 0 ≤ u 0) (ha : 0 ≤ a) (hq : 0 < q) (ht : 0 ≤ t)
    (htq : t ≤ q) (haq : a < q) (hM : 0 ≤ M)
    (hstep : ∀ k, u (k+1) ≤ a*u k+M*t^k) :
    ∀ k, u k ≤ (u 0+M/(q-a))*q^k := by
  let A := u 0+M/(q-a)
  have hA : 0 ≤ A := add_nonneg hu0 (div_nonneg hM (sub_pos.mpr haq).le)
  have hMA : M ≤ (q-a)*A := by
    have he : (q-a)*(M/(q-a)) = M := mul_div_cancel₀ M (sub_pos.mpr haq).ne'
    dsimp [A]
    nlinarith [mul_nonneg (sub_pos.mpr haq).le hu0]
  intro k
  induction k with
  | zero => simpa only [pow_zero,mul_one] using le_add_of_nonneg_right (div_nonneg hM (sub_pos.mpr haq).le)
  | succ k ih =>
      have hpow : t^k ≤ q^k := pow_le_pow_left₀ ht htq k
      have hpk : 0 ≤ q^k := pow_nonneg hq.le k
      calc
        u (k+1) ≤ a*u k+M*t^k := hstep k
        _ ≤ a*(A*q^k)+M*q^k := add_le_add (mul_le_mul_of_nonneg_left ih ha) (mul_le_mul_of_nonneg_left hpow hM)
        _ ≤ (A*q)*q^k := by nlinarith [mul_le_mul_of_nonneg_right hMA hpk]
        _ = A*q^(k+1) := by rw [pow_succ]; ring

/-- Actual energy and excess recurrences are iterated in the correct
order. The excess forcing contains the decaying original energy, rather
than an assumed pointwise gradient bound. -/
theorem two_stage_energy_excess_decay (E X : ℕ → ℝ)
    {a b qE qX d t F K : ℝ}
    (hE0 : 0 ≤ E 0) (hX0 : 0 ≤ X 0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hqE : 0 < qE) (hqX : 0 < qX) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (haq : a < qE) (hbq : b < qX) (htE : t ≤ qE) (htX : t ≤ qX)
    (hdq : d*qE ≤ qX) (hF : 0 ≤ F) (hK : 0 ≤ K)
    (hEstep : ∀ k, E (k+1) ≤ a*E k+F*t^k)
    (hXstep : ∀ k, X (k+1) ≤ b*X k+K*d^k*E k+F*t^k) :
    let A := E 0+F/(qE-a)
    let B := X 0+(K*A+F)/(qX-b)
    (∀ k, E k ≤ A*qE^k) ∧ (∀ k, X k ≤ B*qX^k) := by
  dsimp only
  let A := E 0+F/(qE-a)
  have hA : 0 ≤ A := add_nonneg hE0 (div_nonneg hF (sub_pos.mpr haq).le)
  have hEb := geometric_sequence_bound_of_forcing E hE0 ha hqE ht htE haq hF hEstep
  refine ⟨hEb,?_⟩
  apply geometric_sequence_bound_of_forcing X hX0 hb hqX hqX.le le_rfl hbq (by positivity : 0 ≤ K*A+F)
  intro k
  have hpowD : (d*qE)^k ≤ qX^k := pow_le_pow_left₀ (mul_nonneg hd hqE.le) hdq k
  have hpowT : t^k ≤ qX^k := pow_le_pow_left₀ ht htX k
  have henergy := mul_le_mul_of_nonneg_left (hEb k) (mul_nonneg hK (pow_nonneg hd k))
  have hproduct : K*d^k*(A*qE^k) = (K*A)*(d*qE)^k := by rw [mul_pow]; ring
  have herr : K*d^k*E k ≤ (K*A)*qX^k := by
    apply henergy.trans
    rw [hproduct]
    exact mul_le_mul_of_nonneg_left hpowD (mul_nonneg hK hA)
  have hf := mul_le_mul_of_nonneg_left hpowT hF
  nlinarith [hXstep k]

end GaussianTilt.MomentMapLinearDirichlet
