import GaussianTilt.MomentMapLinearDirichletRadialEnergyIteration

/-! # Scale-correct interior starting-energy version of the two-stage iteration -/
noncomputable section
set_option maxHeartbeats 3000000
namespace GaussianTilt.MomentMapLinearDirichlet

/-- The initial-radius dependence is retained exactly. This is the form
needed at interior centers whose distance to the boundary tends to zero:
the starting error M and forcing P R^(n+2β) are never replaced by an
unscaled load constant. -/
theorem exists_scale_correct_radial_campanato_constants (n : ℕ) (hn : 0 < n)
    {K D β τ : ℝ} (hK : 0 < K) (hD : 0 ≤ D) (hβ : 0 < β) (hβ1 : β ≤ 1) (hτ : 0 < τ) :
    ∃ ρ θ C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < θ ∧ θ ≤ 1/2 ∧ θ ≤ τ ∧ 0 < C ∧
      ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ (E X : ℝ → ℝ) (M P : ℝ), 0 ≤ M → 0 ≤ P →
      (∀ r,0<r → r≤R → 0≤E r) → (∀ r,0<r → r≤R → 0≤X r) →
      (∀ r,0<r → r≤R → E r≤M) → (∀ r,0<r → r≤R → X r≤E r) →
      (∀ t,0<t → t≤τ → ∀ r,0<r → r≤R →
        E (t*r)≤(K*t^n+K*(D*r^β)^2)*E r+P*r^((n:ℝ)+2*β) ∧
        X (t*r)≤K*t^(n+2)*X r+K*(D*r^β)^2*E r+P*r^((n:ℝ)+2*β)) →
      ∀ k : ℕ, X ((R*ρ)*θ^k) ≤ C*(M+P*R^((n:ℝ)+2*β))*(ρ*θ^k)^((n:ℝ)+β) := by
  obtain ⟨ρ,θ,C,hρ,hρ1,hρ1',hθ,hθ2,hθτ,hC,hIter⟩ :=
    exists_radial_energy_campanato_constants n hn hK hD hβ hβ1 hτ zero_lt_one
  refine ⟨ρ,θ,C,hρ,hρ1,hθ,hθ2,hθτ,hC,?_⟩
  intro R hR hR1 E X M P hM hP hEn hXn hEb hXE hstep
  let E' := fun t => E (R*t)
  let X' := fun t => X (R*t)
  let P' := P*R^((n:ℝ)+2*β)
  have hP' : 0 ≤ P' := mul_nonneg hP (Real.rpow_nonneg hR.le _)
  have hrad {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : R*r ≤ R := by nlinarith
  have hEstep : ∀ t,0<t → t≤τ → ∀ r,0<r → r≤1 →
      E' (t*r)≤(K*t^n+K*(D*r^β)^2)*E' r+P'*r^((n:ℝ)+2*β) ∧
      X' (t*r)≤K*t^(n+2)*X' r+K*(D*r^β)^2*E' r+P'*r^((n:ℝ)+2*β) := by
    intro t ht htτ r hr hr1
    have hh := hstep t ht htτ (R*r) (mul_pos hR hr) (hrad hr hr1)
    have hpow : (R*r)^β ≤ r^β := Real.rpow_le_rpow (mul_pos hR hr).le (by nlinarith) hβ.le
    have hd : (D*(R*r)^β)^2 ≤ (D*r^β)^2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr (mul_le_mul_of_nonneg_left hpow hD)
    have hterm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hK.le)
      (hEn _ (mul_pos hR hr) (hrad hr hr1))
    have hforce : P*(R*r)^((n:ℝ)+2*β)=P'*r^((n:ℝ)+2*β) := by
      rw [Real.mul_rpow hR.le hr.le]
      dsimp [P']
      ring
    have he : t*(R*r)=R*(t*r) := by ring
    rw [he,hforce] at hh
    dsimp [E',X']
    constructor <;> nlinarith [hh.1,hh.2]
  have hb := hIter E' X' M P' hM hP'
    (fun r hr hr1 => hEn _ (mul_pos hR hr) (hrad hr hr1))
    (fun r hr hr1 => hXn _ (mul_pos hR hr) (hrad hr hr1))
    (fun r hr hr1 => hEb _ (mul_pos hR hr) (hrad hr hr1))
    (fun r hr hr1 => hXE _ (mul_pos hR hr) (hrad hr hr1)) hEstep
  intro k
  simpa only [X',P',mul_assoc] using hb k

end GaussianTilt.MomentMapLinearDirichlet
