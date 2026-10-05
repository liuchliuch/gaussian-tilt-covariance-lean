import GaussianTilt.MomentMapLinearDirichletRadialEnergyIteration

/-! # Full forcing-exponent Campanato gain from genuine bounded gradient energy

After the initial weak regularity pass has made the true gradient bounded,
E(r) ≤ M rⁿ permits the full excess exponent n+2β, for every β<1.
No repeated loss of one half of the Hölder exponent is used.
-/
noncomputable section
set_option maxHeartbeats 3000000
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapLinearDirichlet

theorem exists_radial_bounded_energy_full_exponent (n : ℕ)
    {K D β τ R : ℝ} (hK : 0 < K) (hD : 0 ≤ D)
    (hβ : 0 < β) (hβ1 : β < 1) (hτ : 0 < τ) (hR : 0 < R) :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1/2 ∧ θ ≤ τ ∧ 0 < C ∧
      ∀ (E X : ℝ → ℝ) (M P : ℝ), 0 ≤ M → 0 ≤ P →
      (∀ r, 0<r → r≤R → 0≤X r) →
      (∀ r, 0<r → r≤R → E r≤M*r^n) →
      (X R≤E R) →
      (∀ t,0<t → t≤τ → ∀ r,0<r → r≤R →
        X (t*r)≤K*t^(n+2)*X r+(K*D^2)*r^(2*β)*E r+P*r^((n:ℝ)+2*β)) →
      ∀ k : ℕ, X (R*θ^k) ≤ C*(M+P)*(R*θ^k)^((n:ℝ)+2*β) := by
  have he : 0 < 2-2*β := by linarith
  obtain ⟨θ,hθ,hθr,hθ1,hsmall⟩ := exists_small_radius_holder_bound
    (D := 2*K) he (by norm_num : (0:ℝ)<1) (lt_min hτ (by norm_num : (0:ℝ)<1/2))
  have hθ2 : θ ≤ 1/2 := hθr.trans (min_le_right _ _)
  have hθτ : θ ≤ τ := hθr.trans (min_le_left _ _)
  let p := (n:ℝ)+2*β
  let q := θ^p
  have hq : 0 < q := Real.rpow_pos_of_pos hθ _
  have hd : 0 < q-q/2 := by linarith
  have hRp : 0 < R^p := Real.rpow_pos_of_pos hR _
  have hcoeff : K*θ^(n+2) ≤ q/2 := by
    have hp : θ^(n+2) = q*θ^(2-2*β) := by
      dsimp only [q,p]
      rw [← Real.rpow_add hθ]
      have heq : (n:ℝ)+2*β+(2-2*β) = ((n+2:ℕ):ℝ) := by push_cast; ring
      rw [heq,Real.rpow_natCast]
    rw [hp]
    nlinarith [mul_le_mul_of_nonneg_left hsmall hq.le]
  let C := R^n/R^p+(K*D^2+1)/(q-q/2)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨θ,C,hθ,hθ2,hθτ,hC,?_⟩
  intro E X M P hM hP hXn hE hXE hstep
  let Q := M+P
  have hQ : 0 ≤ Q := add_nonneg hM hP
  let r := fun k : ℕ => R*θ^k
  have hr (k : ℕ) : 0 < r k := mul_pos hR (pow_pos hθ _)
  have hrR (k : ℕ) : r k ≤ R := by
    have hh := pow_le_one₀ hθ.le hθ1 (n:=k)
    dsimp only [r]; nlinarith
  have hsucc (k : ℕ) : r (k+1)=θ*r k := by dsimp only [r]; rw [pow_succ]; ring
  have hfactor (k : ℕ) : (r k)^p=R^p*q^k := by
    dsimp only [r,q]
    rw [Real.mul_rpow hR.le (pow_nonneg hθ.le _),← Real.rpow_pow_comm hθ.le]
  have hpow (k : ℕ) : (r k)^(2*β)*(r k)^n=(r k)^p := by
    rw [← Real.rpow_natCast,← Real.rpow_add (hr k)]
    congr 1
    dsimp only [p]; ring
  have hN : K*D^2*M+P ≤ (K*D^2+1)*Q := by
    dsimp only [Q]
    nlinarith [mul_nonneg (mul_nonneg hK.le (sq_nonneg D)) hP]
  have hs : ∀ k, X (r (k+1)) ≤ (q/2)*X (r k)+
      ((K*D^2+1)*Q*R^p)*q^k := by
    intro k
    rw [hsucc]
    have hh := hstep θ hθ hθτ (r k) (hr k) (hrR k)
    have hfirst := mul_le_mul_of_nonneg_right hcoeff (hXn _ (hr k) (hrR k))
    have henergy := mul_le_mul_of_nonneg_left (hE _ (hr k) (hrR k))
      (show 0 ≤ (K*D^2)*(r k)^(2*β) by positivity)
    have heq : (K*D^2)*(r k)^(2*β)*(M*(r k)^n)=(K*D^2*M)*(r k)^p := by
      calc
        _ = (K*D^2*M)*((r k)^(2*β)*(r k)^n) := by ring
        _ = _ := by rw [hpow]
    rw [heq] at henergy
    have hload := mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg (hr k).le p)
    have heq2 : (K*D^2+1)*Q*(r k)^p=((K*D^2+1)*Q*R^p)*q^k := by rw [hfactor]; ring
    rw [heq2] at hload
    nlinarith
  have hz := geometric_sequence_bound_of_forcing (fun k => X (r k))
    (hXn _ (hr 0) (hrR 0)) (by positivity : 0 ≤ q/2) hq hq.le le_rfl
    (half_lt_self hq) (by positivity : 0 ≤ (K*D^2+1)*Q*R^p) hs
  have hX0 : X (r 0) ≤ Q*R^n := by
    have hh := hXE.trans (hE R hR le_rfl)
    have hMQ : M ≤ Q := le_add_of_nonneg_right hP
    simpa only [r,pow_zero,mul_one] using hh.trans
      (mul_le_mul_of_nonneg_right hMQ (pow_nonneg hR.le n))
  have hconstant : Q*R^n+((K*D^2+1)*Q*R^p)/(q-q/2) = C*Q*R^p := by
    dsimp only [C]
    field_simp
    <;> ring
  intro k
  apply (hz k).trans
  have hh := mul_le_mul_of_nonneg_right (add_le_add_right hX0 (((K*D^2+1)*Q*R^p)/(q-q/2)))
    (pow_nonneg hq.le k)
  rw [hconstant] at hh
  exact hh.trans_eq (by rw [hfactor]; ring)

end GaussianTilt.MomentMapLinearDirichlet
