import GaussianTilt.MomentMapLinearDirichletEnergySmallScale
import GaussianTilt.MomentMapLinearDirichletEnergyUniformConstants

/-! # Actual radial energy/excess recurrences yield uniform Campanato powers -/
noncomputable section
set_option maxHeartbeats 4000000
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapLinearDirichlet

lemma exists_small_radius_holder_bound {D β ε R : ℝ} (hβ : 0 < β) (hε : 0 < ε) (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ r ≤ 1 ∧ D*r^β ≤ ε := by
  have hc : Continuous (fun r : ℝ => D*r^β) := continuous_const.mul (Real.continuous_rpow_const hβ.le)
  have hU : {r : ℝ | D*r^β<ε} ∈ 𝓝 (0:ℝ) :=
    (isOpen_lt hc continuous_const).mem_nhds (by simpa only [mem_setOf_eq,Real.zero_rpow hβ.ne',mul_zero] using hε)
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hU
  let r := min (δ/2) (min R (1:ℝ))
  have hr : 0 < r := lt_min (half_pos hδ) (lt_min hR zero_lt_one)
  refine ⟨r,hr,(min_le_right _ _).trans (min_le_left _ _),(min_le_right _ _).trans (min_le_right _ _),?_⟩
  exact (hδU (show r ∈ Metric.ball 0 δ by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hr]
    exact (min_le_left _ _).trans_lt (half_lt_self hδ))).le

/-- Constants are selected before the energy functions and the load.
A genuine coefficient oscillation D r^β is small at the constructed initial
radius; both actual recurrences then give r^(n+β) excess at every scale. -/
theorem exists_radial_energy_campanato_constants (n : ℕ) (hn : 0 < n)
    {K D β τ R₀ : ℝ} (hK : 0 < K) (hD : 0 ≤ D) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hτ : 0 < τ) (hR₀ : 0 < R₀) :
    ∃ r₀ θ C : ℝ, 0 < r₀ ∧ r₀ ≤ R₀ ∧ r₀ ≤ 1 ∧ 0 < θ ∧ θ ≤ 1/2 ∧ θ ≤ τ ∧ 0 < C ∧
      ∀ (E X : ℝ → ℝ) (M P : ℝ), 0 ≤ M → 0 ≤ P →
      (∀ r,0<r → r≤R₀ → 0≤E r) → (∀ r,0<r → r≤R₀ → 0≤X r) →
      (∀ r,0<r → r≤R₀ → E r≤M) → (∀ r,0<r → r≤R₀ → X r≤E r) →
      (∀ t,0<t → t≤τ → ∀ r,0<r → r≤R₀ →
        E (t*r)≤(K*t^n+K*(D*r^β)^2)*E r+P*r^((n:ℝ)+2*β) ∧
        X (t*r)≤K*t^(n+2)*X r+K*(D*r^β)^2*E r+P*r^((n:ℝ)+2*β)) →
      ∀ k : ℕ, X (r₀*θ^k) ≤ C*(M+P)*(r₀*θ^k)^((n:ℝ)+β) := by
  obtain ⟨θ,ε,hθ,hθ2,hθτ,hε,hEc,hXc⟩ := exists_energy_excess_contraction_constants_below n hK hβ hβ1 hτ
  obtain ⟨r₀,hr₀,hr₀R,hr₀1,hsmall⟩ := exists_small_radius_holder_bound (D := D) hβ hε hR₀
  have hθ1 : θ < 1 := hθ2.trans_lt (by norm_num)
  obtain ⟨hqE,hqE1,hqX,hqX1,htE,htX,hdq⟩ := energy_excess_power_parameters hn hθ hθ1 hβ hβ1
  let qE := θ^((n:ℝ)-β/2)
  let qX := θ^((n:ℝ)+β)
  let A := 1+1/(qE-qE/2)
  let B := 1+(K*D^2*A+1)/(qX-qX/2)
  let C := B/r₀^((n:ℝ)+β)
  have hqe : 0 < qE := hqE
  have hqx : 0 < qX := hqX
  have hdenE : 0 < qE-qE/2 := by linarith
  have hdenX : 0 < qX-qX/2 := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := div_pos hB (Real.rpow_pos_of_pos hr₀ _)
  refine ⟨r₀,θ,C,hr₀,hr₀R,hr₀1,hθ,hθ2,hθτ,hC,?_⟩
  intro E X M P hM hP hEn hXn hEb hXE hstep
  let r := fun k : ℕ => r₀*θ^k
  let Q := M+P
  have hQ : 0 ≤ Q := add_nonneg hM hP
  have hr (k : ℕ) : 0 < r k := mul_pos hr₀ (pow_pos hθ _)
  have hrr₀ (k : ℕ) : r k ≤ r₀ := by
    have hp := pow_le_one₀ hθ.le hθ1.le (n := k)
    dsimp [r]; nlinarith
  have hrR (k : ℕ) : r k ≤ R₀ := (hrr₀ k).trans hr₀R
  have hsucc (k : ℕ) : r (k+1)=θ*r k := by dsimp [r]; rw [pow_succ]; ring
  have hfactor (k : ℕ) (s : ℝ) : (r k)^s = r₀^s*(θ^s)^k := by
    dsimp only [r]
    rw [Real.mul_rpow hr₀.le (pow_nonneg hθ.le _),← Real.rpow_pow_comm hθ.le]
  have hforce (k : ℕ) : P*(r k)^((n:ℝ)+2*β) ≤ Q*(θ^((n:ℝ)+2*β))^k := by
    rw [hfactor]
    have hp : r₀^((n:ℝ)+2*β) ≤ 1 := Real.rpow_le_one hr₀.le hr₀1 (by positivity)
    have hPQ : P*r₀^((n:ℝ)+2*β) ≤ Q := (mul_le_of_le_one_right hP hp).trans (le_add_of_nonneg_left hM)
    have ht := mul_le_mul_of_nonneg_right hPQ (pow_nonneg (Real.rpow_nonneg hθ.le ((n:ℝ)+2*β)) k)
    nlinarith
  have hdelta (k : ℕ) : (D*(r k)^β)^2 ≤ ε^2 := by
    have hd : D*(r k)^β ≤ ε := (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hr k).le (hrr₀ k) hβ.le) hD).trans hsmall
    exact (sq_le_sq₀ (by positivity) hε.le).mpr hd
  have hdeltaScale (k : ℕ) : (D*(r k)^β)^2 ≤ D^2*(θ^(2*β))^k := by
    have hp : r₀^(2*β) ≤ 1 := Real.rpow_le_one hr₀.le hr₀1 (by positivity)
    have he : ((r k)^β)^2 = (r k)^(2*β) := by
      rw [← Real.rpow_two,← Real.rpow_mul (hr k).le]
      congr 1
      ring
    rw [mul_pow,he,hfactor]
    have ht := mul_le_mul_of_nonneg_right hp (pow_nonneg (Real.rpow_nonneg hθ.le (2*β)) k)
    nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg D)]
  have hXc' : K*θ^(n+2) ≤ qX/2 := by
    have he : θ^((n:ℝ)+2)=θ^(n+2) := by norm_cast
    rwa [he] at hXc
  have hEstep : ∀ k, E (r (k+1)) ≤ (qE/2)*E (r k)+(1*Q)*(θ^((n:ℝ)+2*β))^k := by
    intro k
    rw [hsucc]
    have hh := (hstep θ hθ hθτ (r k) (hr k) (hrR k)).1
    have hd := mul_le_mul_of_nonneg_left (hdelta k) hK.le
    have hcoeff : K*θ^n+K*(D*(r k)^β)^2 ≤ qE/2 := by linarith
    have hc := mul_le_mul_of_nonneg_right hcoeff (hEn _ (hr k) (hrR k))
    nlinarith [hforce k]
  have hXstep : ∀ k, X (r (k+1)) ≤ (qX/2)*X (r k)+(K*D^2)*(θ^(2*β))^k*E (r k)+(1*Q)*(θ^((n:ℝ)+2*β))^k := by
    intro k
    rw [hsucc]
    have hh := (hstep θ hθ hθτ (r k) (hr k) (hrR k)).2
    have hd := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hdeltaScale k) hK.le) (hEn _ (hr k) (hrR k))
    have hc := mul_le_mul_of_nonneg_right hXc' (hXn _ (hr k) (hrR k))
    nlinarith [hforce k]
  have hE0 : E (r 0) ≤ Q := (hEb _ (hr 0) (hrR 0)).trans (le_add_of_nonneg_right hP)
  have hX0 : X (r 0) ≤ Q := (hXE _ (hr 0) (hrR 0)).trans hE0
  have hh := two_stage_energy_excess_decay_with_data_factor (fun k => E (r k)) (fun k => X (r k))
    (hEn _ (hr 0) (hrR 0)) (hXn _ (hr 0) (hrR 0)) hQ hE0 hX0
    (by positivity : 0 ≤ qE/2) (by positivity : 0 ≤ qX/2) hqE hqX
    (Real.rpow_nonneg hθ.le _) (Real.rpow_nonneg hθ.le _) (half_lt_self hqE) (half_lt_self hqX)
    htE htX hdq (by norm_num : (0:ℝ)≤1) (by positivity : 0 ≤ K*D^2) hEstep hXstep
  intro k
  change X (r k) ≤ C*Q*(r k)^((n:ℝ)+β)
  have hx : X (r k) ≤ B*Q*qX^k := hh.2 k
  apply hx.trans_eq
  rw [hfactor]
  dsimp only [C,qX]
  field_simp

end GaussianTilt.MomentMapLinearDirichlet
