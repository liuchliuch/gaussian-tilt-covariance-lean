import GaussianTilt.MomentMapRegularityImprovementNormalization

/-! # Actual adaptive scales and all-radius remainder interpolation -/
noncomputable section
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapRegularity

def adaptiveRadius (R c : ℝ) : ℕ → ℝ
  | 0 => R
  | k+1 => (adaptiveRadius R c k) ^ (1+c)

lemma adaptiveRadius_pos {R c : ℝ} (hR : 0 < R) (k : ℕ) : 0 < adaptiveRadius R c k := by
  induction k with
  | zero => exact hR
  | succ k ih => exact Real.rpow_pos_of_pos ih _

lemma adaptiveRadius_le_initial {R c : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hc : 0 ≤ c) :
    ∀ k, adaptiveRadius R c k ≤ R := by
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [adaptiveRadius,Real.rpow_add (adaptiveRadius_pos hR k),Real.rpow_one]
    exact (mul_le_of_le_one_right (adaptiveRadius_pos hR k).le
      (Real.rpow_le_one (adaptiveRadius_pos hR k).le (ih.trans hR1) hc)).trans ih

lemma adaptiveRadius_succ_le {R c : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hc : 0 ≤ c) (k : ℕ) :
    adaptiveRadius R c (k+1) ≤ R^c*adaptiveRadius R c k := by
  rw [adaptiveRadius,Real.rpow_add (adaptiveRadius_pos hR k),Real.rpow_one]
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (adaptiveRadius_pos hR k).le
    (adaptiveRadius_le_initial hR hR1 hc k) hc) (adaptiveRadius_pos hR k).le).trans_eq (mul_comm _ _)

lemma adaptiveRadius_geometric_bound {R c : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hc : 0 ≤ c) (k : ℕ) :
    adaptiveRadius R c k ≤ R*(R^c)^k := by
  induction k with
  | zero => simp [adaptiveRadius]
  | succ k ih =>
    have hh := adaptiveRadius_succ_le hR hR1 hc k
    apply hh.trans
    calc
      _ ≤ R^c*(R*(R^c)^k) := mul_le_mul_of_nonneg_left ih (Real.rpow_nonneg hR.le _)
      _ = _ := by rw [pow_succ]; ring

lemma adaptiveRadius_tendsto_zero {R c : ℝ} (hR : 0 < R) (hR1 : R < 1) (hc : 0 < c) :
    Tendsto (adaptiveRadius R c) atTop (𝓝 0) := by
  have hq : 0 ≤ R^c := Real.rpow_nonneg hR.le _
  have hq1 : R^c < 1 := Real.rpow_lt_one hR.le hR1 hc
  have ht := (show Tendsto (fun _ : ℕ => R) atTop (𝓝 R) from tendsto_const_nhds).mul
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1)
  apply squeeze_zero (fun k => (adaptiveRadius_pos hR k).le)
    (adaptiveRadius_geometric_bound hR hR1.le hc.le)
  simpa only [mul_zero] using ht

lemma adaptiveRadius_two_step {R c : ℝ} (hR : 0 < R) (k : ℕ) :
    adaptiveRadius R c (k+2) = (adaptiveRadius R c k)^((1+c)^2) := by
  rw [adaptiveRadius,adaptiveRadius,← Real.rpow_mul (adaptiveRadius_pos hR k).le]
  congr 1
  ring

/-- Every sufficiently small radius lies between two successive adaptive
scales. This is derived from the actual recurrence and convergence to zero. -/
lemma exists_adaptiveRadius_gap {R c s : ℝ} (hR : 0 < R) (hR1 : R < 1) (hc : 0 < c)
    (hs : 0 < s) (hsR : s ≤ adaptiveRadius R c 1) :
    ∃ k : ℕ, adaptiveRadius R c (k+2) < s ∧ s ≤ adaptiveRadius R c (k+1) := by
  have hsmall : ∃ k, adaptiveRadius R c (k+1) < s := by
    obtain ⟨k,hk⟩ := ((adaptiveRadius_tendsto_zero hR hR1 hc).eventually (eventually_lt_nhds hs)).exists
    have hq := Real.rpow_le_one hR.le hR1.le hc.le
    exact ⟨k,(adaptiveRadius_succ_le hR hR1.le hc.le k).trans_lt
      ((mul_le_of_le_one_left (adaptiveRadius_pos hR k).le hq).trans_lt hk)⟩
  have hn0 : Nat.find hsmall ≠ 0 := by
    intro hz
    have hh := Nat.find_spec hsmall
    rw [hz] at hh
    exact hh.not_ge hsR
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨k,?_,?_⟩
  · have hh := Nat.find_spec hsmall
    simpa only [hk,Nat.succ_eq_add_one,Nat.add_assoc] using hh
  · have hh := Nat.find_min hsmall (show k < Nat.find hsmall by omega)
    exact le_of_not_gt hh

/-- Numeric interpolation preserves a positive quadratic remainder order
across the actual gaps between adaptive scales. -/
lemma adaptive_gap_remainder_bound {r s c α β A B : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlower : r^((1+c)^2) ≤ s) (hupper : s ≤ r^(1+c))
    (hdensity : (1+c)^2*(2+β) ≤ 2+α)
    (htaylor : 1 ≤ (1+c)*(1-β)) :
    A*r^(2+α)+B*s^3/r ≤ (A+B)*s^(2+β) := by
  have hd : r^(2+α) ≤ s^(2+β) := by
    calc
      _ ≤ r^((1+c)^2*(2+β)) := Real.rpow_le_rpow_of_exponent_ge hr hr1 hdensity
      _ = (r^((1+c)^2))^(2+β) := Real.rpow_mul hr.le _ _
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hr.le _) hlower (by linarith)
  have ht : s^(1-β) ≤ r := by
    calc
      _ ≤ (r^(1+c))^(1-β) := Real.rpow_le_rpow hs.le hupper (sub_nonneg.mpr hβ1)
      _ = r^((1+c)*(1-β)) := (Real.rpow_mul hr.le _ _).symm
      _ ≤ r^1 := Real.rpow_le_rpow_of_exponent_ge hr hr1 htaylor
      _ = r := Real.rpow_one _
  have hdiv : s^3/r ≤ s^(2+β) := by
    apply (div_le_iff₀ hr).mpr
    have hp := mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hs.le (2+β))
    have he : s^(2+β)*s^(1-β)=s^3 := by
      rw [← Real.rpow_add hs]
      norm_num [show (2+β)+(1-β)=(3:ℝ) by ring]
    rw [he] at hp
    exact hp
  have hd' := mul_le_mul_of_nonneg_left hd hA
  have ht' := mul_le_mul_of_nonneg_left hdiv hB
  convert add_le_add hd' ht' using 1 <;> ring

end GaussianTilt.MomentMapRegularity
