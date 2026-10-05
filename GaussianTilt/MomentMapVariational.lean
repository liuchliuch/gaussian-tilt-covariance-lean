import GaussianTilt.MomentMapPartition
import GaussianTilt.MomentMapCompactness

/-! # Coercivity of the actual moment-measure variational functional

The source partition is controlled by the target-weighted dual budget.
Together with an elementary logarithm estimate this supplies coercivity
directly for regular targets, without a functional Santaló assumption.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

def dualBudget (q u : E n → ℝ) : ℝ := ∫ y, q y * u y
def dualPartition (K : Set (E n)) (u : E n → ℝ) : ℝ := ∫ x, Real.exp (-fenchel K u x)
def dualObjective (K : Set (E n)) (q u : E n → ℝ) : ℝ :=
  Real.log (dualPartition K u) - dualBudget q u

lemma log_budget_bound (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (n : ℝ) * Real.log (s + 1) ≤ s / 2 +
      ((n : ℝ) + 1) * Real.log (2 * ((n : ℝ) + 1)) := by
  let N : ℝ := (n : ℝ) + 1
  have hN : 0 < N := by dsimp [N]; positivity
  have hL : 0 < 2 * N := by positivity
  have hsp : 0 < s + 1 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hsp hL)
  rw [Real.log_div hsp.ne' hL.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h hN.le
  have heq : N * ((s + 1) / (2 * N)) = (s + 1) / 2 := by field_simp
  have hlog : 0 ≤ Real.log (s + 1) := Real.log_nonneg (by linarith)
  have hN1 : 1 ≤ N := by dsimp [N]; linarith [Nat.cast_nonneg (α := ℝ) n]
  change (n : ℝ) * Real.log (s + 1) ≤ s / 2 + N * Real.log (2 * N)
  nlinarith

theorem dualPartition_polynomial_bound {K : Set (E n)} {u q : E n → ℝ} {R r c : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hu : Continuous u) (huc : ConvexOn ℝ univ u) (hu0 : ∀ y, 0 ≤ u y)
    (huorigin : u 0 = 0) (hq0 : ∀ y, 0 ≤ q y)
    (hi : Integrable (fun y => q y * u y)) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y) :
    let D := (c * (volume (Metric.ball (0 : E n) r)).toReal)⁻¹
    0 < dualPartition K u ∧ dualPartition K u ≤
      (Real.exp 1 * (2 * (D + 1) * ((n : ℝ) + 1) / r) ^ n) * (dualBudget q u + 1) ^ n := by
  dsimp only
  let s := dualBudget q u
  let v := (volume (Metric.ball (0 : E n) r)).toReal
  let D := (c * v)⁻¹
  have hs : 0 ≤ s := integral_nonneg (fun y => mul_nonneg (hq0 y) (hu0 y))
  have hv : 0 < v := ENNReal.toReal_pos
    (Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self hr⟩).ne'
    (ne_top_of_le_ne_top (isCompact_closedBall (0 : E n) r).measure_ne_top
      (measure_mono Metric.ball_subset_closedBall))
  have hD : 0 < D := inv_pos.mpr (mul_pos hc hv)
  have hB : ∀ y ∈ Metric.closedBall (0 : E n) r, u y ≤ D * s := by
    intro y hy
    have h := convex_inner_ball_bound hu huc hu0 hq0 hi hc hr hqlower (le_refl s)
      y (Metric.closedBall_subset_ball (by linarith : r < 2 * r) hy)
    apply (le_abs_self _).trans
    convert h using 1
    dsimp [D, s, v]
    ring
  obtain ⟨hiφ, hp, hb⟩ := fenchel_partition_bounds hK (fun y _ => hu0 y)
    hr (mul_nonneg hD.le hs) hball huorigin hB
  refine ⟨hp, ?_⟩
  have hbase : 2 * ((D * s + 1) * ((n : ℝ) + 1)) / r ≤
      (2 * (D + 1) * ((n : ℝ) + 1) / r) * (s + 1) := by
    apply (div_le_iff₀ hr).mpr
    have hcancel : (2 * (D + 1) * ((n : ℝ) + 1) / r) * (s + 1) * r =
        2 * (D + 1) * ((n : ℝ) + 1) * (s + 1) := by field_simp
    rw [hcancel]
    have hmul := mul_nonneg (show 0 ≤ 2 * ((n : ℝ) + 1) by positivity) (add_nonneg hD.le hs)
    nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * ((D * s + 1) * ((n : ℝ) + 1)) / r) hbase n
  have h := hb.trans (mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg 1))
  simpa only [mul_pow, mul_assoc] using h

/-- Every superlevel of the actual variational functional has a bounded
target-weighted integral. This proves the coercivity input, rather than
assuming it for a maximizing sequence. -/
theorem dualObjective_coercive {K : Set (E n)} {q : E n → ℝ} {R r c : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y) :
    ∃ A : ℝ, ∀ u : E n → ℝ, Continuous u → ConvexOn ℝ univ u →
      (∀ y, 0 ≤ u y) → u 0 = 0 → Integrable (fun y => q y * u y) →
      dualObjective K q u ≤ A - dualBudget q u / 2 := by
  let D := (c * (volume (Metric.ball (0 : E n) r)).toReal)⁻¹
  let C := Real.exp 1 * (2 * (D + 1) * ((n : ℝ) + 1) / r) ^ n
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨Real.log C + ((n : ℝ) + 1) * Real.log (2 * ((n : ℝ) + 1)), ?_⟩
  intro u hu huc hu0 huorigin hi
  have hs : 0 ≤ dualBudget q u := integral_nonneg (fun y => mul_nonneg (hq0 y) (hu0 y))
  obtain ⟨hp, hb⟩ := dualPartition_polynomial_bound hK hball hu huc hu0 huorigin hq0 hi hc hr hqlower
  change dualPartition K u ≤ C * (dualBudget q u + 1) ^ n at hb
  have hlog := Real.log_le_log hp hb
  rw [Real.log_mul hC.ne' (pow_pos (by positivity : 0 < dualBudget q u + 1) n).ne', Real.log_pow] at hlog
  have hsmall := log_budget_bound n hs
  dsimp [dualObjective]
  linarith

end GaussianTilt.MomentMapCoercivity
