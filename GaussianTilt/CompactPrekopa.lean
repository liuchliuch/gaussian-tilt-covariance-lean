import GaussianTilt.Prekopa
import GaussianTilt.CompactBrascampLieb

/-!
# Prékopa–Leindler with hard support boundaries

The positive supports of the input slices may have discontinuous or vanishing
endpoint values. Compact interior intervals and actual integral convergence
remove the need for a globally continuous density.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Interval Topology
namespace GaussianTilt.Prekopa

/-- Prékopa–Leindler for interval-supported densities with arbitrary endpoint
behavior. Continuity is required only on the positive support interiors. -/
theorem integral_rpow_mul_le_of_interval_support {f g h : ℝ → ℝ} {a b c d α β : ℝ}
    (hab : a < b) (hcd : c < d) (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β = 1)
    (hf : ContinuousOn f (Ioo a b)) (hg : ContinuousOn g (Ioo c d))
    (hh : ContinuousOn h (Ioo (α * a + β * c) (α * b + β * d)))
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hgp : ∀ y ∈ Ioo c d, 0 < g y)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h) (hhn : ∀ z, 0 ≤ h z)
    (hfs : ∀ x ∉ Icc a b, f x = 0) (hgs : ∀ y ∉ Icc c d, g y = 0)
    (hmajor : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d,
      f x ^ α * g y ^ β ≤ h (α * x + β * y)) :
    (∫ x, f x) ^ α * (∫ y, g y) ^ β ≤ ∫ z, h z := by
  let r : ℕ → ℝ := fun n ↦ (1 / 4 : ℝ) * (1 / ((n : ℝ) + 1))
  have hrp : ∀ n, 0 < r n := by intro n; dsimp [r]; positivity
  have hrl : ∀ n, r n ≤ (1 / 4 : ℝ) := by
    intro n
    apply mul_le_of_le_one_right (by norm_num)
    exact (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hr0 : Tendsto r atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
  let u : ℕ → ℝ := fun n ↦ a + (b - a) * r n
  let v : ℕ → ℝ := fun n ↦ b - (b - a) * r n
  let s : ℕ → ℝ := fun n ↦ c + (d - c) * r n
  let t : ℕ → ℝ := fun n ↦ d - (d - c) * r n
  have hu : Tendsto u atTop (𝓝 a) := by simpa [u] using tendsto_const_nhds.add (tendsto_const_nhds.mul hr0)
  have hv : Tendsto v atTop (𝓝 b) := by simpa [v] using tendsto_const_nhds.sub (tendsto_const_nhds.mul hr0)
  have hs : Tendsto s atTop (𝓝 c) := by simpa [s] using tendsto_const_nhds.add (tendsto_const_nhds.mul hr0)
  have ht : Tendsto t atTop (𝓝 d) := by simpa [t] using tendsto_const_nhds.sub (tendsto_const_nhds.mul hr0)
  have hfL := (BrascampLieb.tendsto_intervalIntegral_of_integrable hfi hu hv).rpow_const (Or.inr hα.le)
  have hgL := (BrascampLieb.tendsto_intervalIntegral_of_integrable hgi hs ht).rpow_const (Or.inr hβ.le)
  have hhL : Tendsto (fun n ↦ ∫ z in α * u n + β * s n..α * v n + β * t n, h z) atTop
      (𝓝 (∫ z in α * a + β * c..α * b + β * d, h z)) := BrascampLieb.tendsto_intervalIntegral_of_integrable hhi
    ((tendsto_const_nhds.mul hu).add (tendsto_const_nhds.mul hs))
    ((tendsto_const_nhds.mul hv).add (tendsto_const_nhds.mul ht))
  rw [BrascampLieb.integral_interval_eq_full_of_compact_support hab.le hfs] at hfL
  rw [BrascampLieb.integral_interval_eq_full_of_compact_support hcd.le hgs] at hgL
  have hloc : (∫ x, f x) ^ α * (∫ y, g y) ^ β ≤ ∫ z in α * a + β * c..α * b + β * d, h z := by
    apply le_of_tendsto_of_tendsto (hfL.mul hgL) hhL
    filter_upwards [] with n
    have huf : a < u n ∧ u n < v n ∧ v n < b := by
      dsimp [u, v]
      have hpos := mul_pos (sub_pos.mpr hab) (hrp n)
      have hle := mul_le_mul_of_nonneg_left (hrl n) (sub_pos.mpr hab).le
      exact ⟨by linarith, by linarith, by linarith⟩
    have hsg : c < s n ∧ s n < t n ∧ t n < d := by
      dsimp [s, t]
      have hpos := mul_pos (sub_pos.mpr hcd) (hrp n)
      have hle := mul_le_mul_of_nonneg_left (hrl n) (sub_pos.mpr hcd).le
      exact ⟨by linarith, by linarith, by linarith⟩
    have hsubf : Icc (u n) (v n) ⊆ Ioo a b := fun x hx ↦ ⟨huf.1.trans_le hx.1, hx.2.trans_lt huf.2.2⟩
    have hsubg : Icc (s n) (t n) ⊆ Ioo c d := fun y hy ↦ ⟨hsg.1.trans_le hy.1, hy.2.trans_lt hsg.2.2⟩
    have hsubh : Icc (α * u n + β * s n) (α * v n + β * t n) ⊆
        Ioo (α * a + β * c) (α * b + β * d) := by
      intro z hz
      constructor
      · exact (add_lt_add (mul_lt_mul_of_pos_left huf.1 hα) (mul_lt_mul_of_pos_left hsg.1 hβ)).trans_le hz.1
      · exact hz.2.trans_lt (add_lt_add (mul_lt_mul_of_pos_left huf.2.2 hα) (mul_lt_mul_of_pos_left hsg.2.2 hβ))
    exact integral_rpow_mul_le_continuousOn huf.2.1 hsg.2.1 (hf.mono hsubf) (hg.mono hsubg)
      (hh.mono hsubh) (fun x hx ↦ hfp x (hsubf hx)) (fun y hy ↦ hgp y (hsubg hy))
      hα.le hβ.le hαβ (fun x hx y hy ↦ hmajor x (hsubf hx) y (hsubg hy))
  apply hloc.trans
  rw [intervalIntegral.integral_of_le
    (add_le_add (mul_le_mul_of_nonneg_left hab.le hα.le) (mul_le_mul_of_nonneg_left hcd.le hβ.le))]
  exact setIntegral_le_integral hhi (Filter.Eventually.of_forall hhn)

end GaussianTilt.Prekopa
