import GaussianTilt.LowerPaperResults
import GaussianTilt.CubeModerateBounds

/-! # Uniform specialization of moderate-deviation parameters to actual slices -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace GaussianTilt.UniformModerate

/-- The deficit per transverse coordinate at the original slice scale. -/
def relativeDeficit (d : ℕ) (s : ℝ) : ℝ :=
  2 * (1 + s) * (d : ℝ) ^ (-(2 / 5 : ℝ))

lemma relativeDeficit_eq {d : ℕ} (hd : 0 < d) (s : ℝ) :
    relativeDeficit d s = 2 * deviationScale d * (1 + s) / (d : ℝ) := by
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  have hpow : (d : ℝ) ^ (3 / 5 : ℝ) / d = (d : ℝ) ^ (-(2 / 5 : ℝ)) := by
    conv_lhs => rhs; rw [← Real.rpow_one (d : ℝ)]
    rw [← Real.rpow_sub hp]
    norm_num
  dsimp [relativeDeficit, deviationScale]
  rw [← hpow]
  ring

lemma relativeDeficit_pos {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s) :
    0 < relativeDeficit d s := by
  dsimp [relativeDeficit]
  exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)

lemma rate_power {d : ℕ} (hd : 0 < d) (s : ℝ) (k : ℕ) :
    (d : ℝ) * relativeDeficit d s ^ k =
      (2 * (1 + s)) ^ k * (d : ℝ) ^ (1 + (-(2 / 5 : ℝ)) * k) := by
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  rw [relativeDeficit, mul_pow, ← Real.rpow_mul_natCast hp.le]
  calc
    (d : ℝ) * ((2 * (1 + s)) ^ k * (d : ℝ) ^ ((-(2 / 5 : ℝ)) * k)) =
        (2 * (1 + s)) ^ k * ((d : ℝ) ^ (1 : ℝ) * (d : ℝ) ^ ((-(2 / 5 : ℝ)) * k)) := by
          rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hp]

lemma rate_square {d : ℕ} (hd : 0 < d) (s : ℝ) :
    (d : ℝ) * relativeDeficit d s ^ 2 = 4 * (1 + s) ^ 2 * (d : ℝ) ^ (1 / 5 : ℝ) := by
  rw [rate_power hd s 2, show 1 + (-(2 / 5 : ℝ)) * (2 : ℕ) = (1 / 5 : ℝ) by norm_num, mul_pow]
  norm_num

lemma rate_cube {d : ℕ} (hd : 0 < d) (s : ℝ) :
    (d : ℝ) * relativeDeficit d s ^ 3 = 8 * (1 + s) ^ 3 * (d : ℝ) ^ (-(1 / 5 : ℝ)) := by
  rw [rate_power hd s 3, show 1 + (-(2 / 5 : ℝ)) * (3 : ℕ) = (-(1 / 5 : ℝ)) by norm_num, mul_pow]
  norm_num

lemma rate_four {d : ℕ} (hd : 0 < d) (s : ℝ) :
    (d : ℝ) * Real.sqrt d * relativeDeficit d s ^ 4 =
      16 * (1 + s) ^ 4 * (d : ℝ) ^ (-(1 / 10 : ℝ)) := by
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  calc
    (d : ℝ) * Real.sqrt d * relativeDeficit d s ^ 4 =
        Real.sqrt d * ((d : ℝ) * relativeDeficit d s ^ 4) := by ring
    _ = Real.sqrt d * ((2 * (1 + s)) ^ 4 * (d : ℝ) ^ (1 + (-(2 / 5 : ℝ)) * (4 : ℕ))) := by rw [rate_power hd]
    _ = 16 * (1 + s) ^ 4 * ((d : ℝ) ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-(3 / 5 : ℝ))) := by
      rw [Real.sqrt_eq_rpow]; norm_num; ring
    _ = _ := by rw [← Real.rpow_add hp]; norm_num

lemma relativeDeficit_mul_sqrt {d : ℕ} (hd : 0 < d) (s : ℝ) :
    relativeDeficit d s * Real.sqrt d = 2 * (1 + s) * (d : ℝ) ^ (1 / 10 : ℝ) := by
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  rw [relativeDeficit, Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hp]
  norm_num

/-- Every finite-theorem admissibility condition holds eventually, uniformly
throughout each fixed bounded nonnegative slice interval. -/
theorem eventually_admissible {s₀ ε : ℝ} (hs₀ : 0 ≤ s₀) (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop, 0 < d ∧ ∀ s ∈ Icc (0 : ℝ) s₀,
      0 < relativeDeficit d s ∧ relativeDeficit d s ≤ ε ∧
      ε⁻¹ ≤ (d : ℝ) * relativeDeficit d s ^ 2 ∧
      (d : ℝ) * relativeDeficit d s ^ 3 ≤ ε ∧
      (d : ℝ) * Real.sqrt d * relativeDeficit d s ^ 4 ≤ ε := by
  have hcast : Tendsto (fun d : ℕ ↦ (d : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hδ : Tendsto (fun d : ℕ ↦ 2 * (1 + s₀) * (d : ℝ) ^ (-(2 / 5 : ℝ))) atTop (𝓝 0) := by
    convert ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp hcast).const_mul (2 * (1 + s₀)) using 1 <;> simp
  have h3 : Tendsto (fun d : ℕ ↦ 8 * (1 + s₀) ^ 3 * (d : ℝ) ^ (-(1 / 5 : ℝ))) atTop (𝓝 0) := by
    convert ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp hcast).const_mul (8 * (1 + s₀) ^ 3) using 1 <;> simp
  have h4 : Tendsto (fun d : ℕ ↦ 16 * (1 + s₀) ^ 4 * (d : ℝ) ^ (-(1 / 10 : ℝ))) atTop (𝓝 0) := by
    convert ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hcast).const_mul (16 * (1 + s₀) ^ 4) using 1 <;> simp
  have h2 : Tendsto (fun d : ℕ ↦ 4 * (d : ℝ) ^ (1 / 5 : ℝ)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp hcast).const_mul_atTop (by norm_num)
  filter_upwards [hδ.eventually (gt_mem_nhds hε), h3.eventually (gt_mem_nhds hε),
    h4.eventually (gt_mem_nhds hε), h2.eventually_ge_atTop (ε⁻¹), eventually_gt_atTop 0] with d hdδ hd3 hd4 hd2 hd
  refine ⟨hd, ?_⟩
  intro s hs
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : 0 ≤ 1 + s := by linarith [hs.1]
  have h1le : 1 + s ≤ 1 + s₀ := by linarith [hs.2]
  refine ⟨relativeDeficit_pos hd hs.1, ?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (by linarith : 2 * (1 + s) ≤ 2 * (1 + s₀))
      (Real.rpow_nonneg hp.le _)).trans hdδ.le
  · rw [rate_square hd]
    apply hd2.trans
    have hs2 : 1 ≤ (1 + s) ^ 2 := by nlinarith [hs.1]
    have h := mul_le_mul_of_nonneg_right hs2 (Real.rpow_nonneg hp.le (1 / 5 : ℝ))
    nlinarith
  · rw [rate_cube hd]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1 h1le 3) (by norm_num))
      (Real.rpow_nonneg hp.le _)).trans hd3.le
  · rw [rate_four hd]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1 h1le 4) (by norm_num))
      (Real.rpow_nonneg hp.le _)).trans hd4.le

lemma cubeSlice_eq_deficit_event {d : ℕ} (hd : 0 < d) (s : ℝ) :
    LowerProbability.cubeSlice d (deviationScale d) s =
      (LowerProbability.cubeLaw d).real
        {x | (d : ℝ) * relativeDeficit d s ≤ ModerateDeviations.cubeDeficit d x} := by
  have hp : (d : ℝ) ≠ 0 := by positivity
  have hthreshold : (d : ℝ) * relativeDeficit d s = 2 * deviationScale d * (1 + s) := by
    rw [relativeDeficit_eq hd]
    field_simp
  unfold LowerProbability.cubeSlice LowerProbability.sliceProbability
  congr 1
  ext x
  rw [hthreshold]
  have hsum : ModerateDeviations.cubeDeficit d x = -(∑ i, ((x i) ^ 2 - 1)) := by
    unfold ModerateDeviations.cubeDeficit ModerateDeviations.coordinateDeficit
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [Set.mem_setOf_eq]
  rw [hsum]
  constructor <;> intro h <;> linarith

lemma prefactor_eq {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s) (K E : ℝ) :
    K * E / (relativeDeficit d s * Real.sqrt d) =
      (K / (2 * (1 + s))) * (d : ℝ) ^ (-(1 / 10 : ℝ)) * E := by
  rw [relativeDeficit_mul_sqrt hd, Real.rpow_neg (Nat.cast_nonneg d)]
  field_simp

/-- Original Lemma 4.4 at the exact cube and deviation scale, including its
uniform d^(-1/10) prefactor. The finite probability theorem is proved in the
imported module, rather than supplied as an assumption. -/
theorem original4_4 {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ d : ℕ in atTop, ∀ s ∈ Icc (0 : ℝ) s₀,
      c * (d : ℝ) ^ (-(1 / 10 : ℝ)) *
          Real.exp (-(5 / 2 : ℝ) * (d : ℝ) ^ (1 / 5 : ℝ) * (1 + s) ^ 2) ≤
        LowerProbability.cubeSlice d (deviationScale d) s ∧
      LowerProbability.cubeSlice d (deviationScale d) s ≤
        C * (d : ℝ) ^ (-(1 / 10 : ℝ)) *
          Real.exp (-(5 / 2 : ℝ) * (d : ℝ) ^ (1 / 5 : ℝ) * (1 + s) ^ 2) := by
  obtain ⟨kLo, kHi, ε, hkLo, hkHi, hε, hfinite⟩ :=
    CubeModerateBounds.cube_moderate_deviation_bounds
  refine ⟨kLo / (2 * (1 + s₀)), kHi / 2, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_admissible hs₀.le hε] with d hd
  intro s hs
  obtain ⟨hδ, hδε, hlarge, h3, h4⟩ := hd.2 s hs
  have h := hfinite d (relativeDeficit d s) hd.1 hδ hδε hlarge h3 h4
  rw [← cubeSlice_eq_deficit_event hd.1] at h
  have he : -(5 / 8 : ℝ) * (d : ℝ) * relativeDeficit d s ^ 2 =
      -(5 / 2 : ℝ) * (d : ℝ) ^ (1 / 5 : ℝ) * (1 + s) ^ 2 := by
    rw [mul_assoc, rate_square hd.1]
    ring
  rw [he, prefactor_eq hd.1 hs.1, prefactor_eq hd.1 hs.1] at h
  have hden : 0 < 2 * (1 + s) := by linarith [hs.1]
  constructor
  · apply le_trans _ h.1
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    exact div_le_div_of_nonneg_left hkLo.le hden (by linarith [hs.2])
  · apply h.2.trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    exact div_le_div_of_nonneg_left hkHi.le (by norm_num) (by linarith [hs.1])

end GaussianTilt.UniformModerate
