import GaussianTilt.LowerFubini
import GaussianTilt.LowerPaperResults
import GaussianTilt.ModerateDeviations
import GaussianTilt.SliceMoments

/-!
# Genuine covariance-scale estimates for the lower-bound body
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Real
open scoped BigOperators Topology

namespace GaussianTilt
namespace LowerScales
open LowerProbability LowerFubini

lemma deviationScale_div_dimension_tendsto_zero :
    Tendsto (fun d : ℕ ↦ deviationScale d / (d : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  rw [deviationScale]
  conv_rhs => rhs; rw [← Real.rpow_one (d : ℝ)]
  rw [← Real.rpow_sub hp]
  norm_num

lemma sqrt_div_dimension_tendsto_zero :
    Tendsto (fun d : ℕ ↦ Real.sqrt (d : ℝ) / (d : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.sqrt_eq_rpow]
  conv_rhs => rhs; rw [← Real.rpow_one (d : ℝ)]
  rw [← Real.rpow_sub hp]
  norm_num

/-- A subexponential lower bound for an actual positive-width cube slice. This
uses the proved change-of-measure bound, not a moderate-deviation asymptotic. -/
theorem eventually_cubeSlice_one_lower : ∀ᶠ d : ℕ in atTop,
    Real.exp (-(d : ℝ) / 36) ≤ cubeSlice d (deviationScale d) 1 := by
  let u : ℕ → ℝ := fun d ↦ deviationScale d / (d : ℝ)
  let v : ℕ → ℝ := fun d ↦ Real.sqrt (d : ℝ) / (d : ℝ)
  let T : ℕ → ℝ := fun d ↦ (4 * u d + 3 * v d) / meanDeficitConstant
  have hu : Tendsto u atTop (𝓝 0) := deviationScale_div_dimension_tendsto_zero
  have hv : Tendsto v atTop (𝓝 0) := sqrt_div_dimension_tendsto_zero
  have hs : Tendsto (fun d ↦ 4 * u d + 3 * v d) atTop (𝓝 0) := by
    convert (hu.const_mul 4).add (hv.const_mul 3) using 1 <;> norm_num
  have hT : Tendsto T atTop (𝓝 0) := by
    convert hs.div_const meanDeficitConstant using 1 <;> simp [T]
  have hi : Tendsto (fun d : ℕ ↦ (d : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hc : Tendsto (fun d ↦ 10 * (u d) ^ 2 + 6 * T d * v d + 4 * (T d) ^ 3 +
      Real.log (4 / 3) / (d : ℝ)) atTop (𝓝 0) := by
    convert (((hu.pow 2).const_mul 10).add ((hT.const_mul 6).mul hv)).add
      ((hT.pow 3).const_mul 4) |>.add (hi.const_mul (Real.log (4 / 3))) using 1 <;>
      simp [div_eq_mul_inv]
  have hs' := hs.eventually (eventually_lt_nhds (show 0 < meanDeficitConstant / 2 by
    exact half_pos meanDeficitConstant_pos))
  have hc' := hc.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 36))
  filter_upwards [hs', hc', eventually_gt_atTop 0] with d hsd hcd hd
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  have hsmall : 2 * deviationScale d * (1 + (1 : ℝ)) + 3 * Real.sqrt d ≤
      meanDeficitConstant * (d : ℝ) / 2 := by
    have hm := mul_le_mul_of_nonneg_right hsd.le hp.le
    dsimp [u, v] at hm
    field_simp at hm ⊢
    nlinarith
  have htail := ModerateDeviations.cubeSlice_lower_tail hd (deviationScale_pos hd).le
    (s := 1) (by norm_num) hsmall
  have hTd : T d = (2 * deviationScale d * (1 + (1 : ℝ)) + 3 * Real.sqrt d) /
      ((d : ℝ) * meanDeficitConstant) := by
    dsimp [T, u, v]
    ring
  rw [← hTd] at htail
  let cost : ℝ := (5 / 2 : ℝ) * (deviationScale d ^ 2 / d) * (1 + (1 : ℝ)) ^ 2 +
    6 * T d * Real.sqrt d + 4 * (d : ℝ) * (T d) ^ 3
  have hcost : cost + Real.log (4 / 3) ≤ (d : ℝ) / 36 := by
    have hm := mul_le_mul_of_nonneg_right hcd.le hp.le
    dsimp [u, v] at hm
    dsimp [cost]
    field_simp at hm ⊢
    nlinarith
  calc
    Real.exp (-(d : ℝ) / 36) ≤ Real.exp (-cost - Real.log (4 / 3)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = (3 / 4 : ℝ) * Real.exp (-cost) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
      ring
    _ ≤ cubeSlice d (deviationScale d) 1 := by
      convert htail using 1
      congr 2
      dsimp [cost]
      ring

/-- The actual raw body's low-energy proportion vanishes enough to prevent
transverse collapse, using only the proved exponential lower denominator. -/
theorem eventually_rawUniform_lowEnergy_le_half : ∀ᶠ d : ℕ in atTop,
    (rawUniform d (deviationScale d)).real
      {p | transverseEnergy p ≤ (d : ℝ) / 2} ≤ (1 / 2 : ℝ) := by
  have hlim : Tendsto (fun d : ℕ ↦ (d : ℝ) * Real.exp (-(d : ℝ) / 36)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (1 / 36)
      (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    convert h using 1
    funext d
    simp only [Function.comp_apply, Real.rpow_one]
    congr 1
    ring
  have hsmall := hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_cubeSlice_one_lower, eventually_rawBody_parameters,
    hsmall, eventually_gt_atTop 0] with d hslice hparam hsm hd
  have hΔ := hparam.1
  have hroom := hparam.2
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hΔ1 : 1 ≤ deviationScale d := by
    exact Real.one_le_rpow hd1 (by norm_num)
  have hfrac : (d : ℝ) / deviationScale d ≤ d := by
    exact div_le_self (by positivity) hΔ1
  have hsm' : (d : ℝ) / deviationScale d * Real.exp (-(d : ℝ) / 36) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right hfrac (Real.exp_nonneg _)).trans hsm.le
  let C := ((volume (Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3)))⁻¹ ^ d).toReal
  let V := volume.real (rawBodyWith d (deviationScale d))
  let B := volume.real (rawBodyWith d (deviationScale d) ∩
    {p | transverseEnergy p ≤ (d : ℝ) / 2})
  have hC : 0 < C := cubeVolumeFactor_pos d
  have hV : 0 < V := ENNReal.toReal_pos (rawBodyWith_volume_pos d hroom).ne'
    (rawBodyWith_isCompact d hΔ).measure_ne_top
  have hden : Real.exp (-(d : ℝ) / 36) ≤ C * V :=
    hslice.trans (rawBody_normalized_volume_lower d hΔ)
  have hnum : C * B ≤ ((d : ℝ) / deviationScale d) * Real.exp (-(d : ℝ) / 18) :=
    rawBody_lowEnergy_volume_bound hd hΔ
  have hexp : Real.exp (-(d : ℝ) / 18) =
      Real.exp (-(d : ℝ) / 36) * Real.exp (-(d : ℝ) / 36) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, ← mul_assoc] at hnum
  have hnum' : C * B ≤ (1 / 2 : ℝ) * (C * V) :=
    hnum.trans ((mul_le_mul_of_nonneg_right hsm' (Real.exp_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hden (by norm_num)))
  have hB : B ≤ (1 / 2 : ℝ) * V := by nlinarith
  rw [rawUniform_real_apply d (deviationScale d)
    (measurableSet_le (continuous_transverseEnergy d).measurable measurable_const)]
  exact (div_le_iff₀ hV).mpr (by nlinarith)

/-- The complete transverse assertion of original Lemma 4.7, for the actual
uniform raw body at the exact paper scale. -/
theorem eventually_rawTransverseVariance_bounds : ∀ᶠ d : ℕ in atTop,
    ∀ i : Fin d, (1 / 4 : ℝ) ≤ rawTransverseVariance (deviationScale d) i ∧
      rawTransverseVariance (deviationScale d) i ≤ 3 := by
  filter_upwards [eventually_rawBody_parameters, eventually_rawUniform_lowEnergy_le_half]
    with d hpar hbad
  intro i
  exact ⟨rawTransverseVariance_lower_of_lowEnergy hpar.1 hpar.2 i hbad,
    rawTransverseVariance_le_three hpar.1 hpar.2 i⟩

lemma sqrt_div_deviationScale_tendsto_zero :
    Tendsto (fun d : ℕ ↦ Real.sqrt (d : ℝ) / deviationScale d) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.sqrt_eq_rpow, deviationScale, ← Real.rpow_sub hp]
  norm_num

/-- A genuine Gaussian-rate lower bound for the central slice. The exact
prefactor is not needed to make the far tail negligible in the moment proof. -/
theorem eventually_cubeSlice_zero_lower_rate : ∀ᶠ d : ℕ in atTop,
    Real.exp (-3 * (deviationScale d ^ 2 / (d : ℝ))) ≤ cubeSlice d (deviationScale d) 0 := by
  let u : ℕ → ℝ := fun d ↦ deviationScale d / (d : ℝ)
  let v : ℕ → ℝ := fun d ↦ Real.sqrt (d : ℝ) / (d : ℝ)
  let w : ℕ → ℝ := fun d ↦ Real.sqrt (d : ℝ) / deviationScale d
  have hu : Tendsto u atTop (𝓝 0) := deviationScale_div_dimension_tendsto_zero
  have hv : Tendsto v atTop (𝓝 0) := sqrt_div_dimension_tendsto_zero
  have hw : Tendsto w atTop (𝓝 0) := sqrt_div_deviationScale_tendsto_zero
  have hs : Tendsto (fun d ↦ 2 * u d + 3 * v d) atTop (𝓝 0) := by
    convert (hu.const_mul 2).add (hv.const_mul 3) using 1 <;> norm_num
  have h1 : Tendsto (fun d ↦ 6 / meanDeficitConstant * (2 * w d + 3 * (w d) ^ 2))
      atTop (𝓝 0) := by
    convert ((hw.const_mul 2).add ((hw.pow 2).const_mul 3)).const_mul
      (6 / meanDeficitConstant) using 1 <;> norm_num
  have h2 : Tendsto (fun d ↦ 4 / meanDeficitConstant ^ 3 * u d * (2 + 3 * w d) ^ 3)
      atTop (𝓝 0) := by
    convert (hu.const_mul (4 / meanDeficitConstant ^ 3)).mul
      ((tendsto_const_nhds.add (hw.const_mul 3)).pow 3) using 1 <;> norm_num
  have h3 : Tendsto (fun d ↦ Real.log (4 / 3) * (w d) ^ 2) atTop (𝓝 0) := by
    convert (hw.pow 2).const_mul (Real.log (4 / 3)) using 1 <;> norm_num
  have hc : Tendsto (fun d ↦ (5 / 2 : ℝ) +
      6 / meanDeficitConstant * (2 * w d + 3 * (w d) ^ 2) +
      4 / meanDeficitConstant ^ 3 * u d * (2 + 3 * w d) ^ 3 +
      Real.log (4 / 3) * (w d) ^ 2) atTop (𝓝 (5 / 2)) := by
    convert ((tendsto_const_nhds.add h1).add h2).add h3 using 1 <;> norm_num
  have hs' := hs.eventually (eventually_lt_nhds (half_pos meanDeficitConstant_pos))
  have hc' := hc.eventually (eventually_lt_nhds (by norm_num : (5 / 2 : ℝ) < 3))
  filter_upwards [hs', hc', eventually_gt_atTop 0] with d hsd hcd hd
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  have hΔ := deviationScale_pos hd
  have hsqrt : (Real.sqrt (d : ℝ)) ^ 2 = d := Real.sq_sqrt hp.le
  have hsmall : 2 * deviationScale d * (1 + (0 : ℝ)) + 3 * Real.sqrt d ≤
      meanDeficitConstant * (d : ℝ) / 2 := by
    have hm := mul_le_mul_of_nonneg_right hsd.le hp.le
    dsimp [u, v] at hm
    field_simp at hm ⊢
    nlinarith
  have ht := ModerateDeviations.cubeSlice_lower_tail hd hΔ.le (s := 0) (by norm_num) hsmall
  let T := (2 * deviationScale d + 3 * Real.sqrt (d : ℝ)) /
    ((d : ℝ) * meanDeficitConstant)
  let cost := (5 / 2 : ℝ) * (deviationScale d ^ 2 / d) +
    6 * T * Real.sqrt d + 4 * (d : ℝ) * T ^ 3
  have hid : (cost + Real.log (4 / 3)) / (deviationScale d ^ 2 / (d : ℝ)) =
      (5 / 2 : ℝ) + 6 / meanDeficitConstant * (2 * w d + 3 * (w d) ^ 2) +
      4 / meanDeficitConstant ^ 3 * u d * (2 + 3 * w d) ^ 3 +
      Real.log (4 / 3) * (w d) ^ 2 := by
    dsimp [cost, T, u, w]
    field_simp
    simp only [hsqrt]
    ring
  have hcost : cost + Real.log (4 / 3) ≤ 3 * (deviationScale d ^ 2 / (d : ℝ)) := by
    apply (div_le_iff₀ (by positivity : 0 < deviationScale d ^ 2 / (d : ℝ))).mp
    rw [hid]
    exact hcd.le
  calc
    Real.exp (-3 * (deviationScale d ^ 2 / (d : ℝ))) ≤
        Real.exp (-cost - Real.log (4 / 3)) := Real.exp_le_exp.mpr (by linarith)
    _ = (3 / 4 : ℝ) * Real.exp (-cost) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
      ring
    _ ≤ cubeSlice d (deviationScale d) 0 := by
      convert ht using 1
      congr 2
      dsimp [cost, T]
      ring

/-- The exact local comparison still required from the probability argument.
All comparisons involve the genuine cube law and the exact deviation scale. -/
def LocalSliceComparison (d : ℕ) (c C k K : ℝ) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 2,
    c * cubeSlice d (deviationScale d) 0 *
        Real.exp (-K * (deviationScale d ^ 2 / (d : ℝ)) * s) ≤
      cubeSlice d (deviationScale d) s ∧
    cubeSlice d (deviationScale d) s ≤
      C * cubeSlice d (deviationScale d) 0 *
        Real.exp (-k * (deviationScale d ^ 2 / (d : ℝ)) * s)

/-- The global tail and the central Gaussian-rate lower bound are already
proved. Thus a local comparison on `[0,2]` supplies the full envelopes needed
for every slice moment. -/
theorem eventually_cubeSlice_envelopes_of_local {c C k K : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hk : 0 < k) (hK : 0 < K)
    (hlocal : ∀ᶠ d : ℕ in atTop, LocalSliceComparison d c C k K) :
    ∀ᶠ d : ℕ in atTop,
      0 < deviationScale d ^ 2 / (d : ℝ) ∧
      0 < cubeSlice d (deviationScale d) 0 ∧
      (∀ s ∈ Icc (0 : ℝ) (1 / (deviationScale d ^ 2 / (d : ℝ))),
        (c * Real.exp (-K)) * cubeSlice d (deviationScale d) 0 ≤
          cubeSlice d (deviationScale d) s) ∧
      (∀ s, 0 ≤ s → cubeSlice d (deviationScale d) s ≤
        (C + 1) * cubeSlice d (deviationScale d) 0 *
          Real.exp (-(min k (8 / 9)) * (deviationScale d ^ 2 / (d : ℝ)) * s)) := by
  have hg : ∀ᶠ d : ℕ in atTop, 1 ≤ (d : ℝ) ^ (1 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop 1)
  filter_upwards [hlocal, eventually_cubeSlice_zero_lower_rate, hg, eventually_gt_atTop 0]
    with d hloc hzero hrate hd
  let r := deviationScale d ^ 2 / (d : ℝ)
  have hr : 0 < r := div_pos (sq_pos_of_pos (deviationScale_pos hd)) (by exact_mod_cast hd)
  have hr1 : 1 ≤ r := by simpa only [r, deviationScale_sq_div hd] using hrate
  have hm : 0 < cubeSlice d (deviationScale d) 0 := lt_of_lt_of_le (Real.exp_pos _) hzero
  refine ⟨hr, hm, ?_, ?_⟩
  · apply SliceMoments.core_lower_of_local_exponential hr (s₀ := 2) (by
      have hh : 1 / r ≤ 1 := (div_le_one hr).mpr hr1
      linarith) hK.le (mul_nonneg hc.le hm.le)
    exact fun s hs ↦ (hloc s hs).1
  · apply SliceMoments.global_envelope_of_local_and_gaussian (s₀ := 2) (k := 8 / 9)
      hr.le (by norm_num) (by norm_num) (le_min hk.le (by norm_num)) (min_le_right _ _)
    · intro s hs
      have hcmp : Real.exp (-k * r * s) ≤ Real.exp (-(min k (8 / 9)) * r * s) := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_right (min_le_left k (8 / 9))
          (mul_nonneg hr.le hs.1)
        nlinarith
      calc
        _ ≤ C * cubeSlice d (deviationScale d) 0 * Real.exp (-k * r * s) := (hloc s hs).2
        _ ≤ (C + 1) * cubeSlice d (deviationScale d) 0 * Real.exp (-k * r * s) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_left hcmp (by positivity)
    · intro s hs
      exact cubeSlice_global_tail d (deviationScale_pos hd).le hs
    · calc
        _ ≤ Real.exp (-3 * r) := by
          apply Real.exp_le_exp.mpr
          have hmin : min k (8 / 9 : ℝ) ≤ 8 / 9 := min_le_right _ _
          nlinarith [mul_le_mul_of_nonneg_left hmin hr.le]
        _ ≤ cubeSlice d (deviationScale d) 0 := hzero
        _ ≤ (C + 1) * cubeSlice d (deviationScale d) 0 := by nlinarith

/-- The real-variable implication of Lemmas 4.6 and 4.7, with only the genuine
local probability comparison left as an explicit dependency. -/
theorem eventually_rawAxialVariance_bounds_of_local {c C k K : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hk : 0 < k) (hK : 0 < K)
    (hlocal : ∀ᶠ d : ℕ in atTop, LocalSliceComparison d c C k K) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧ ∀ᶠ d : ℕ in atTop,
      c' / (d : ℝ) ^ (2 / 5 : ℝ) ≤ rawAxialVariance d (deviationScale d) ∧
      rawAxialVariance d (deviationScale d) ≤ C' / (d : ℝ) ^ (2 / 5 : ℝ) := by
  let c₀ := c * Real.exp (-K)
  let C₀ := C + 1
  let k₀ := min k (8 / 9 : ℝ)
  have hc₀ : 0 < c₀ := mul_pos hc (Real.exp_pos _)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; linarith
  have hk₀ : 0 < k₀ := lt_min hk (by norm_num)
  refine ⟨c₀ * k₀ / (3 * C₀), 2 * C₀ / (c₀ * k₀ ^ 3), by positivity, by positivity, ?_⟩
  filter_upwards [eventually_cubeSlice_envelopes_of_local hc hC hk hK hlocal,
    eventually_rawBody_parameters, eventually_gt_atTop 0] with d he hpar hd
  have h := SliceMoments.rawAxialVariance_bounds_of_envelope hpar.1 hpar.2
    he.1 hc₀ hC₀ hk₀ he.2.1 he.2.2.1 he.2.2.2
  have hrpow : (deviationScale d ^ 2 / (d : ℝ)) ^ 2 = (d : ℝ) ^ (2 / 5 : ℝ) := by
    rw [deviationScale_sq_div hd, ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ d)]
    norm_num
  rwa [hrpow] at h

/-- The complete analytic implication of Lemma 4.6 for every nonnegative integer
moment (in particular the paper's `0` and `2`), with local comparison as the sole
remaining probabilistic input. -/
theorem eventually_sliceMoment_bounds_of_local {c C k K : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hk : 0 < k) (hK : 0 < K)
    (hlocal : ∀ᶠ d : ℕ in atTop, LocalSliceComparison d c C k K) (n : ℕ) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧ ∀ᶠ d : ℕ in atTop,
      c' * cubeSlice d (deviationScale d) 0 /
          (deviationScale d ^ 2 / (d : ℝ)) ^ (n + 1) ≤
        SliceMoments.moment n (cubeSlice d (deviationScale d)) ∧
      SliceMoments.moment n (cubeSlice d (deviationScale d)) ≤
        C' * cubeSlice d (deviationScale d) 0 /
          (deviationScale d ^ 2 / (d : ℝ)) ^ (n + 1) := by
  let c₀ := c * Real.exp (-K)
  let C₀ := C + 1
  let k₀ := min k (8 / 9 : ℝ)
  have hc₀ : 0 < c₀ := mul_pos hc (Real.exp_pos _)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; linarith
  have hk₀ : 0 < k₀ := lt_min hk (by norm_num)
  refine ⟨c₀ / (n + 1 : ℝ), C₀ * (n.factorial : ℝ) / k₀ ^ (n + 1),
    by positivity, by positivity, ?_⟩
  filter_upwards [eventually_cubeSlice_envelopes_of_local hc hC hk hK hlocal,
    eventually_rawBody_parameters] with d he hpar
  have hl := SliceMoments.moment_lower he.1 (SliceMoments.cube_moment_integrable hpar.1 n)
    (fun s _ ↦ cubeSlice_nonneg d (deviationScale d) s) he.2.2.1
  have hu := SliceMoments.moment_upper he.1 hk₀ (SliceMoments.cube_moment_integrable hpar.1 n)
    he.2.2.2
  constructor
  · convert hl using 1
    dsimp [c₀]
    field_simp
  · convert hu using 1
    dsimp [C₀]
    rw [mul_pow]
    field_simp

end LowerScales
end GaussianTilt
