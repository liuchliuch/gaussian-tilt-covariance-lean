import GaussianTilt.LowerScales

/-!
# Completing the genuine lower-bound construction from its axial scale

This module performs the deterministic precision selection and the actual
measure/covariance argument. Its only remaining asymptotic input is the raw
axial variance upper bound, supplied by the local slice comparison pipeline.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Real
open scoped BigOperators Topology Matrix.Norms.L2Operator

namespace GaussianTilt
namespace LowerConclusion
open LowerProbability LowerMarginal LowerFubini LowerScales

/-- Any diagonal covariance entry is bounded by the Euclidean operator norm. -/
lemma matrix_diagonal_le_opNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    A i i ≤ ‖A‖ := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have h := (PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin n) ℝ).symm (A.mulVec e)) i).trans
    (Matrix.l2_opNorm_mulVec A e)
  have he : ‖e‖ = 1 := by simp [e]
  rw [he, mul_one] at h
  have hentry : ((EuclideanSpace.equiv (Fin n) ℝ).symm (A.mulVec e)) i = A i i := by
    change (A.mulVec (Pi.single i 1)) i = A i i
    simp [Matrix.mulVec_single, Matrix.col]
  rw [hentry, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

lemma deviationScale_mul_precisionScale {d : ℕ} (hd : 0 < d) :
    deviationScale d * (d : ℝ) ^ (2 / 5 : ℝ) = d := by
  rw [deviationScale, ← Real.rpow_add (by exact_mod_cast hd : (0 : ℝ) < d)]
  norm_num

/-- A fixed precision multiple works in every sufficiently large dimension.
All hypotheses of the proved actual-body covariance bound are discharged here. -/
theorem eventually_tilt_covariance_lower_of_axial_upper {B : ℝ} (hB : 0 < B)
    (hb : ∀ᶠ d : ℕ in atTop,
      rawAxialVariance d (deviationScale d) ≤ B / (d : ℝ) ^ (2 / 5 : ℝ)) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᶠ d : ℕ in atTop,
      ∀ i₀ : Fin d,
        0 < A / (d : ℝ) ^ (2 / 5 : ℝ) ∧
        c * (d : ℝ) ^ (2 / 5 : ℝ) ≤
          Reference.covariance (Reference.gaussianTilt
            (Reference.uniform (euclideanBody (deviationScale d) i₀))
              (A / (d : ℝ) ^ (2 / 5 : ℝ))) 0 0 := by
  let A : ℝ := 1 + 3 * (3 + 2 * Real.sqrt B) / meanDeficitConstant
  have hA1 : 1 ≤ A := by
    exact le_add_of_nonneg_right (div_nonneg (by positivity) meanDeficitConstant_pos.le)
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hA1
  have hchoose : 3 + 2 * Real.sqrt B ≤ meanDeficitConstant * A / 3 := by
    dsimp [A]
    have hc := meanDeficitConstant_pos
    field_simp
    nlinarith
  have htend : Tendsto (fun d : ℕ ↦ A / (d : ℝ) ^ (2 / 5 : ℝ)) atTop (𝓝 0) := by
    have h := (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop).const_mul A
    simpa only [mul_zero, div_eq_mul_inv] using h
  have htSmall := htend.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hrate : ∀ᶠ d : ℕ in atTop, (9 / 2 : ℝ) * Real.log 2 ≤ (d : ℝ) ^ (1 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop _)
  refine ⟨A, windowConstant / A, hA, div_pos windowConstant_pos hA, ?_⟩
  filter_upwards [hb, eventually_rawBody_parameters, eventually_rawTransverseVariance_bounds,
    htSmall, hrate, eventually_gt_atTop 0] with d hbd hpar had hts hrs hd
  intro i₀
  let R : ℝ := (d : ℝ) ^ (2 / 5 : ℝ)
  let t : ℝ := A / R
  let a := rawTransverseVariance (deviationScale d) i₀
  let b := rawAxialVariance d (deviationScale d)
  let L := Real.sqrt (R / A)
  have hR : 0 < R := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have ht : 0 < t := div_pos hA hR
  have ha : 0 < a := rawTransverseVariance_pos hpar.1 hpar.2 i₀
  have hbp : 0 < b := rawAxialVariance_pos hpar.1 hpar.2
  have hL : 0 < L := Real.sqrt_pos.mpr (div_pos hR hA)
  have hLsq : L ^ 2 = R / A := Real.sq_sqrt (div_pos hR hA).le
  have htL : t * L ^ 2 = 1 := by rw [hLsq]; dsimp [t]; field_simp
  have hspan : Real.sqrt b * L ≤ Real.sqrt B := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg b) hL.le) (Real.sqrt_nonneg B)).mp
    rw [mul_pow, Real.sq_sqrt hbp.le, Real.sq_sqrt hB.le, hLsq]
    have hbR : b * R ≤ B := (le_div_iff₀ hR).mp hbd
    calc
      b * (R / A) = b * R / A := by ring
      _ ≤ B / A := div_le_div_of_nonneg_right hbR hA.le
      _ ≤ B := div_le_self hB.le hA1
  have hτ : t / a ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg ht.le ha.le, (div_le_one ha).mpr ?_⟩
    exact hts.le.trans (had i₀).1
  have hdt : (d : ℝ) * t = A * deviationScale d := by
    rw [show (d : ℝ) = deviationScale d * R from (deviationScale_mul_precisionScale hd).symm]
    dsimp [t]
    field_simp
  have hdef : 2 * deviationScale d * (1 + Real.sqrt b * L) + deviationScale d ≤
      (d : ℝ) * meanDeficitConstant * (t / a) := by
    calc
      _ ≤ (3 + 2 * Real.sqrt B) * deviationScale d := by nlinarith [hpar.1]
      _ ≤ (meanDeficitConstant * A / 3) * deviationScale d :=
        mul_le_mul_of_nonneg_right hchoose hpar.1.le
      _ = (meanDeficitConstant * A * deviationScale d) / 3 := by ring
      _ ≤ (meanDeficitConstant * A * deviationScale d) / a :=
        div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg meanDeficitConstant_pos.le hA.le) hpar.1.le) ha (had i₀).2
      _ = meanDeficitConstant * ((d : ℝ) * t) / a := by rw [hdt]; ring
      _ = (d : ℝ) * meanDeficitConstant * (t / a) := by ring
  have hcov := euclideanBody_tilt_covariance_lower hpar.1 hpar.2 i₀ ht hτ hL htL hdef
    (by rwa [deviationScale_sq_div hd])
  refine ⟨ht, ?_⟩
  convert hcov using 1
  dsimp [t, R]
  field_simp

/-- The original independent lower-bound statement follows from the actual
raw axial upper scale. No abstract covariance or marginal model is substituted. -/
theorem lowerBound_of_axial_upper {B : ℝ} (hB : 0 < B)
    (hb : ∀ᶠ d : ℕ in atTop,
      rawAxialVariance d (deviationScale d) ≤ B / (d : ℝ) ^ (2 / 5 : ℝ)) :
    Reference.LowerBound := by
  obtain ⟨A, c, hA, hc, hcov⟩ := eventually_tilt_covariance_lower_of_axial_upper hB hb
  have hev := hcov.and (eventually_rawBody_parameters.and (eventually_gt_atTop 0))
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp hev
  refine ⟨c / (2 : ℝ) ^ (2 / 5 : ℝ), by positivity, d₀ + 1, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  have hdd₀ : d₀ ≤ d := by omega
  obtain ⟨hcovd, hpar, hd⟩ := hd₀ d hdd₀
  let i₀ : Fin d := ⟨0, hd⟩
  obtain ⟨ht, hentry⟩ := hcovd i₀
  refine ⟨euclideanBody (deviationScale d) i₀,
    A / (d : ℝ) ^ (2 / 5 : ℝ), euclideanBody_convexBody hpar.1 hpar.2 i₀,
    euclideanBody_unconditional i₀, euclideanBody_isotropic hpar.1 hpar.2 i₀, ht, ?_⟩
  have hdim : ((d + 1 : ℕ) : ℝ) ^ (2 / 5 : ℝ) ≤
      (2 : ℝ) ^ (2 / 5 : ℝ) * (d : ℝ) ^ (2 / 5 : ℝ) := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    calc
      _ ≤ ((2 : ℝ) * d) ^ (2 / 5 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
        push_cast
        linarith
      _ = _ := Real.mul_rpow (by norm_num) (by positivity)
  calc
    _ ≤ (c / (2 : ℝ) ^ (2 / 5 : ℝ)) *
        ((2 : ℝ) ^ (2 / 5 : ℝ) * (d : ℝ) ^ (2 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left hdim (by positivity)
    _ = c * (d : ℝ) ^ (2 / 5 : ℝ) := by field_simp
    _ ≤ Reference.covariance (Reference.gaussianTilt
        (Reference.uniform (euclideanBody (deviationScale d) i₀))
          (A / (d : ℝ) ^ (2 / 5 : ℝ))) 0 0 := hentry
    _ ≤ _ := matrix_diagonal_le_opNorm _ _

/-- End-to-end lower-bound pipeline from the sole remaining local comparison
input. The geometric construction, raw scales, precision, Gaussian marginal,
and Euclidean covariance norm are all proved rather than assumed. -/
theorem lowerBound_of_local_comparison {c C k K : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hk : 0 < k) (hK : 0 < K)
    (hlocal : ∀ᶠ d : ℕ in atTop, LocalSliceComparison d c C k K) :
    Reference.LowerBound := by
  obtain ⟨c', C', hc', hC', hscale⟩ :=
    eventually_rawAxialVariance_bounds_of_local hc hC hk hK hlocal
  exact lowerBound_of_axial_upper hC' (hscale.mono fun _ hd ↦ hd.2)


/-- Original Lemma 4.9's uniform-in-precision implication, with the actual raw
axial upper bound as its only still-external scale input. -/
theorem eventually_tilt_slice_acceptance_of_axial_upper {B : ℝ} (hB : 0 < B)
    (hb : ∀ᶠ d : ℕ in atTop,
      rawAxialVariance d (deviationScale d) ≤ B / (d : ℝ) ^ (2 / 5 : ℝ)) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A ≥ A₀, ∀ᶠ d : ℕ in atTop,
      ∀ i₀ : Fin d, ∀ z : ℝ,
        |z| ≤ (Real.sqrt (A / (d : ℝ) ^ (2 / 5 : ℝ)))⁻¹ →
        1 - Real.exp (-2 * deviationScale d ^ 2 / (9 * (d : ℝ))) ≤
          tiltedSlice d ((A / (d : ℝ) ^ (2 / 5 : ℝ)) /
            rawTransverseVariance (deviationScale d) i₀) (deviationScale d)
              (rawAxialVariance d (deviationScale d)) z ∧
        (1 / 2 : ℝ) ≤ 1 - Real.exp (-2 * deviationScale d ^ 2 / (9 * (d : ℝ))) := by
  let A₀ : ℝ := 1 + 3 * (3 + 2 * Real.sqrt B) / meanDeficitConstant
  have hA₀1 : 1 ≤ A₀ :=
    le_add_of_nonneg_right (div_nonneg (by positivity) meanDeficitConstant_pos.le)
  have hchoose₀ : 3 + 2 * Real.sqrt B ≤ meanDeficitConstant * A₀ / 3 := by
    dsimp [A₀]
    have hc := meanDeficitConstant_pos
    field_simp
    nlinarith
  refine ⟨A₀, lt_of_lt_of_le (by norm_num) hA₀1, ?_⟩
  intro A hAA₀
  have hA1 : 1 ≤ A := hA₀1.trans hAA₀
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hA1
  have hchoose : 3 + 2 * Real.sqrt B ≤ meanDeficitConstant * A / 3 :=
    hchoose₀.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hAA₀ meanDeficitConstant_pos.le) (by norm_num))
  have htend : Tendsto (fun d : ℕ ↦ A / (d : ℝ) ^ (2 / 5 : ℝ)) atTop (𝓝 0) := by
    have h := (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop).const_mul A
    simpa only [mul_zero, div_eq_mul_inv] using h
  have htSmall := htend.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hrate : ∀ᶠ d : ℕ in atTop, (9 / 2 : ℝ) * Real.log 2 ≤ (d : ℝ) ^ (1 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop _)
  filter_upwards [hb, eventually_rawBody_parameters, eventually_rawTransverseVariance_bounds,
    htSmall, hrate, eventually_gt_atTop 0] with d hbd hpar had hts hrs hd
  intro i₀ z hz
  let R : ℝ := (d : ℝ) ^ (2 / 5 : ℝ)
  let t : ℝ := A / R
  let a := rawTransverseVariance (deviationScale d) i₀
  let b := rawAxialVariance d (deviationScale d)
  let L := Real.sqrt (R / A)
  have hR : 0 < R := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have ht : 0 < t := div_pos hA hR
  have ha : 0 < a := rawTransverseVariance_pos hpar.1 hpar.2 i₀
  have hbp : 0 < b := rawAxialVariance_pos hpar.1 hpar.2
  have hL : 0 < L := Real.sqrt_pos.mpr (div_pos hR hA)
  have hLsq : L ^ 2 = R / A := Real.sq_sqrt (div_pos hR hA).le
  have htL : t * L ^ 2 = 1 := by rw [hLsq]; dsimp [t]; field_simp
  have hspan : Real.sqrt b * L ≤ Real.sqrt B := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg b) hL.le) (Real.sqrt_nonneg B)).mp
    rw [mul_pow, Real.sq_sqrt hbp.le, Real.sq_sqrt hB.le, hLsq]
    have hbR : b * R ≤ B := (le_div_iff₀ hR).mp hbd
    calc
      b * (R / A) = b * R / A := by ring
      _ ≤ B / A := div_le_div_of_nonneg_right hbR hA.le
      _ ≤ B := div_le_self hB.le hA1
  have hτ : t / a ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg ht.le ha.le, (div_le_one ha).mpr ?_⟩
    exact hts.le.trans (had i₀).1
  have hdt : (d : ℝ) * t = A * deviationScale d := by
    rw [show (d : ℝ) = deviationScale d * R from (deviationScale_mul_precisionScale hd).symm]
    dsimp [t]
    field_simp
  have hdef : 2 * deviationScale d * (1 + Real.sqrt b * L) + deviationScale d ≤
      (d : ℝ) * meanDeficitConstant * (t / a) := by
    calc
      _ ≤ (3 + 2 * Real.sqrt B) * deviationScale d := by nlinarith [hpar.1]
      _ ≤ (meanDeficitConstant * A / 3) * deviationScale d :=
        mul_le_mul_of_nonneg_right hchoose hpar.1.le
      _ = (meanDeficitConstant * A * deviationScale d) / 3 := by ring
      _ ≤ (meanDeficitConstant * A * deviationScale d) / a :=
        div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg meanDeficitConstant_pos.le hA.le) hpar.1.le) ha (had i₀).2
      _ = meanDeficitConstant * ((d : ℝ) * t) / a := by rw [hdt]; ring
      _ = (d : ℝ) * meanDeficitConstant * (t / a) := by ring
  have hLinv : L = (Real.sqrt t)⁻¹ := by
    have hmul : Real.sqrt t * L = 1 := by
      rw [show L = Real.sqrt (R / A) from rfl, ← Real.sqrt_mul ht.le]
      have hh : t * (R / A) = 1 := by dsimp [t]; field_simp
      rw [hh, Real.sqrt_one]
    have hn := (Real.sqrt_pos.mpr ht).ne'
    field_simp
    nlinarith
  have hzL : |z| ≤ L := by rw [hLinv]; exact hz
  have hdefz : 2 * deviationScale d * (1 + Real.sqrt b * |z|) + deviationScale d ≤
      (d : ℝ) * meanDeficitConstant * (t / a) := by
    have hh := mul_le_mul_of_nonneg_left hzL (Real.sqrt_nonneg b)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * deviationScale d from mul_nonneg (by norm_num) hpar.1.le)
    nlinarith
  refine ⟨tiltedSlice_acceptance_of_deficit d hτ hpar.1.le hdefz, ?_⟩
  have hr : (9 / 2 : ℝ) * Real.log 2 ≤ deviationScale d ^ 2 / (d : ℝ) := by
    rwa [deviationScale_sq_div hd]
  have he : Real.exp (-2 * deviationScale d ^ 2 / (9 * (d : ℝ))) ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ Real.exp (-Real.log 2) := by
        apply Real.exp_le_exp.mpr
        have hid : -2 * deviationScale d ^ 2 / (9 * (d : ℝ)) =
            -(2 / 9 : ℝ) * (deviationScale d ^ 2 / (d : ℝ)) := by ring
        rw [hid]
        linarith
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  linarith

end LowerConclusion
end GaussianTilt
