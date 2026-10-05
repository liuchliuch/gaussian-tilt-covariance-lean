import GaussianTilt.LocalComparison
import GaussianTilt.LowerConclusion

/-!
# Closed original lower-bound statements

The local probability comparison is proved in `LocalComparison`; every theorem
here has the actual paper parameters and no unproved analytic hypotheses.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Real
open scoped BigOperators Topology Matrix.Norms.L2Operator

namespace GaussianTilt
open LowerProbability LowerFubini LowerMarginal LowerScales LowerConclusion

/-- Original Theorem 4.1, equivalently Theorem 1.1(ii), with the exact independent
Euclidean uniform-body/Gaussian-tilt specification. -/
theorem original4_1 : Reference.LowerBound := by
  obtain ⟨c, C, hc, hC, hlocal⟩ := UniformModerate.exists_eventually_localSliceComparison
  exact lowerBound_of_local_comparison hc hC (by norm_num) (by norm_num) hlocal

/-- Original Lemma 4.6, in fact proved for every nonnegative integer moment. -/
theorem original4_6 (ℓ : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      c * cubeSlice d (deviationScale d) 0 /
          (deviationScale d ^ 2 / (d : ℝ)) ^ (ℓ + 1) ≤
        (∫ s in Ici (0 : ℝ), s ^ ℓ * cubeSlice d (deviationScale d) s) ∧
      (∫ s in Ici (0 : ℝ), s ^ ℓ * cubeSlice d (deviationScale d) s) ≤
        C * cubeSlice d (deviationScale d) 0 /
          (deviationScale d ^ 2 / (d : ℝ)) ^ (ℓ + 1) := by
  obtain ⟨c, C, hc, hC, hlocal⟩ := UniformModerate.exists_eventually_localSliceComparison
  exact eventually_sliceMoment_bounds_of_local hc hC (by norm_num) (by norm_num) hlocal ℓ

/-- Original Lemma 4.7: the genuine transverse and axial raw covariance scales,
including the exact ratio of actual half-line slice integrals. -/
theorem original4_7 : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ d : ℕ in atTop,
    (∀ i : Fin d, (1 / 4 : ℝ) ≤ rawTransverseVariance (deviationScale d) i ∧
      rawTransverseVariance (deviationScale d) i ≤ 3) ∧
    rawAxialVariance d (deviationScale d) =
      (∫ s in Ici (0 : ℝ), s ^ 2 * cubeSlice d (deviationScale d) s) /
        (∫ s in Ici (0 : ℝ), cubeSlice d (deviationScale d) s) ∧
    c / (d : ℝ) ^ (2 / 5 : ℝ) ≤ rawAxialVariance d (deviationScale d) ∧
      rawAxialVariance d (deviationScale d) ≤ C / (d : ℝ) ^ (2 / 5 : ℝ) := by
  obtain ⟨c, C, hc, hC, hlocal⟩ := UniformModerate.exists_eventually_localSliceComparison
  obtain ⟨c', C', hc', hC', hb⟩ :=
    eventually_rawAxialVariance_bounds_of_local hc hC (by norm_num) (by norm_num) hlocal
  refine ⟨c', C', hc', hC', ?_⟩
  filter_upwards [hb, eventually_rawTransverseVariance_bounds, eventually_rawBody_parameters]
    with d hbd had hpar
  exact ⟨had, rawAxialVariance_eq_halfline_slice_ratio hpar.1 hpar.2, hbd⟩

private lemma inv_sqrt_bounds {b r c C : ℝ} (hb : 0 < b) (hr : 0 < r)
    (hc : 0 < c) (hC : 0 < C) (hl : c / r ^ 2 ≤ b) (hu : b ≤ C / r ^ 2) :
    (Real.sqrt C)⁻¹ * r ≤ (Real.sqrt b)⁻¹ ∧
      (Real.sqrt b)⁻¹ ≤ (Real.sqrt c)⁻¹ * r := by
  have hlow : Real.sqrt c / r ≤ Real.sqrt b := by
    have h := Real.sqrt_le_sqrt hl
    rwa [Real.sqrt_div hc.le, Real.sqrt_sq_eq_abs, abs_of_pos hr] at h
  have hupp : Real.sqrt b ≤ Real.sqrt C / r := by
    have h := Real.sqrt_le_sqrt hu
    rwa [Real.sqrt_div hC.le, Real.sqrt_sq_eq_abs, abs_of_pos hr] at h
  constructor
  · have h := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hb) hupp
    simpa only [one_div, div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul, mul_one, mul_comm] using h
  · have h := one_div_le_one_div_of_le (div_pos (Real.sqrt_pos.mpr hc) hr) hlow
    simpa only [one_div, div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul, mul_one, mul_comm] using h

/-- Original Corollary 4.8: the actual diagonal image is isotropic,
unconditional, and a convex body, its inverse axial scale is of order `d^(1/5)`,
and the forward and inverse coordinate maps are genuine inverses. -/
theorem original4_8 : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ d : ℕ in atTop,
    ∀ i₀ : Fin d,
      Reference.convexBody (euclideanBody (deviationScale d) i₀) ∧
      Reference.unconditional (euclideanBody (deviationScale d) i₀) ∧
      Reference.isotropic (Reference.uniform (euclideanBody (deviationScale d) i₀)) ∧
      c * (d : ℝ) ^ (1 / 5 : ℝ) ≤ (Real.sqrt (rawAxialVariance d (deviationScale d)))⁻¹ ∧
      (Real.sqrt (rawAxialVariance d (deviationScale d)))⁻¹ ≤ C * (d : ℝ) ^ (1 / 5 : ℝ) ∧
      (∀ p : RawPoint d,
        diagonalScale (Real.sqrt (rawTransverseVariance (deviationScale d) i₀))
          (Real.sqrt (rawAxialVariance d (deviationScale d)))
          (diagonalScale (Real.sqrt (rawTransverseVariance (deviationScale d) i₀))⁻¹
            (Real.sqrt (rawAxialVariance d (deviationScale d)))⁻¹ p) = p) := by
  obtain ⟨c, C, hc, hC, hscale⟩ := original4_7
  refine ⟨(Real.sqrt C)⁻¹, (Real.sqrt c)⁻¹, by positivity, by positivity, ?_⟩
  filter_upwards [hscale, eventually_rawBody_parameters, eventually_gt_atTop 0] with d hs hpar hd
  intro i₀
  have ha := rawTransverseVariance_pos hpar.1 hpar.2 i₀
  have hb := rawAxialVariance_pos hpar.1 hpar.2
  have hr : (0 : ℝ) < (d : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  have hrpow : ((d : ℝ) ^ (1 / 5 : ℝ)) ^ 2 = (d : ℝ) ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ d)]
    norm_num
  have hbds := inv_sqrt_bounds hb hr hc hC (by rw [hrpow]; exact hs.2.2.1) (by rw [hrpow]; exact hs.2.2.2)
  obtain ⟨hconv, hunc, hiso⟩ := euclideanBody_certified hpar.1 hpar.2 i₀
  exact ⟨hconv, hunc, hiso, hbds.1, hbds.2, isotropization_inverse ha hb⟩

/-- Original Lemma 4.9: uniformly on the full Gaussian window, for every
sufficiently large fixed precision multiple, the actual slice mass has the
paper's exponential acceptance bound. -/
theorem original4_9 : ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A ≥ A₀, ∀ᶠ d : ℕ in atTop,
    ∀ i₀ : Fin d, ∀ z : ℝ,
      |z| ≤ (Real.sqrt (A / (d : ℝ) ^ (2 / 5 : ℝ)))⁻¹ →
      1 - Real.exp (-2 * deviationScale d ^ 2 / (9 * (d : ℝ))) ≤
        tiltedSlice d ((A / (d : ℝ) ^ (2 / 5 : ℝ)) /
          rawTransverseVariance (deviationScale d) i₀) (deviationScale d)
            (rawAxialVariance d (deviationScale d)) z ∧
      (1 / 2 : ℝ) ≤ 1 - Real.exp (-2 * deviationScale d ^ 2 / (9 * (d : ℝ))) := by
  obtain ⟨c, C, hc, hC, hscale⟩ := original4_7
  exact eventually_tilt_slice_acceptance_of_axial_upper hC (hscale.mono fun _ hd ↦ hd.2.2.2)

/-- The actual axial random variable and the covariance entry agree, including
centering, under the true Euclidean Gaussian tilt. -/
lemma euclideanBody_tilt_axial_variance_eq_covariance {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) {t : ℝ} (ht : 0 < t) :
    variance (fun x : Reference.Space (d+1) ↦ x 0)
      (Reference.gaussianTilt (Reference.uniform (euclideanBody Δ i₀)) t) =
    Reference.covariance (Reference.gaussianTilt (Reference.uniform (euclideanBody Δ i₀)) t) 0 0 := by
  rw [euclideanBody_tilt_covariance_eq_axialLaw hΔ hroom i₀ ht,
    ← euclideanBody_tilt_axial_marginal hΔ hroom i₀ ht]
  have hx : Measurable (fun x : Reference.Space (d+1) ↦ x 0) :=
    (EuclideanSpace.proj (0 : Fin (d+1))).continuous.measurable
  rw [variance_map (by fun_prop) hx.aemeasurable]
  rfl

/-- Legacy fixed-precision implementation of the intended two-constant 4.10
conclusion, including the actual marginal and both variance scales. This is
not the literal printed same-c chain. `Section4StatementBridges.corrected4_10`
proves the separately specified correction for every admissible fixed A. -/
theorem original4_10 : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᶠ d : ℕ in atTop,
    ∀ i₀ : Fin d,
      0 < A / (d : ℝ) ^ (2 / 5 : ℝ) ∧
      Measure.map (fun x : Reference.Space (d+1) ↦ x 0)
        (Reference.gaussianTilt (Reference.uniform (euclideanBody (deviationScale d) i₀))
          (A / (d : ℝ) ^ (2 / 5 : ℝ))) =
        axialLaw (A / (d : ℝ) ^ (2 / 5 : ℝ))
          (tiltedSlice d ((A / (d : ℝ) ^ (2 / 5 : ℝ)) /
            rawTransverseVariance (deviationScale d) i₀) (deviationScale d)
              (rawAxialVariance d (deviationScale d))) ∧
      windowConstant / (A / (d : ℝ) ^ (2 / 5 : ℝ)) ≤
        variance (fun x : Reference.Space (d+1) ↦ x 0)
          (Reference.gaussianTilt (Reference.uniform (euclideanBody (deviationScale d) i₀))
            (A / (d : ℝ) ^ (2 / 5 : ℝ))) ∧
      c * (d : ℝ) ^ (2 / 5 : ℝ) ≤
        variance (fun x : Reference.Space (d+1) ↦ x 0)
          (Reference.gaussianTilt (Reference.uniform (euclideanBody (deviationScale d) i₀))
            (A / (d : ℝ) ^ (2 / 5 : ℝ))) := by
  obtain ⟨A, hA, hacc⟩ := original4_9
  refine ⟨A, windowConstant / A, hA, div_pos windowConstant_pos hA, ?_⟩
  filter_upwards [hacc A le_rfl, eventually_rawBody_parameters, eventually_gt_atTop 0]
    with d haccd hpar hd
  intro i₀
  let t := A / (d : ℝ) ^ (2 / 5 : ℝ)
  have ht : 0 < t := div_pos hA (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)
  have hL : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr ht)
  have htL : t * ((Real.sqrt t)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt ht.le]
    field_simp
  have hvar : windowConstant / t ≤
      Reference.covariance (Reference.gaussianTilt
        (Reference.uniform (euclideanBody (deviationScale d) i₀)) t) 0 0 := by
    rw [euclideanBody_tilt_covariance_eq_axialLaw hpar.1 hpar.2 i₀ ht]
    apply gaussian_window_variance ht hL htL (tiltedSlice_measurable _ _ _ _)
      (tiltedSlice_mem_Icc _ _ _ _) (tiltedSlice_even _ _ _ _)
    intro z hz
    exact (haccd i₀ z hz).2.trans (haccd i₀ z hz).1
  have hvareq := euclideanBody_tilt_axial_variance_eq_covariance hpar.1 hpar.2 i₀ ht
  rw [← hvareq] at hvar
  refine ⟨ht, euclideanBody_tilt_axial_marginal hpar.1 hpar.2 i₀ ht, hvar, ?_⟩
  convert hvar using 1
  dsimp [t]
  field_simp

end GaussianTilt
