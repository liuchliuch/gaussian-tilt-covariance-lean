import GaussianTilt.TiltedCubeComparison

/-! # Finite moderate-deviation bounds for cube squares

The constants below are fixed numerical or explicitly constructed analytic
constants. The normal comparison, tilting, moments and saddlepoint are all
proved in the imported modules.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal Topology
namespace GaussianTilt.CubeModerateBounds
open LowerProbability ModerateDeviations SmoothComparison LaplaceCutoff TiltedCubeComparison

/-- Uniform third-moment budget for a tilted centered coordinate and its normal comparator. -/
def momentBudget : ℝ := 27 + 12 * Real.exp (9 / 8 : ℝ)

def errorConstant : ℝ := cutoffDerivativeBound / 6 * momentBudget

def lowerPeak : ℝ := Real.exp (-4) / Real.sqrt (2 * Real.pi * (9 / 4 : ℝ))

def upperPeak : ℝ := (Real.sqrt (2 * Real.pi * meanDeficitConstant))⁻¹

lemma momentBudget_pos : 0 < momentBudget := by unfold momentBudget; positivity
lemma errorConstant_pos : 0 < errorConstant := by
  unfold errorConstant
  exact mul_pos (div_pos cutoffDerivativeBound_pos (by norm_num)) momentBudget_pos
lemma lowerPeak_pos : 0 < lowerPeak := by unfold lowerPeak; positivity
lemma upperPeak_pos : 0 < upperPeak := by
  unfold upperPeak
  exact inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) meanDeficitConstant_pos))

/-- The actual tilted variance, bundled with its proved nonnegativity. -/
def tiltedVariance (t : ℝ) : ℝ≥0 :=
  ⟨variance coordinateDeficit (deficitTilt t), variance_nonneg _ _⟩

lemma tiltedVariance_lower {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    meanDeficitConstant ≤ (tiltedVariance t : ℝ) := deficitTilt_variance_lower ht

lemma tiltedVariance_upper (t : ℝ) : (tiltedVariance t : ℝ) ≤ 9 / 4 :=
  deficitTilt_variance_le t

lemma sqrt_gaussian_scale (d : ℕ) (v : ℝ≥0) :
    Real.sqrt (2 * Real.pi * ((d : ℝ) * (v : ℝ))) =
      Real.sqrt d * Real.sqrt (2 * Real.pi * v) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg d)]
  congr 1
  ring

lemma gaussian_lower_peak {d : ℕ} (hd : 0 < d) {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    lowerPeak / (t * Real.sqrt d) ≤
      Real.exp (-4) / (t * Real.sqrt (2 * Real.pi * ((d : ℝ) * (tiltedVariance t : ℝ)))) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [sqrt_gaussian_scale]
  have htpos := ht.1
  have hv := tiltedVariance_upper t
  have hs : Real.sqrt (2 * Real.pi * (tiltedVariance t : ℝ)) ≤
      Real.sqrt (2 * Real.pi * (9 / 4 : ℝ)) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
  have hden : 0 < t * (Real.sqrt d * Real.sqrt (2 * Real.pi * (tiltedVariance t : ℝ))) := by
    have hvar : 0 < (tiltedVariance t : ℝ) :=
      meanDeficitConstant_pos.trans_le (tiltedVariance_lower ⟨ht.1.le, ht.2⟩)
    positivity
  calc
    _ = Real.exp (-4) / (t * (Real.sqrt d * Real.sqrt (2 * Real.pi * (9 / 4 : ℝ)))) := by
      unfold lowerPeak
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _) hden (by gcongr)

lemma gaussian_upper_peak {d : ℕ} (hd : 0 < d) {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    1 / (t * Real.sqrt (2 * Real.pi * ((d : ℝ) * (tiltedVariance t : ℝ)))) ≤
      upperPeak / (t * Real.sqrt d) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have htpos := ht.1
  have hv := tiltedVariance_lower ⟨ht.1.le, ht.2⟩
  have hs : Real.sqrt (2 * Real.pi * meanDeficitConstant) ≤
      Real.sqrt (2 * Real.pi * (tiltedVariance t : ℝ)) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
  rw [sqrt_gaussian_scale]
  calc
    _ ≤ 1 / (t * (Real.sqrt d * Real.sqrt (2 * Real.pi * meanDeficitConstant))) := by
      apply div_le_div_of_nonneg_left zero_le_one
      · have hc := meanDeficitConstant_pos
        have htpos := ht.1
        positivity
      · gcongr
    _ = _ := by unfold upperPeak; ring

/-- Correct Laplace prefactors for the concrete tilted cube, with only
explicit deterministic scale conditions. -/
theorem tilted_cube_laplace_bounds {d : ℕ} (hd : 0 < d) {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) 1)
    (hscale : 1 ≤ (d : ℝ) * meanDeficitConstant * t ^ 2)
    (hsmooth : 2 * errorConstant * (d : ℝ) * Real.sqrt d * t ^ 4 ≤ lowerPeak) :
    lowerPeak / (2 * t * Real.sqrt d) ≤ oneSidedLaplace (sumLaw (centeredDeficitLaw t) d) t ∧
      oneSidedLaplace (sumLaw (centeredDeficitLaw t) d) t ≤
        Real.exp 1 * (upperPeak + lowerPeak / 2) / (t * Real.sqrt d) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have htpos := ht.1
  have hvlo := tiltedVariance_lower ⟨ht.1.le, ht.2⟩
  have hvup := tiltedVariance_upper t
  let E : ℝ := (d : ℝ) * (cutoffDerivativeBound * t ^ 3 / 6 *
      (thirdMoment (centeredDeficitLaw t) + thirdMoment (gaussianReal 0 (tiltedVariance t))))
  have hm : thirdMoment (centeredDeficitLaw t) + thirdMoment (gaussianReal 0 (tiltedVariance t)) ≤
      momentBudget := by
    have h1 := centeredDeficitLaw_third_le t
    have h2 := gaussian_thirdMoment_le hvup
    unfold momentBudget
    linarith
  have he : E ≤ errorConstant * (d : ℝ) * t ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hm
      (show 0 ≤ (d : ℝ) * cutoffDerivativeBound * t ^ 3 / 6 by
        have hc := cutoffDerivativeBound_pos
        positivity)
    dsimp [E, errorConstant]
    nlinarith only [h]
  have hEs : E ≤ lowerPeak / (2 * t * Real.sqrt d) := by
    apply he.trans
    apply (le_div_iff₀ (by positivity : 0 < 2 * t * Real.sqrt (d : ℝ))).mpr
    nlinarith only [hsmooth]
  have hL := oneSidedLaplace_normal_bounds
    ((centeredDeficitLaw_memLp t 1).integrable le_rfl)
    (centeredDeficitLaw_memLp t 2).integrable_sq
    (by simpa only [id_eq, Real.norm_eq_abs] using
      (centeredDeficitLaw_memLp t 3).integrable_norm_pow' (p := 3))
    (centeredDeficitLaw_mean t) (tiltedVariance t) (centeredDeficitLaw_second t) d ht.1
    (by nlinarith [mul_le_mul_of_nonneg_left hvlo (show 0 ≤ (d : ℝ) * t ^ 2 by positivity)])
  change _ - E ≤ _ ∧ _ ≤ Real.exp 1 * (_ + E) at hL
  have hplo := gaussian_lower_peak hd ht
  have hpup := gaussian_upper_peak hd ht
  constructor
  · calc
      _ = lowerPeak / (t * Real.sqrt d) - lowerPeak / (2 * t * Real.sqrt d) := by ring
      _ ≤ Real.exp (-4) / (t * Real.sqrt (2 * Real.pi * ((d : ℝ) * (tiltedVariance t : ℝ)))) - E :=
        sub_le_sub hplo hEs
      _ ≤ _ := hL.1
  · calc
      _ ≤ Real.exp 1 * (1 / (t * Real.sqrt (2 * Real.pi * ((d : ℝ) * (tiltedVariance t : ℝ)))) + E) := hL.2
      _ ≤ Real.exp 1 * (upperPeak / (t * Real.sqrt d) + lowerPeak / (2 * t * Real.sqrt d)) :=
        mul_le_mul_of_nonneg_left (add_le_add hpup hEs) (Real.exp_nonneg _)
      _ = _ := by ring

def lowerTiltConstant : ℝ := Real.exp (-1) * lowerPeak / 2

def upperTiltConstant : ℝ := Real.exp 2 * (upperPeak + lowerPeak / 2)

lemma lowerTiltConstant_pos : 0 < lowerTiltConstant := by
  unfold lowerTiltConstant
  have h := lowerPeak_pos
  positivity

lemma upperTiltConstant_pos : 0 < upperTiltConstant := by
  unfold upperTiltConstant
  have h1 := upperPeak_pos
  have h2 := lowerPeak_pos
  positivity

/-- Sharp finite bounds at the actual saddlepoint, including the polynomial
prefactor. All probability estimates are discharged; the hypotheses are
explicit deterministic scale inequalities. -/
theorem cube_tail_saddlepoint_bounds {d : ℕ} (hd : 0 < d) {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hscale : 1 ≤ (d : ℝ) * meanDeficitConstant * t ^ 2)
    (hsmooth : 2 * errorConstant * (d : ℝ) * Real.sqrt d * t ^ 4 ≤ lowerPeak)
    (hrate : 30 * (d : ℝ) * t ^ 3 ≤ 1) :
    lowerTiltConstant * Real.exp (-(5 / 8 : ℝ) * (d : ℝ) *
        deriv (cgf coordinateDeficit cubeCoordinateLaw) t ^ 2) / (t * Real.sqrt d) ≤
      (cubeLaw d).real {x | (d : ℝ) * deriv (cgf coordinateDeficit cubeCoordinateLaw) t ≤ cubeDeficit d x} ∧
    (cubeLaw d).real {x | (d : ℝ) * deriv (cgf coordinateDeficit cubeCoordinateLaw) t ≤ cubeDeficit d x} ≤
      upperTiltConstant * Real.exp (-(5 / 8 : ℝ) * (d : ℝ) *
        deriv (cgf coordinateDeficit cubeCoordinateLaw) t ^ 2) / (t * Real.sqrt d) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have htpos := ht.1
  have hL := tilted_cube_laplace_bounds hd ⟨ht.1, by linarith [ht.2]⟩ hscale hsmooth
  have hK := abs_le.mp (coordinateDeficit_saddlepoint_rate ⟨ht.1.le, ht.2⟩)
  let R : ℝ := (d : ℝ) * (cgf coordinateDeficit cubeCoordinateLaw t -
    t * deriv (cgf coordinateDeficit cubeCoordinateLaw) t)
  let G : ℝ := -(5 / 8 : ℝ) * (d : ℝ) * deriv (cgf coordinateDeficit cubeCoordinateLaw) t ^ 2
  have hRlo : -1 + G ≤ R := by
    have h := mul_le_mul_of_nonneg_left hK.1 hdpos.le
    dsimp [G, R]
    nlinarith only [h, hrate]
  have hRup : R ≤ 1 + G := by
    have h := mul_le_mul_of_nonneg_left hK.2 hdpos.le
    dsimp [G, R]
    nlinarith only [h, hrate]
  have helo : Real.exp (-1) * Real.exp G ≤ Real.exp R := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hRlo
  have heup : Real.exp R ≤ Real.exp 1 * Real.exp G := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hRup
  rw [cubeDeficit_tail_eq_laplace]
  change lowerTiltConstant * Real.exp G / (t * Real.sqrt d) ≤
    Real.exp R * oneSidedLaplace (sumLaw (centeredDeficitLaw t) d) t ∧
    Real.exp R * oneSidedLaplace (sumLaw (centeredDeficitLaw t) d) t ≤
      upperTiltConstant * Real.exp G / (t * Real.sqrt d)
  constructor
  · calc
      _ = (Real.exp (-1) * Real.exp G) * (lowerPeak / (2 * t * Real.sqrt d)) := by
        unfold lowerTiltConstant
        ring
      _ ≤ _ := mul_le_mul helo hL.1 (by have h := lowerPeak_pos; positivity) (Real.exp_nonneg _)
  · have hn : 0 ≤ oneSidedLaplace (sumLaw (centeredDeficitLaw t) d) t :=
      integral_nonneg (fun _ ↦ Real.exp_nonneg _)
    calc
      _ ≤ (Real.exp 1 * Real.exp G) *
          (Real.exp 1 * (upperPeak + lowerPeak / 2) / (t * Real.sqrt d)) :=
        mul_le_mul heup hL.2 hn (by positivity)
      _ = _ := by
        have he2 : Real.exp 1 * Real.exp 1 = Real.exp 2 := by rw [← Real.exp_add]; norm_num
        unfold upperTiltConstant
        calc
          _ = (Real.exp 1 * Real.exp 1) * (upperPeak + lowerPeak / 2) * Real.exp G /
              (t * Real.sqrt d) := by ring
          _ = _ := by rw [he2]

/-- A universal admissible scale for the finite moderate-deviation estimate. -/
def moderateScale : ℝ :=
  min (meanDeficitConstant / 2)
    (min (meanDeficitConstant / 36)
      (min (meanDeficitConstant ^ 3 / 30)
        (meanDeficitConstant ^ 4 * lowerPeak / (2 * errorConstant))))

lemma moderateScale_pos : 0 < moderateScale := by
  unfold moderateScale
  have hc := meanDeficitConstant_pos
  have hl := lowerPeak_pos
  have he := errorConstant_pos
  positivity

/-- Finite cube-square moderate deviations, including the correct polynomial
prefactor and Gaussian exponent. The constants are universal, and every
hypothesis after the positivity conditions is a deterministic scale bound.
This theorem is the input for the paper's bounded-window specialization. -/
theorem cube_moderate_deviation_bounds :
    ∃ kLo kHi ε : ℝ, 0 < kLo ∧ 0 < kHi ∧ 0 < ε ∧
      ∀ (d : ℕ) (δ : ℝ), 0 < d → 0 < δ → δ ≤ ε →
        ε⁻¹ ≤ (d : ℝ) * δ ^ 2 → (d : ℝ) * δ ^ 3 ≤ ε →
        (d : ℝ) * Real.sqrt d * δ ^ 4 ≤ ε →
        kLo * Real.exp (-(5 / 8 : ℝ) * (d : ℝ) * δ ^ 2) / (δ * Real.sqrt d) ≤
          (cubeLaw d).real {x | (d : ℝ) * δ ≤ cubeDeficit d x} ∧
        (cubeLaw d).real {x | (d : ℝ) * δ ≤ cubeDeficit d x} ≤
          kHi * Real.exp (-(5 / 8 : ℝ) * (d : ℝ) * δ ^ 2) / (δ * Real.sqrt d) := by
  refine ⟨meanDeficitConstant * lowerTiltConstant, 6 * upperTiltConstant, moderateScale,
    mul_pos meanDeficitConstant_pos lowerTiltConstant_pos,
    mul_pos (by norm_num) upperTiltConstant_pos, moderateScale_pos, ?_⟩
  intro d δ hd hδ hsmall hlarge hcubic hfourth
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hc := meanDeficitConstant_pos
  have he := errorConstant_pos
  have hε := moderateScale_pos
  have hε2 : moderateScale ≤ meanDeficitConstant / 2 := min_le_left _ _
  have hε36 : moderateScale ≤ meanDeficitConstant / 36 := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : moderateScale ≤ meanDeficitConstant ^ 3 / 30 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε4 : moderateScale ≤ meanDeficitConstant ^ 4 * lowerPeak / (2 * errorConstant) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδc : δ ≤ meanDeficitConstant := by linarith
  obtain ⟨t, ht, hmean⟩ := exists_cube_saddlepoint ⟨hδ.le, hδc⟩
  have htHalf : t ≤ 1 / 2 := by
    apply ht.2.trans
    apply (div_le_iff₀ hc).mpr
    linarith
  have hm := (abs_le.mp (coordinateDeficit_cgf_deriv_remainder ⟨ht.1, htHalf⟩)).2
  rw [hmean] at hm
  have ht2 : t ^ 2 ≤ t / 2 := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr htHalf)]
  have hδt : δ ≤ 6 * t := by nlinarith
  have htpos : 0 < t := by linarith
  have hct : meanDeficitConstant * t ≤ δ := by
    have h := (le_div_iff₀ hc).mp ht.2
    nlinarith
  have hscale : 1 ≤ (d : ℝ) * meanDeficitConstant * t ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hlarge hε.le
    rw [mul_inv_cancel₀ hε.ne'] at hh
    have h36 : 36 * moderateScale ≤ meanDeficitConstant := by linarith
    have hh36 := mul_le_mul_of_nonneg_right h36
      (show 0 ≤ (d : ℝ) * δ ^ 2 by positivity)
    have hsq := pow_le_pow_left₀ hδ.le hδt 2
    have hsqmul := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ (d : ℝ) * meanDeficitConstant by positivity)
    nlinarith
  have hrate : 30 * (d : ℝ) * t ^ 3 ≤ 1 := by
    have hp := pow_le_pow_left₀ (mul_nonneg hc.le ht.1) hct 3
    rw [mul_pow] at hp
    have hmul := mul_le_mul_of_nonneg_left hp hdpos.le
    have hh : meanDeficitConstant ^ 3 * (30 * (d : ℝ) * t ^ 3) ≤ meanDeficitConstant ^ 3 * 1 := by
      nlinarith
    exact le_of_mul_le_mul_left hh (pow_pos hc 3)
  have hsmooth : 2 * errorConstant * (d : ℝ) * Real.sqrt d * t ^ 4 ≤ lowerPeak := by
    have hp := pow_le_pow_left₀ (mul_nonneg hc.le ht.1) hct 4
    rw [mul_pow] at hp
    have hmul := mul_le_mul_of_nonneg_left hp
      (show 0 ≤ (d : ℝ) * Real.sqrt d by positivity)
    have hεmul := (le_div_iff₀ (show 0 < 2 * errorConstant by positivity)).mp hε4
    have hmul2 := mul_le_mul_of_nonneg_left (hmul.trans hfourth)
      (show 0 ≤ 2 * errorConstant by positivity)
    have hh : meanDeficitConstant ^ 4 *
        (2 * errorConstant * (d : ℝ) * Real.sqrt d * t ^ 4) ≤ meanDeficitConstant ^ 4 * lowerPeak := by
      nlinarith only [hmul2, hεmul]
    exact le_of_mul_le_mul_left hh (pow_pos hc 4)
  have hP := cube_tail_saddlepoint_bounds hd ⟨htpos, htHalf⟩ hscale hsmooth hrate
  rw [hmean] at hP
  have hsqrt : 0 < Real.sqrt (d : ℝ) := by positivity
  constructor
  · apply le_trans _ hP.1
    apply (div_le_div_iff₀ (mul_pos hδ hsqrt) (mul_pos htpos hsqrt)).mpr
    have h := mul_le_mul_of_nonneg_left hct
      (show 0 ≤ lowerTiltConstant * Real.exp (-(5 / 8 : ℝ) * (d : ℝ) * δ ^ 2) * Real.sqrt d by
        have hl := lowerTiltConstant_pos
        positivity)
    nlinarith only [h]
  · apply hP.2.trans
    apply (div_le_div_iff₀ (mul_pos htpos hsqrt) (mul_pos hδ hsqrt)).mpr
    have h := mul_le_mul_of_nonneg_left hδt
      (show 0 ≤ upperTiltConstant * Real.exp (-(5 / 8 : ℝ) * (d : ℝ) * δ ^ 2) * Real.sqrt d by
        have hu := upperTiltConstant_pos
        positivity)
    nlinarith only [h]

end GaussianTilt.CubeModerateBounds
