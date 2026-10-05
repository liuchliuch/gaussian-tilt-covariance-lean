import GaussianTilt.GaussianLaplace

/-! # Finite relative-tail estimates for general Cramér laws

The control package below is constructed from the original Cramér hypotheses.
It is not a replacement assumption for the desired moderate-deviation bound.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal Topology
namespace GaussianTilt.CramerFinite
open CramerAnalytic StandardizedTilt SmoothComparison GaussianSmoothing LaplaceCutoff LaplaceComparison
  GaussianLaplace TiltedCubeComparison

structure TiltControl (μ : Measure ℝ) where
  radius : ℝ
  remainder : ℝ
  moment : ℝ
  radius_pos : 0 < radius
  radius_le_one : radius ≤ 1
  remainder_pos : 0 < remainder
  moment_pos : 0 < moment
  bounds : ∀ t ∈ Set.Icc (0 : ℝ) radius,
    t ∈ interior (integrableExpSet id μ) ∧
    |iteratedDeriv 2 (cgf id μ) t - 1| ≤ remainder * t ∧
    |deriv (cgf id μ) t - t| ≤ remainder * t ^ 2 ∧
    |cgf id μ t - t ^ 2 / 2| ≤ remainder * t ^ 3 ∧
    (1 / 2 : ℝ) ≤ iteratedDeriv 2 (cgf id μ) t ∧
    iteratedDeriv 2 (cgf id μ) t ≤ 2 ∧
    t / 2 ≤ deriv (cgf id μ) t ∧ deriv (cgf id μ) t ≤ 2 * t
  third : ∀ t ∈ Set.Icc (0 : ℝ) radius, thirdMoment (law μ t) ≤ moment

/-- Every normalized Cramér law admits the analytic and moment controls used
below; no new regularity or normal approximation is assumed. -/
theorem exists_tiltControl {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : StandardCramer μ) :
    Nonempty (TiltControl μ) := by
  obtain ⟨η, C, hη, hη1, hC, hlocal⟩ := exists_cgf_local_control hμ
  have hdom (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) η) : t ∈ interior (integrableExpSet id μ) :=
    (hlocal t ht).1
  have hmean (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) η) : |deriv (cgf id μ) t| ≤ 2 := by
    obtain ⟨_, _, _, _, _, _, hlo, hup⟩ := hlocal t ht
    have hm : 0 ≤ deriv (cgf id μ) t := (div_nonneg ht.1 (by norm_num) : 0 ≤ t / 2).trans hlo
    rw [abs_of_nonneg hm]
    nlinarith [ht.2]
  have hvar (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) η) : (1 / 2 : ℝ) ≤ iteratedDeriv 2 (cgf id μ) t :=
    (hlocal t ht).2.2.2.2.1
  obtain ⟨M, hM, hthird⟩ := exists_third_moment_bound hμ hη hdom hmean hvar
  exact ⟨⟨η, C, M, hη, hη1, hC, hM, hlocal, hthird⟩⟩

lemma TiltControl.saddlepoint {μ : Measure ℝ} (P : TiltControl μ) {δ : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (P.radius / 2)) :
    ∃ t ∈ Set.Icc (0 : ℝ) (2 * δ), t ≤ P.radius ∧ deriv (cgf id μ) t = δ := by
  have hmax : 2 * δ ≤ P.radius := by linarith [hδ.2]
  have hcont : ContinuousOn (deriv (cgf id μ)) (Set.Icc (0 : ℝ) (2 * δ)) := by
    intro x hx
    exact (analyticAt_cgf ((P.bounds x ⟨hx.1, hx.2.trans hmax⟩).1)).deriv.continuousAt.continuousWithinAt
  have hzero := P.bounds 0 ⟨le_rfl, P.radius_pos.le⟩
  have hz : deriv (cgf id μ) 0 = 0 := by linarith [hzero.2.2.2.2.2.2.1, hzero.2.2.2.2.2.2.2]
  have hhigh := (P.bounds (2 * δ) ⟨by linarith [hδ.1], hmax⟩).2.2.2.2.2.2.1
  have hmem : δ ∈ Set.Icc (deriv (cgf id μ) 0) (deriv (cgf id μ) (2 * δ)) := by
    rw [hz]
    exact ⟨hδ.1, by linarith⟩
  obtain ⟨t, ht, hm⟩ := intermediate_value_Icc (by linarith [hδ.1]) hcont hmem
  exact ⟨t, ht, ht.2.trans hmax, hm⟩

lemma abs_sqrt_sub_one_le {v : ℝ} (hv : 0 ≤ v) :
    |Real.sqrt v - 1| ≤ |v - 1| := by
  have hs := Real.sq_sqrt hv
  have hid : (Real.sqrt v - 1) * (Real.sqrt v + 1) = v - 1 := by nlinarith
  have hh : |Real.sqrt v - 1| ≤ |Real.sqrt v - 1| * (Real.sqrt v + 1) := by
    nlinarith [mul_nonneg (abs_nonneg (Real.sqrt v - 1)) (Real.sqrt_nonneg v)]
  calc
    _ ≤ _ := hh
    _ = |(Real.sqrt v - 1) * (Real.sqrt v + 1)| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt v + 1)]
    _ = _ := by rw [hid]

lemma TiltControl.rate_error {μ : Measure ℝ} (P : TiltControl μ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) P.radius) :
    |cgf id μ t - t * deriv (cgf id μ) t + deriv (cgf id μ) t ^ 2 / 2| ≤
      (P.remainder + P.remainder ^ 2) * t ^ 3 := by
  obtain ⟨_, _, hm, hK, _, _, _, _⟩ := P.bounds t ht
  have ht1 : t ≤ 1 := ht.2.trans P.radius_le_one
  have ht4 : t ^ 4 ≤ t ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg ht.1 3) (sub_nonneg.mpr ht1)]
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg P.remainder_pos.le (sq_nonneg t))).mpr hm
  rw [sq_abs] at hs
  have hsmul := mul_le_mul_of_nonneg_left ht4 (sq_nonneg P.remainder)
  have hk := abs_le.mp hK
  have hzero := sq_nonneg (deriv (cgf id μ) t - t)
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg (sq_nonneg P.remainder) (pow_nonneg ht.1 3)]

lemma TiltControl.frequency_error {μ : Measure ℝ} (P : TiltControl μ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) P.radius) :
    |t * Real.sqrt (iteratedDeriv 2 (cgf id μ) t) - deriv (cgf id μ) t| ≤
      2 * P.remainder * t ^ 2 := by
  obtain ⟨_, hv, hm, _, hvl, _, _, _⟩ := P.bounds t ht
  have hs : |Real.sqrt (iteratedDeriv 2 (cgf id μ) t) - 1| ≤ P.remainder * t :=
    (abs_sqrt_sub_one_le (by linarith)).trans hv
  have heq : t * Real.sqrt (iteratedDeriv 2 (cgf id μ) t) - deriv (cgf id μ) t =
      t * (Real.sqrt (iteratedDeriv 2 (cgf id μ) t) - 1) + (t - deriv (cgf id μ) t) := by ring
  rw [heq]
  have htri := abs_add_le (t * (Real.sqrt (iteratedDeriv 2 (cgf id μ) t) - 1)) (t - deriv (cgf id μ) t)
  rw [abs_mul, abs_of_nonneg ht.1, abs_sub_comm t] at htri
  nlinarith [mul_le_mul_of_nonneg_left hs ht.1]

/-- Exact general saddlepoint representation, with the standardized tilted
convolution law, proved using actual measure maps and MGF uniqueness. -/
theorem sum_tail_eq_standardized_laplace {μ : Measure ℝ} [IsProbabilityMeasure μ] {t : ℝ}
    (ht : t ∈ interior (integrableExpSet id μ)) (hv : 0 < iteratedDeriv 2 (cgf id μ) t) (n : ℕ) :
    (sumLaw μ n).real {x | (n : ℝ) * deriv (cgf id μ) t ≤ x} =
      Real.exp ((n : ℝ) * (cgf id μ t - t * deriv (cgf id μ) t)) *
      oneSidedLaplace (sumLaw (law μ t) n) (t * Real.sqrt (iteratedDeriv 2 (cgf id μ) t)) := by
  have htSum := interior_integrableExpSet_sumLaw ht n
  have hiSum : Integrable (fun x : ℝ ↦ Real.exp (t * x)) (sumLaw μ n) :=
    interior_subset (s := integrableExpSet id (sumLaw μ n)) htSum
  let σ := Real.sqrt (iteratedDeriv 2 (cgf id μ) t)
  have hσ : 0 < σ := Real.sqrt_pos.mpr hv
  have hmap : (sumLaw (law μ t) n).map (fun x ↦ σ * x) =
      ((sumLaw μ n).tilted (fun x ↦ t * x)).map
        (fun x ↦ x - (n : ℝ) * deriv (cgf id μ) t) := by
    rw [← normalized_sum_map ht n, Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    dsimp only [Function.comp_apply]
    dsimp [σ]
    field_simp
  have h := tail_eq_tilted_laplace (sumLaw μ n) id measurable_id t
    ((n : ℝ) * deriv (cgf id μ) t) hiSum
  simp only [id_eq] at h
  rw [← hmap, oneSidedLaplace_map_mul _ hσ, cgf_sumLaw] at h
  convert h using 1
  congr 2
  ring

def normalFirstMoment : ℝ := ∫ x : ℝ, |x| ∂gaussianReal 0 1

def normalLaplaceConstant : ℝ := Real.exp (-4) / Real.sqrt (2 * Real.pi)

lemma normalFirstMoment_nonneg : 0 ≤ normalFirstMoment := integral_nonneg (fun _ ↦ abs_nonneg _)

lemma normalFirstMoment_integrable : Integrable (fun x : ℝ ↦ |x|) (gaussianReal 0 1) := by
  have h := ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).norm
  simpa only [id_eq, Real.norm_eq_abs] using h

lemma normalLaplaceConstant_pos : 0 < normalLaplaceConstant := by
  unfold normalLaplaceConstant
  positivity

lemma TiltControl.normalApproximationConstant_pos {μ : Measure ℝ} (P : TiltControl μ) :
    0 < normalApproximationConstant P.moment := by
  have hM : 0 ≤ thirdMoment (gaussianReal 0 1) := integral_nonneg (fun _ ↦ by positivity)
  unfold normalApproximationConstant
  have h := P.moment_pos
  positivity

def TiltControl.approximationBudget {μ : Measure ℝ} (P : TiltControl μ) : ℝ :=
  2 * normalApproximationConstant P.moment + 8 * P.remainder * normalFirstMoment

def TiltControl.relativeConstant {μ : Measure ℝ} (P : TiltControl μ) : ℝ :=
  max 1 (max (8 * (P.remainder + P.remainder ^ 2)) (P.approximationBudget / normalLaplaceConstant))

lemma TiltControl.approximationBudget_pos {μ : Measure ℝ} (P : TiltControl μ) :
    0 < P.approximationBudget := by
  unfold TiltControl.approximationBudget
  have h1 := P.normalApproximationConstant_pos
  have h2 := P.remainder_pos
  have h3 := normalFirstMoment_nonneg
  positivity

lemma TiltControl.relativeConstant_pos {μ : Measure ℝ} (P : TiltControl μ) :
    0 < P.relativeConstant := zero_lt_one.trans_le (le_max_left _ _)

lemma TiltControl.relativeConstant_rate {μ : Measure ℝ} (P : TiltControl μ) :
    8 * (P.remainder + P.remainder ^ 2) ≤ P.relativeConstant :=
  (le_max_left _ _).trans (le_max_right _ _)

lemma TiltControl.relativeConstant_budget {μ : Measure ℝ} (P : TiltControl μ) :
    P.approximationBudget / normalLaplaceConstant ≤ P.relativeConstant :=
  (le_max_right _ _).trans (le_max_right _ _)

lemma TiltControl.laplace_error {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (P : TiltControl μ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) P.radius)
    (n : ℕ) (hn : 0 < n) :
    |oneSidedLaplace (sumLaw (law μ t) n) (t * Real.sqrt (iteratedDeriv 2 (cgf id μ) t)) -
      oneSidedLaplace (gaussianReal 0 1) (t * Real.sqrt (iteratedDeriv 2 (cgf id μ) t) * Real.sqrt n)| ≤
      2 * normalApproximationConstant P.moment * (n : ℝ) ^ (-(1 / 5 : ℝ)) := by
  obtain ⟨hdom, _, _, _, hvl, _, _, _⟩ := P.bounds t ht
  haveI := law_probability hdom
  have hv : 0 < iteratedDeriv 2 (cgf id μ) t := by linarith
  have hcdf (a : ℝ) := cdf_sum_normal_rate_of_third_le
    ((law_memLp hdom 1).integrable le_rfl) (law_memLp hdom 2).integrable_sq
    (law_third_integrable hdom) (law_mean hdom) (law_second hdom hv) (P.third t ht) n hn a
  have hh := oneSidedLaplace_cdf_bound_nonneg hcdf
    (mul_nonneg ht.1 (Real.sqrt_nonneg (iteratedDeriv 2 (cgf id μ) t)))
  have hnnz : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [gaussian_laplace_scale hnnz] at hh
  simpa only [NNReal.coe_natCast, mul_assoc] using hh

lemma exp_perturbation_bound {R r : ℝ} (hR : |R| ≤ r) :
    |Real.exp R - 1| ≤ Real.exp r - 1 := by
  have hb := abs_le.mp hR
  have hp : Real.exp R ≤ Real.exp r := Real.exp_le_exp.mpr hb.2
  have hn : Real.exp (-R) ≤ Real.exp r := Real.exp_le_exp.mpr (by linarith)
  have hsum : 2 ≤ Real.exp R + Real.exp (-R) := by
    linarith [Real.add_one_le_exp R, Real.add_one_le_exp (-R)]
  apply abs_le.mpr
  constructor <;> linarith

lemma multiplicative_perturbation {R r q E : ℝ} (hR : |R| ≤ r) (hq : |q - 1| ≤ E) :
    |Real.exp R * q - 1| ≤ Real.exp r * (1 + E) - 1 := by
  have he := exp_perturbation_bound hR
  have hup : Real.exp R ≤ Real.exp r := Real.exp_le_exp.mpr (abs_le.mp hR).2
  have hmul := mul_le_mul hup hq (abs_nonneg (q - 1)) (Real.exp_nonneg r)
  have heq : Real.exp R * q - 1 = Real.exp R * (q - 1) + (Real.exp R - 1) := by ring
  rw [heq]
  have htri := abs_add_le (Real.exp R * (q - 1)) (Real.exp R - 1)
  rw [abs_mul, abs_of_pos (Real.exp_pos R)] at htri
  nlinarith only [htri, hmul, he]

lemma abs_div_sub_one {L J : ℝ} (hJ : 0 < J) :
    |L / J - 1| = |L - J| / J := by
  rw [← abs_of_pos hJ, ← abs_div]
  congr 1
  rw [abs_of_pos hJ]
  field_simp

/-- Finite relative-tail estimate at a deficit per summand `δ`. Every analytic
and probabilistic ingredient comes from the proved control package. -/
theorem TiltControl.relative_tail_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (P : TiltControl μ) (n : ℕ) (hn : 0 < n) {δ : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (P.radius / 2)) :
    |(sumLaw μ n).real {x | (n : ℝ) * δ ≤ x} / normalTail (δ * Real.sqrt n) - 1| ≤
      Real.exp (P.relativeConstant * (n : ℝ) * δ ^ 3) *
        (1 + P.relativeConstant * (1 + δ * Real.sqrt n) *
          (δ ^ 2 * Real.sqrt n + (n : ℝ) ^ (-(1 / 5 : ℝ)))) - 1 := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := by positivity
  obtain ⟨t, ht, htr, hmean⟩ := P.saddlepoint hδ
  have htc : t ∈ Set.Icc (0 : ℝ) P.radius := ⟨ht.1, htr⟩
  obtain ⟨hdom, _, _, _, hvl, _, _, _⟩ := P.bounds t htc
  have hv : 0 < iteratedDeriv 2 (cgf id μ) t := by linarith
  let σ : ℝ := Real.sqrt (iteratedDeriv 2 (cgf id μ) t)
  let z : ℝ := δ * Real.sqrt n
  let w : ℝ := t * σ * Real.sqrt n
  let xerr : ℝ := δ ^ 2 * Real.sqrt n
  let yerr : ℝ := (n : ℝ) ^ (-(1 / 5 : ℝ))
  let L : ℝ := oneSidedLaplace (sumLaw (law μ t) n) (t * σ)
  let J : ℝ := oneSidedLaplace (gaussianReal 0 1) z
  let R : ℝ := (n : ℝ) * (cgf id μ t - t * δ + δ ^ 2 / 2)
  have hz : 0 ≤ z := mul_nonneg hδ.1 hsqrt.le
  have hw : 0 ≤ w := by dsimp [w, σ]; exact mul_nonneg (mul_nonneg ht.1 (Real.sqrt_nonneg _)) hsqrt.le
  have hxerr : 0 ≤ xerr := by dsimp [xerr]; positivity
  have hyerr : 0 ≤ yerr := Real.rpow_nonneg hnp.le _
  have hJlo : normalLaplaceConstant / (1 + z) ≤ J := gaussian_laplace_lower hz
  have hJ : 0 < J := (div_pos normalLaplaceConstant_pos (by linarith)).trans_le hJlo
  have hCLT := P.laplace_error htc n hn
  change |L - oneSidedLaplace (gaussianReal 0 1) w| ≤
    2 * normalApproximationConstant P.moment * yerr at hCLT
  have hfreq0 := P.frequency_error htc
  rw [hmean] at hfreq0
  have hfreq : |w - z| ≤ 8 * P.remainder * xerr := by
    calc
      _ = |t * σ - δ| * Real.sqrt n := by
        rw [← abs_of_nonneg hsqrt.le, ← abs_mul]
        congr 1
        dsimp [w, z]
        ring
      _ ≤ (2 * P.remainder * t ^ 2) * Real.sqrt n :=
        mul_le_mul_of_nonneg_right hfreq0 hsqrt.le
      _ ≤ (2 * P.remainder * (2 * δ) ^ 2) * Real.sqrt n := by
        apply mul_le_mul_of_nonneg_right _ hsqrt.le
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1 ht.2 2) (by have h := P.remainder_pos; positivity)
      _ = _ := by dsimp [xerr]; ring
  have hLip := oneSidedLaplace_lipschitz (gaussianReal 0 1) normalFirstMoment_integrable hw hz
  change |oneSidedLaplace (gaussianReal 0 1) w - J| ≤ |w - z| * normalFirstMoment at hLip
  have hLip' := hLip.trans (mul_le_mul_of_nonneg_right hfreq normalFirstMoment_nonneg)
  have htri := abs_sub_le L (oneSidedLaplace (gaussianReal 0 1) w) J
  have hLabs : |L - J| ≤ P.approximationBudget * (xerr + yerr) := by
    have hα : 0 ≤ 2 * normalApproximationConstant P.moment := by
      have h := P.normalApproximationConstant_pos
      positivity
    have hβ : 0 ≤ 8 * P.remainder * normalFirstMoment := by
      have h1 := P.remainder_pos
      have h2 := normalFirstMoment_nonneg
      positivity
    dsimp [TiltControl.approximationBudget]
    nlinarith only [htri, hCLT, hLip', mul_nonneg hα hxerr, mul_nonneg hβ hyerr]
  have hq : |L / J - 1| ≤ P.relativeConstant * (1 + z) * (xerr + yerr) := by
    calc
      _ = |L - J| / J := abs_div_sub_one hJ
      _ ≤ (P.approximationBudget * (xerr + yerr)) / J := div_le_div_of_nonneg_right hLabs hJ.le
      _ ≤ (P.approximationBudget * (xerr + yerr)) / (normalLaplaceConstant / (1 + z)) := by
        apply div_le_div_of_nonneg_left
        · exact mul_nonneg P.approximationBudget_pos.le (add_nonneg hxerr hyerr)
        · exact div_pos normalLaplaceConstant_pos (by linarith)
        · exact hJlo
      _ = (P.approximationBudget / normalLaplaceConstant) * (1 + z) * (xerr + yerr) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right P.relativeConstant_budget (by linarith)) (add_nonneg hxerr hyerr)
  have hrate0 := P.rate_error htc
  rw [hmean] at hrate0
  have hR : |R| ≤ P.relativeConstant * (n : ℝ) * δ ^ 3 := by
    calc
      _ = (n : ℝ) * |cgf id μ t - t * δ + δ ^ 2 / 2| := by
        dsimp [R]
        rw [abs_mul, abs_of_pos hnp]
      _ ≤ (n : ℝ) * ((P.remainder + P.remainder ^ 2) * t ^ 3) :=
        mul_le_mul_of_nonneg_left hrate0 hnp.le
      _ ≤ (n : ℝ) * ((P.remainder + P.remainder ^ 2) * (2 * δ) ^ 3) := by
        apply mul_le_mul_of_nonneg_left _ hnp.le
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1 ht.2 3)
          (add_nonneg P.remainder_pos.le (sq_nonneg P.remainder))
      _ = (8 * (P.remainder + P.remainder ^ 2)) * ((n : ℝ) * δ ^ 3) := by ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right P.relativeConstant_rate
          (mul_nonneg hnp.le (pow_nonneg hδ.1 3))
        simpa only [mul_assoc] using h
  have hTail := sum_tail_eq_standardized_laplace hdom hv n
  rw [hmean] at hTail
  change (sumLaw μ n).real {x | (n : ℝ) * δ ≤ x} =
    Real.exp ((n : ℝ) * (cgf id μ t - t * δ)) * L at hTail
  have hzsq : z ^ 2 = (n : ℝ) * δ ^ 2 := by
    dsimp [z]
    rw [mul_pow, Real.sq_sqrt hnp.le]
    ring
  have hratio : (sumLaw μ n).real {x | (n : ℝ) * δ ≤ x} / normalTail z = Real.exp R * (L / J) := by
    rw [hTail, normalTail_laplace]
    change (Real.exp ((n : ℝ) * (cgf id μ t - t * δ)) * L) /
      (Real.exp (-(z ^ 2) / 2) * J) = _
    calc
      _ = (Real.exp ((n : ℝ) * (cgf id μ t - t * δ)) / Real.exp (-(z ^ 2) / 2)) * (L / J) := by ring
      _ = Real.exp ((n : ℝ) * (cgf id μ t - t * δ) - (-(z ^ 2) / 2)) * (L / J) := by rw [Real.exp_sub]
      _ = _ := by
        congr 2
        rw [hzsq]
        dsimp [R]
        ring
  have hfinal := multiplicative_perturbation hR hq
  rw [← hratio] at hfinal
  exact hfinal

/-- A finite relative-error form of Cramér–Petrov for a normalized law.
The error is uniform in the normal-deviation parameter `z`; its right-hand
side tends to zero throughout `z=o(n^(1/6))`. -/
theorem cramer_finite_relative_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : StandardCramer μ) :
    ∃ A κ : ℝ, 0 < A ∧ 0 < κ ∧ ∀ (n : ℕ) (z : ℝ), 0 < n → 0 ≤ z → z / Real.sqrt n ≤ κ →
      |(sumLaw μ n).real {x | Real.sqrt n * z ≤ x} / normalTail z - 1| ≤
        Real.exp (A * z ^ 3 / Real.sqrt n) *
          (1 + A * (1 + z) * (z ^ 2 / Real.sqrt n + (n : ℝ) ^ (-(1 / 5 : ℝ)))) - 1 := by
  obtain ⟨P⟩ := exists_tiltControl hμ
  refine ⟨P.relativeConstant, P.radius / 2, P.relativeConstant_pos, half_pos P.radius_pos, ?_⟩
  intro n z hn hz hsmall
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := by positivity
  let δ : ℝ := z / Real.sqrt n
  have hδ : δ ∈ Set.Icc (0 : ℝ) (P.radius / 2) := ⟨div_nonneg hz hsqrt.le, hsmall⟩
  have h := P.relative_tail_bound n hn hδ
  have hzid : δ * Real.sqrt n = z := by dsimp [δ]; field_simp
  have hthreshold : (n : ℝ) * δ = Real.sqrt n * z := by
    dsimp [δ]
    calc
      _ = (Real.sqrt (n : ℝ)) ^ 2 * (z / Real.sqrt n) := by rw [Real.sq_sqrt hnp.le]
      _ = _ := by field_simp
  have hcube : (n : ℝ) * δ ^ 3 = z ^ 3 / Real.sqrt n := by
    dsimp [δ]
    calc
      _ = (Real.sqrt (n : ℝ)) ^ 2 * (z / Real.sqrt n) ^ 3 := by rw [Real.sq_sqrt hnp.le]
      _ = _ := by field_simp
  have hsquare : δ ^ 2 * Real.sqrt n = z ^ 2 / Real.sqrt n := by
    dsimp [δ]
    field_simp
  rw [hzid, hthreshold, mul_assoc P.relativeConstant (n : ℝ), hcube, hsquare] at h
  convert h using 1
  congr 3
  ring

end GaussianTilt.CramerFinite
