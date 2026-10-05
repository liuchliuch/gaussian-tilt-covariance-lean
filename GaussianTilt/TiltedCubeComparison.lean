import GaussianTilt.ModerateDeviations
import GaussianTilt.LaplaceCutoff

/-! # The actual tilted cube and the normal-comparison law

These are measure identities and moment estimates for the concrete tilted
uniform-cube coordinates, not assumptions about an unspecified iid model.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal Topology
namespace GaussianTilt.TiltedCubeComparison
open LowerProbability ModerateDeviations SmoothComparison LaplaceCutoff

lemma mgf_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (u : ℝ) :
    mgf id (μ ∗ ν) u = mgf id μ u * mgf id ν u := by
  rw [mgf, Measure.conv, integral_map (by fun_prop) (by fun_prop)]
  simp only [id_eq, mul_add, Real.exp_add]
  exact integral_prod_mul (fun x : ℝ ↦ Real.exp (u * x)) (fun x : ℝ ↦ Real.exp (u * x))

lemma mgf_sumLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (u : ℝ) :
    mgf id (sumLaw μ n) u = mgf id μ u ^ n := by
  induction n with
  | zero => simp [sumLaw, mgf]
  | succ n ih => rw [sumLaw, mgf_conv, ih, pow_succ']

lemma mgf_exponential_tilt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (t u : ℝ) :
    mgf X (μ.tilted (fun x ↦ t * X x)) u = mgf X μ (t + u) / mgf X μ t := by
  rw [mgf, integral_exp_tilted]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  simp only [Pi.add_apply]
  ring

/-- Centered one-coordinate deficit under the actual exponential family. -/
def centeredDeficitLaw (t : ℝ) : Measure ℝ :=
  (deficitTilt t).map (fun x ↦ coordinateDeficit x - deriv (cgf coordinateDeficit cubeCoordinateLaw) t)

instance centeredDeficitLaw_probability (t : ℝ) : IsProbabilityMeasure (centeredDeficitLaw t) :=
  Measure.isProbabilityMeasure_map (coordinateDeficit_measurable.sub_const _).aemeasurable

lemma deficitTilt_deficit_range (t : ℝ) :
    ∀ᵐ x ∂deficitTilt t, coordinateDeficit x ∈ Set.Icc (-2 : ℝ) 1 :=
  tilted_absolutelyContinuous _ _ coordinateDeficit_range

lemma deficitTilt_deficit_integrable (t : ℝ) : Integrable coordinateDeficit (deficitTilt t) :=
  Integrable.of_mem_Icc (-2) 1 coordinateDeficit_measurable.aemeasurable (deficitTilt_deficit_range t)

lemma deficitTilt_mean_range (t : ℝ) :
    deriv (cgf coordinateDeficit cubeCoordinateLaw) t ∈ Set.Icc (-2 : ℝ) 1 := by
  rw [coordinateDeficit_cgf_deriv]
  have hi := deficitTilt_deficit_integrable t
  constructor
  · have h := integral_mono_ae (integrable_const (-2)) hi ((deficitTilt_deficit_range t).mono fun x hx ↦ hx.1)
    simpa using h
  · have h := integral_mono_ae hi (integrable_const 1) ((deficitTilt_deficit_range t).mono fun x hx ↦ hx.2)
    simpa using h

lemma centeredDeficitLaw_range (t : ℝ) :
    ∀ᵐ x ∂centeredDeficitLaw t, x ∈ Set.Icc (-3 : ℝ) 3 := by
  unfold centeredDeficitLaw
  apply (ae_map_iff (coordinateDeficit_measurable.sub_const _).aemeasurable
    (show MeasurableSet {x : ℝ | x ∈ Set.Icc (-3 : ℝ) 3} from measurableSet_Icc)).mpr
  filter_upwards [deficitTilt_deficit_range t] with x hx
  have hm := deficitTilt_mean_range t
  constructor <;> linarith [hx.1, hx.2, hm.1, hm.2]

lemma centeredDeficitLaw_memLp (t : ℝ) (p : ℝ≥0∞) : MemLp id p (centeredDeficitLaw t) := by
  apply MemLp.of_bound (by fun_prop) 3
  filter_upwards [centeredDeficitLaw_range t] with x hx
  exact abs_le.mpr hx

lemma centeredDeficitLaw_mean (t : ℝ) : ∫ x, x ∂centeredDeficitLaw t = 0 := by
  rw [centeredDeficitLaw, integral_map (coordinateDeficit_measurable.sub_const _).aemeasurable (by fun_prop)]
  rw [integral_sub (deficitTilt_deficit_integrable t) (integrable_const _),
    ← coordinateDeficit_cgf_deriv]
  simp

lemma centeredDeficitLaw_second (t : ℝ) :
    ∫ x, x ^ 2 ∂centeredDeficitLaw t = variance coordinateDeficit (deficitTilt t) := by
  rw [centeredDeficitLaw, integral_map (coordinateDeficit_measurable.sub_const _).aemeasurable (by fun_prop),
    variance_eq_integral coordinateDeficit_measurable.aemeasurable, ← coordinateDeficit_cgf_deriv]

lemma centeredDeficitLaw_third_le (t : ℝ) : thirdMoment (centeredDeficitLaw t) ≤ 27 := by
  have hi := (centeredDeficitLaw_memLp t 3).integrable_norm_pow' (p := 3)
  have h := integral_mono_ae hi (integrable_const 27) ?_
  · simpa only [thirdMoment, id_eq, Real.norm_eq_abs, integral_const, measureReal_univ_eq_one, one_smul] using h
  · filter_upwards [centeredDeficitLaw_range t] with x hx
    have hpow := pow_le_pow_left₀ (abs_nonneg x) (abs_le.mpr hx) 3
    simpa only [id_eq, Real.norm_eq_abs, show (3 : ℝ) ^ 3 = 27 by norm_num] using hpow

lemma mgf_centeredDeficitLaw (t u : ℝ) :
    mgf id (centeredDeficitLaw t) u =
      (mgf coordinateDeficit cubeCoordinateLaw (t + u) / mgf coordinateDeficit cubeCoordinateLaw t) *
        Real.exp (-u * deriv (cgf coordinateDeficit cubeCoordinateLaw) t) := by
  rw [centeredDeficitLaw, mgf_id_map (coordinateDeficit_measurable.sub_const _).aemeasurable]
  simp only [sub_eq_add_neg]
  rw [mgf_add_const, deficitTilt, mgf_exponential_tilt]
  congr 1
  congr 1
  ring

lemma cubeDeficit_mgf (d : ℕ) (u : ℝ) :
    mgf (cubeDeficit d) (cubeLaw d) u = mgf coordinateDeficit cubeCoordinateLaw u ^ d := by
  rw [← exp_cgf (cubeDeficit_exp_integrable d u), cubeDeficit_cgf, Real.exp_nat_mul,
    exp_cgf (coordinateDeficit_exp_integrable u)]

lemma mgf_centeredCube (d : ℕ) (t u : ℝ) :
    mgf (fun x ↦ cubeDeficit d x - (d : ℝ) * deriv (cgf coordinateDeficit cubeCoordinateLaw) t)
      (tiltedDeficitCube d t) u = mgf id (centeredDeficitLaw t) u ^ d := by
  simp only [sub_eq_add_neg]
  rw [mgf_add_const, tiltedDeficitCube, mgf_exponential_tilt,
    cubeDeficit_mgf, cubeDeficit_mgf, mgf_centeredDeficitLaw]
  rw [mul_pow, div_pow]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Exact distributional identification of the centered tilted cube with the
convolution law to which the proved Lindeberg estimate applies. -/
theorem centeredCube_map (d : ℕ) (t : ℝ) :
    (tiltedDeficitCube d t).map
      (fun x ↦ cubeDeficit d x - (d : ℝ) * deriv (cgf coordinateDeficit cubeCoordinateLaw) t) =
      sumLaw (centeredDeficitLaw t) d := by
  let X : (Fin d → ℝ) → ℝ := fun x ↦ cubeDeficit d x -
    (d : ℝ) * deriv (cgf coordinateDeficit cubeCoordinateLaw) t
  have hX : Measurable X := (cubeDeficit_measurable d).sub_const _
  have hmgf : mgf X (tiltedDeficitCube d t) = mgf id (sumLaw (centeredDeficitLaw t) d) := by
    funext u
    rw [mgf_sumLaw]
    exact mgf_centeredCube d t u
  have hexp : integrableExpSet X (tiltedDeficitCube d t) = Set.univ := by
    ext u
    simp only [Set.mem_univ, iff_true]
    apply integrable_exp_mul_of_mem_Icc hX.aemeasurable
    filter_upwards [tilted_absolutelyContinuous (cubeLaw d) (fun x ↦ t * cubeDeficit d x)
      (cubeDeficit_range d)] with x hx
    change X x ∈ Set.Icc (-2 * (d : ℝ) - (d : ℝ) * deriv (cgf coordinateDeficit cubeCoordinateLaw) t)
      ((d : ℝ) - (d : ℝ) * deriv (cgf coordinateDeficit cubeCoordinateLaw) t)
    exact ⟨sub_le_sub_right hx.1 _, sub_le_sub_right hx.2 _⟩
  have hcomplex : complexMGF X (tiltedDeficitCube d t) =
      complexMGF id (sumLaw (centeredDeficitLaw t) d) := by
    funext z
    exact eqOn_complexMGF_of_mgf hmgf (by simp [hexp])
  have h := Measure.ext_of_complexMGF_eq hX.aemeasurable aemeasurable_id hcomplex
  simpa only [Measure.map_id] using h

/-- The tilted coordinate variance is uniformly nondegenerate. -/
theorem deficitTilt_variance_lower {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    meanDeficitConstant ≤ variance coordinateDeficit (deficitTilt t) := by
  let m : ℝ := ∫ x, coordinateDeficit x ∂deficitTilt t
  let Q : ℝ → ℝ := fun x ↦ (coordinateDeficit x - m) ^ 2
  have hLp : MemLp coordinateDeficit 2 cubeCoordinateLaw := by
    apply MemLp.of_bound coordinateDeficit_measurable.aestronglyMeasurable 2
    exact coordinateDeficit_abs_le
  have hQi : Integrable Q cubeCoordinateLaw := (hLp.sub (memLp_const m)).integrable_sq
  have hQt : Integrable Q (deficitTilt t) := by
    have hlp := memLp_tilted_mul (X := coordinateDeficit) (μ := cubeCoordinateLaw)
      (t := t) (by simp [coordinateDeficit_integrableExpSet]) 2
    exact (hlp.sub (memLp_const m)).integrable_sq
  have hweighted : Integrable (fun x ↦ Real.exp (t * coordinateDeficit x) * Q x) cubeCoordinateLaw := by
    simpa only [smul_eq_mul] using
      (integrable_tilted_iff (coordinateDeficit_exp_integrable t) Q).mp hQt
  let M : ℝ := mgf coordinateDeficit cubeCoordinateLaw t
  have hMpos : 0 < M := mgf_pos (coordinateDeficit_exp_integrable t)
  have hMle : M ≤ Real.exp t := by
    have h := integral_mono_ae (coordinateDeficit_exp_integrable t) (integrable_const (Real.exp t)) ?_
    · simpa [M, mgf] using h
    · filter_upwards [coordinateDeficit_range] with x hx
      exact Real.exp_le_exp.mpr (by nlinarith [ht.1, hx.2])
  have hdensity : ∀ᵐ x ∂cubeCoordinateLaw,
      Real.exp (-3) * Q x ≤ (Real.exp (t * coordinateDeficit x) / M) * Q x := by
    filter_upwards [coordinateDeficit_range] with x hx
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply (le_div_iff₀ hMpos).mpr
    calc
      Real.exp (-3) * M ≤ Real.exp (-3) * Real.exp t :=
        mul_le_mul_of_nonneg_left hMle (Real.exp_nonneg _)
      _ = Real.exp (-3 + t) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [ht.1, ht.2, hx.1])
  have hright : Integrable (fun x ↦ (Real.exp (t * coordinateDeficit x) / M) * Q x) cubeCoordinateLaw := by
    convert hweighted.div_const M using 1
    ext x
    ring
  have hi := integral_mono_ae (hQi.const_mul (Real.exp (-3))) hright hdensity
  rw [integral_const_mul] at hi
  have hvar0 : variance coordinateDeficit cubeCoordinateLaw = (4 / 5 : ℝ) := by
    rw [variance_eq_integral coordinateDeficit_measurable.aemeasurable, coordinateDeficit_mean]
    simpa using coordinateDeficit_secondMoment
  have hq := variance_le_expectation_sq
    ((coordinateDeficit_measurable.sub_const m).aestronglyMeasurable (μ := cubeCoordinateLaw))
  rw [variance_sub_const coordinateDeficit_measurable.aestronglyMeasurable m, hvar0] at hq
  have hvar : variance coordinateDeficit (deficitTilt t) =
      ∫ x, (Real.exp (t * coordinateDeficit x) / M) * Q x ∂cubeCoordinateLaw := by
    rw [variance_eq_integral coordinateDeficit_measurable.aemeasurable]
    change (∫ x, Q x ∂deficitTilt t) = _
    rw [deficitTilt, integral_tilted]
    rfl
  rw [← hvar] at hi
  unfold meanDeficitConstant
  simpa only [mul_comm] using (mul_le_mul_of_nonneg_left hq (Real.exp_nonneg (-3))).trans hi

/-- A simple exponential-moment estimate supplies a uniform Gaussian third
moment, avoiding a guessed numerical normal moment. -/
lemma gaussian_thirdMoment_le {v : ℝ≥0} (hv : (v : ℝ) ≤ 9 / 4) :
    thirdMoment (gaussianReal 0 v) ≤ 12 * Real.exp (9 / 8 : ℝ) := by
  have hpoint (x : ℝ) : |x| ^ 3 ≤ 6 * (Real.exp x + Real.exp (-x)) := by
    have hp := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) 3
    norm_num [Nat.factorial] at hp
    have he : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        exact le_add_of_nonneg_right (Real.exp_nonneg _)
      · rw [abs_of_nonpos hx]
        exact le_add_of_nonneg_left (Real.exp_nonneg _)
    nlinarith
  have hp : Integrable (fun x : ℝ ↦ Real.exp x) (gaussianReal 0 v) := by
    simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := v) 1
  have hn : Integrable (fun x : ℝ ↦ Real.exp (-x)) (gaussianReal 0 v) := by
    simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-1)
  have hi := integral_mono (gaussian_third_moment_integrable v) ((hp.add hn).const_mul 6) hpoint
  rw [integral_const_mul] at hi
  simp only [Pi.add_apply] at hi
  rw [integral_add hp hn] at hi
  have h1 : (∫ x : ℝ, Real.exp x ∂gaussianReal 0 v) = Real.exp ((v : ℝ) / 2) := by
    simpa [mgf, id_eq] using congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) 1
  have h2 : (∫ x : ℝ, Real.exp (-x) ∂gaussianReal 0 v) = Real.exp ((v : ℝ) / 2) := by
    simpa [mgf, id_eq] using congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) (-1)
  rw [h1, h2] at hi
  have he : Real.exp ((v : ℝ) / 2) ≤ Real.exp (9 / 8 : ℝ) := Real.exp_le_exp.mpr (by linarith)
  dsimp [thirdMoment] at *
  nlinarith

/-- Exact exponential-tilt identity for a tail, including its one-sided Laplace
factor. It holds for the original measure, not for an abstract tail function. -/
theorem tail_eq_tilted_laplace {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (t a : ℝ) (hi : Integrable (fun x ↦ Real.exp (t * X x)) μ) :
    μ.real {x | a ≤ X x} = Real.exp (cgf X μ t - t * a) *
      oneSidedLaplace ((μ.tilted (fun x ↦ t * X x)).map (fun x ↦ X x - a)) t := by
  let A : Set Ω := {x | a ≤ X x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hX
  have hXsub : Measurable (fun x ↦ X x - a) := hX.sub_const a
  have hM : 0 < mgf X μ t := mgf_pos hi
  have hmap : oneSidedLaplace ((μ.tilted (fun x ↦ t * X x)).map (fun x ↦ X x - a)) t =
      ∫ x in A, Real.exp (-t * (X x - a)) ∂μ.tilted (fun x ↦ t * X x) := by
    unfold oneSidedLaplace
    rw [← integral_indicator measurableSet_Ici,
      integral_map hXsub.aemeasurable
        ((show Measurable (fun x : ℝ ↦ Real.exp (-t * x)) by fun_prop).aestronglyMeasurable.indicator measurableSet_Ici),
      ← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : a ≤ X x
    · simp [A, hx, sub_nonneg.mpr hx]
    · have hn : ¬ 0 ≤ X x - a := by linarith
      simp [A, hx, hn]
  have hformula : oneSidedLaplace ((μ.tilted (fun x ↦ t * X x)).map (fun x ↦ X x - a)) t =
      μ.real A * (Real.exp (t * a) / mgf X μ t) := by
    rw [hmap, setIntegral_tilted _ _ A]
    have heq (x : Ω) : (Real.exp (t * X x) / mgf X μ t) • Real.exp (-t * (X x - a)) =
        Real.exp (t * a) / mgf X μ t := by
      rw [smul_eq_mul, div_mul_eq_mul_div, ← Real.exp_add]
      congr 2
      ring
    simp only [mgf] at heq
    simp_rw [heq]
    rw [setIntegral_const, smul_eq_mul]
    rfl
  rw [hformula, Real.exp_sub, exp_cgf hi]
  change μ.real A = _
  field_simp

/-- The precise saddlepoint representation for the actual cube tail. -/
theorem cubeDeficit_tail_eq_laplace (d : ℕ) (t : ℝ) :
    (cubeLaw d).real {x | (d : ℝ) * deriv (cgf coordinateDeficit cubeCoordinateLaw) t ≤ cubeDeficit d x} =
      Real.exp ((d : ℝ) * (cgf coordinateDeficit cubeCoordinateLaw t -
        t * deriv (cgf coordinateDeficit cubeCoordinateLaw) t)) *
      oneSidedLaplace (sumLaw (centeredDeficitLaw t) d) t := by
  rw [tail_eq_tilted_laplace (cubeLaw d) (cubeDeficit d) (cubeDeficit_measurable d)
    t _ (cubeDeficit_exp_integrable d t)]
  change _ * oneSidedLaplace ((tiltedDeficitCube d t).map _) t = _
  rw [centeredCube_map, cubeDeficit_cgf]
  congr 2
  ring

end GaussianTilt.TiltedCubeComparison
