import GaussianTilt.CramerAnalytic
import GaussianTilt.TiltedCubeComparison

/-! # Standardized exponential families for general Cramér laws -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal Topology
namespace GaussianTilt.StandardizedTilt
open CramerAnalytic TiltedCubeComparison SmoothComparison

/-- The actual tilted coordinate, recentered and normalized by its CGF variance. -/
def law (μ : Measure ℝ) (t : ℝ) : Measure ℝ :=
  (μ.tilted (fun x ↦ t * x)).map
    (fun x ↦ (x - deriv (cgf id μ) t) / Real.sqrt (iteratedDeriv 2 (cgf id μ) t))

lemma law_probability {μ : Measure ℝ} [IsProbabilityMeasure μ] {t : ℝ}
    (ht : t ∈ interior (integrableExpSet id μ)) : IsProbabilityMeasure (law μ t) := by
  have hiExp : Integrable (fun x : ℝ ↦ Real.exp (t * x)) μ :=
    interior_subset (s := integrableExpSet id μ) ht
  haveI := isProbabilityMeasure_tilted hiExp
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma law_memLp {μ : Measure ℝ} [IsProbabilityMeasure μ] {t : ℝ}
    (ht : t ∈ interior (integrableExpSet id μ)) (p : ℝ≥0) : MemLp id p (law μ t) := by
  have hiExp : Integrable (fun x : ℝ ↦ Real.exp (t * x)) μ :=
    interior_subset (s := integrableExpSet id μ) ht
  haveI := isProbabilityMeasure_tilted hiExp
  rw [law, memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  have h := (memLp_tilted_mul ht p).sub (memLp_const (deriv (cgf id μ) t))
  convert h.const_mul (Real.sqrt (iteratedDeriv 2 (cgf id μ) t))⁻¹ using 1
  ext x
  simp only [Function.comp_def, id_def, Pi.sub_apply]
  ring

lemma law_mean {μ : Measure ℝ} [IsProbabilityMeasure μ] {t : ℝ}
    (ht : t ∈ interior (integrableExpSet id μ)) : ∫ x, x ∂law μ t = 0 := by
  have hiExp : Integrable (fun x : ℝ ↦ Real.exp (t * x)) μ :=
    interior_subset (s := integrableExpSet id μ) ht
  haveI := isProbabilityMeasure_tilted hiExp
  have hi : Integrable (fun x : ℝ ↦ x) (μ.tilted (fun x ↦ t * x)) :=
    (memLp_tilted_mul ht 1).integrable le_rfl
  rw [law, integral_map (by fun_prop) (by fun_prop), integral_div,
    integral_sub hi (integrable_const _)]
  have hm := integral_tilted_mul_self ht
  simp only [id_eq] at hm
  simp [hm]

lemma law_second {μ : Measure ℝ} [IsProbabilityMeasure μ] {t : ℝ}
    (ht : t ∈ interior (integrableExpSet id μ))
    (hv : 0 < iteratedDeriv 2 (cgf id μ) t) : ∫ x, x ^ 2 ∂law μ t = 1 := by
  have hiExp : Integrable (fun x : ℝ ↦ Real.exp (t * x)) μ :=
    interior_subset (s := integrableExpSet id μ) ht
  haveI := isProbabilityMeasure_tilted hiExp
  rw [law, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [div_pow]
  rw [integral_div, Real.sq_sqrt hv.le]
  have hm := integral_tilted_mul_self ht
  have hvar := variance_tilted_mul ht
  rw [variance_eq_integral (by fun_prop), hm] at hvar
  simpa only [id_eq, hvar, div_self hv.ne'] using congrArg
    (fun x : ℝ ↦ x / iteratedDeriv 2 (cgf id μ) t) hvar

lemma law_third_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ] {t : ℝ}
    (ht : t ∈ interior (integrableExpSet id μ)) :
    Integrable (fun x : ℝ ↦ |x| ^ 3) (law μ t) := by
  haveI := law_probability ht
  simpa only [id_eq, Real.norm_eq_abs] using (law_memLp ht 3).integrable_norm_pow' (p := 3)

lemma one_le_mgf {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : StandardCramer μ) {t : ℝ}
    (ht : t ∈ integrableExpSet id μ) : 1 ≤ mgf id μ t := by
  have hi : Integrable (fun x : ℝ ↦ x) μ :=
    (memLp_of_mem_interior_integrableExpSet hμ.cramer 1).integrable le_rfl
  have hb := integral_mono ((hi.const_mul t).add (integrable_const 1)) ht
    (fun x ↦ Real.add_one_le_exp (t * x))
  simp only [Pi.add_apply] at hb
  rw [integral_add (hi.const_mul t) (integrable_const 1), integral_const_mul, hμ.mean_zero] at hb
  simpa [mgf] using hb

/-- MGF uniqueness requires only a neighborhood of the origin, not entire
exponential moments. -/
lemma map_eq_of_mgf {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    (h0 : 0 ∈ interior (integrableExpSet X μ)) (hM : mgf X μ = mgf Y ν) :
    μ.map X = ν.map Y := by
  apply Measure.ext_of_charFun
  funext u
  rw [← complexMGF_mul_I hX, ← complexMGF_mul_I hY]
  exact eqOn_complexMGF_of_mgf hM (by simpa using h0)

lemma cramer_affine {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (h0 : 0 ∈ interior (integrableExpSet X μ)) (c b : ℝ) :
    0 ∈ interior (integrableExpSet (fun x ↦ c * X x + b) μ) := by
  rw [mem_interior_iff_mem_nhds] at h0 ⊢
  have hpre : ∀ᶠ u in 𝓝 (0 : ℝ), u * c ∈ integrableExpSet X μ := by
    have h : Tendsto (fun u : ℝ ↦ u * c) (𝓝 0) (𝓝 0) := by
      simpa only [zero_mul] using (continuous_id.mul continuous_const).tendsto (0 : ℝ) (f := fun u : ℝ ↦ u * c)
    exact h.eventually h0
  filter_upwards [hpre] with u hu
  change Integrable (fun x ↦ Real.exp (u * c * X x)) μ at hu
  change Integrable (fun x ↦ Real.exp (u * (c * X x + b))) μ
  have hi := hu.const_mul (Real.exp (u * b))
  convert hi using 1
  ext x
  rw [← Real.exp_add]
  congr 1
  ring

lemma cramer_tilt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {t : ℝ}
    (ht : t ∈ interior (integrableExpSet X μ)) :
    0 ∈ interior (integrableExpSet X (μ.tilted (fun x ↦ t * X x))) := by
  have hi : Integrable (fun x ↦ Real.exp (t * X x)) μ := interior_subset (s := integrableExpSet X μ) ht
  rw [mem_interior_iff_mem_nhds] at ht ⊢
  have hpre : ∀ᶠ u in 𝓝 (0 : ℝ), t + u ∈ integrableExpSet X μ := by
    have h : Tendsto (fun u : ℝ ↦ t + u) (𝓝 0) (𝓝 t) := by
      simpa only [add_zero] using (continuous_const.add continuous_id).tendsto (0 : ℝ) (f := fun u : ℝ ↦ t + u)
    exact h.eventually ht
  filter_upwards [hpre] with u hu
  change Integrable (fun x ↦ Real.exp (u * X x)) (μ.tilted (fun x ↦ t * X x))
  change Integrable (fun x ↦ Real.exp ((t + u) * X x)) μ at hu
  apply (integrable_tilted_iff hi (fun x ↦ Real.exp (u * X x))).mpr
  convert hu using 1
  ext x
  rw [smul_eq_mul, ← Real.exp_add]
  congr 1
  ring

lemma normalized_cube_pointwise {m v : ℝ} (hm : |m| ≤ 2) (hv : (1 / 2 : ℝ) ≤ v) (x : ℝ) :
    |(x - m) / Real.sqrt v| ^ 3 ≤ 32 * |x| ^ 3 + 256 := by
  have hvp : 0 < v := by linarith
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hvp
  have hsq := Real.sq_sqrt hvp.le
  have hslo : (1 / 2 : ℝ) ≤ Real.sqrt v := by nlinarith [Real.sqrt_nonneg v]
  have hnum : |x - m| ≤ |x| + 2 := (abs_sub _ _).trans (by linarith)
  have hnorm : |(x - m) / Real.sqrt v| ≤ 2 * (|x| + 2) := by
    rw [abs_div, abs_of_pos hs]
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_le_mul_of_nonneg_left hslo (show 0 ≤ 2 * (|x| + 2) by positivity)]
  have hp := pow_le_pow_left₀ (abs_nonneg _) hnorm 3
  have hpol : (|x| + 2) ^ 3 ≤ 4 * |x| ^ 3 + 32 := by
    nlinarith [mul_nonneg (show 0 ≤ |x| + 2 by positivity) (sq_nonneg (|x| - 2))]
  nlinarith

lemma exp_tilt_le_dom {η t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) η) (x : ℝ) :
    Real.exp (t * x) ≤ 1 + Real.exp (η * x) := by
  rcases le_total 0 x with hx | hx
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.2 hx)).trans
      (le_add_of_nonneg_left zero_le_one)
  · exact (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ht.1 hx)).trans
      (le_add_of_nonneg_right (Real.exp_nonneg _))

/-- A locally uniform third-moment budget for the actual standardized tilt
family. The domination is constructed from exponential moments at the endpoint. -/
theorem exists_third_moment_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : StandardCramer μ) {η : ℝ} (hη : 0 < η)
    (hdom : ∀ t ∈ Set.Icc (0 : ℝ) η, t ∈ interior (integrableExpSet id μ))
    (hmean : ∀ t ∈ Set.Icc (0 : ℝ) η, |deriv (cgf id μ) t| ≤ 2)
    (hvar : ∀ t ∈ Set.Icc (0 : ℝ) η, (1 / 2 : ℝ) ≤ iteratedDeriv 2 (cgf id μ) t) :
    ∃ M > 0, ∀ t ∈ Set.Icc (0 : ℝ) η, thirdMoment (law μ t) ≤ M := by
  let D : ℝ → ℝ := fun x ↦ (32 * |x| ^ 3 + 256) * (1 + Real.exp (η * x))
  have hηdom := hdom η ⟨hη.le, le_rfl⟩
  have hi3 : Integrable (fun x : ℝ ↦ |x| ^ 3) μ := by
    simpa only [id_eq, Real.norm_eq_abs] using
      (memLp_of_mem_interior_integrableExpSet hμ.cramer 3).integrable_norm_pow' (p := 3)
  have hie : Integrable (fun x : ℝ ↦ Real.exp (η * x)) μ :=
    interior_subset (s := integrableExpSet id μ) hηdom
  have hi3e : Integrable (fun x : ℝ ↦ |x| ^ 3 * Real.exp (η * x)) μ := by
    simpa only [id_eq] using integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet hηdom 3
  have hiD : Integrable D μ := by
    convert (((hi3.const_mul 32).add (integrable_const 256)).add
      ((hi3e.const_mul 32).add (hie.const_mul 256))) using 1
    ext x
    dsimp [D]
    ring
  have hD : ∀ x, 0 ≤ D x := by intro x; dsimp [D]; positivity
  have hInt : (0 : ℝ) ≤ ∫ x, D x ∂μ := integral_nonneg hD
  refine ⟨(∫ x, D x ∂μ) + 1, by linarith only [hInt], ?_⟩
  intro t ht
  have htdom := hdom t ht
  let m : ℝ := deriv (cgf id μ) t
  let v : ℝ := iteratedDeriv 2 (cgf id μ) t
  let Z : ℝ → ℝ := fun x ↦ (x - m) / Real.sqrt v
  let A : ℝ := mgf id μ t
  have hA : 1 ≤ A := one_le_mgf hμ (interior_subset (s := integrableExpSet id μ) htdom)
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hpoint (x : ℝ) : (Real.exp (t * x) / A) * |Z x| ^ 3 ≤ D x := by
    have hpoly := normalized_cube_pointwise (hmean t ht) (hvar t ht) x
    have hExp := exp_tilt_le_dom ht x
    calc
      _ ≤ Real.exp (t * x) * |Z x| ^ 3 :=
        mul_le_mul_of_nonneg_right (div_le_self (Real.exp_nonneg _) hA) (by positivity)
      _ ≤ Real.exp (t * x) * (32 * |x| ^ 3 + 256) :=
        mul_le_mul_of_nonneg_left hpoly (Real.exp_nonneg _)
      _ ≤ (1 + Real.exp (η * x)) * (32 * |x| ^ 3 + 256) :=
        mul_le_mul_of_nonneg_right hExp (by positivity)
      _ = D x := by dsimp [D]; ring
  have hiL : Integrable (fun x ↦ (Real.exp (t * x) / A) * |Z x| ^ 3) μ := by
    apply hiD.mono' (by fun_prop)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpoint x
  have hh := integral_mono hiL hiD hpoint
  have heq : thirdMoment (law μ t) =
      ∫ x, (Real.exp (t * x) / A) * |Z x| ^ 3 ∂μ := by
    rw [thirdMoment, law, integral_map (by fun_prop) (by fun_prop), integral_tilted]
    rfl
  rw [← heq] at hh
  linarith

lemma mgf_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (c b u : ℝ) :
    mgf (fun x ↦ c * X x + b) μ u = mgf X μ (u * c) * Real.exp (u * b) := by
  rw [mgf, mgf, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← Real.exp_add]
  congr 1
  ring

lemma mgf_id_exponential_tilt (μ : Measure ℝ) (t u : ℝ) :
    mgf id (μ.tilted (fun x ↦ t * x)) u = mgf id μ (t + u) / mgf id μ t := by
  simpa only [id_eq] using mgf_exponential_tilt μ id t u

lemma mgf_law (μ : Measure ℝ) (t u : ℝ) :
    mgf id (law μ t) u =
      mgf id μ (t + u * (Real.sqrt (iteratedDeriv 2 (cgf id μ) t))⁻¹) / mgf id μ t *
        Real.exp (u * (-deriv (cgf id μ) t * (Real.sqrt (iteratedDeriv 2 (cgf id μ) t))⁻¹)) := by
  rw [law, mgf_id_map (by fun_prop)]
  have heq : (fun x : ℝ ↦ (x - deriv (cgf id μ) t) / Real.sqrt (iteratedDeriv 2 (cgf id μ) t)) =
      fun x ↦ (Real.sqrt (iteratedDeriv 2 (cgf id μ) t))⁻¹ * id x +
        (-deriv (cgf id μ) t * (Real.sqrt (iteratedDeriv 2 (cgf id μ) t))⁻¹) := by
    funext x
    simp only [id_eq]
    ring
  rw [heq, mgf_affine, mgf_id_exponential_tilt]

lemma interior_integrableExpSet_sumLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {t : ℝ} (ht : t ∈ interior (integrableExpSet id μ)) (n : ℕ) :
    t ∈ interior (integrableExpSet id (sumLaw μ n)) := by
  apply interior_mono _ ht
  intro u hu
  change Integrable (fun x : ℝ ↦ Real.exp (u * id x)) (sumLaw μ n)
  apply mgf_pos_iff.mp
  rw [mgf_sumLaw]
  exact pow_pos (mgf_pos hu) n

lemma cramer_law {μ : Measure ℝ} [IsProbabilityMeasure μ] {t : ℝ}
    (ht : t ∈ interior (integrableExpSet id μ)) :
    0 ∈ interior (integrableExpSet id (law μ t)) := by
  haveI := law_probability ht
  have hM := mgf_id_map (μ := μ.tilted (fun x ↦ t * x))
    (show AEMeasurable (fun x : ℝ ↦ (x - deriv (cgf id μ) t) /
      Real.sqrt (iteratedDeriv 2 (cgf id μ) t)) _ by fun_prop)
  change mgf id (law μ t) = mgf
    (fun x : ℝ ↦ (x - deriv (cgf id μ) t) / Real.sqrt (iteratedDeriv 2 (cgf id μ) t))
    (μ.tilted (fun x ↦ t * x)) at hM
  rw [integrableExpSet_eq_of_mgf hM]
  have h := cramer_affine (cramer_tilt ht)
    (Real.sqrt (iteratedDeriv 2 (cgf id μ) t))⁻¹
    (-deriv (cgf id μ) t * (Real.sqrt (iteratedDeriv 2 (cgf id μ) t))⁻¹)
  convert h using 1
  congr 2
  funext x
  simp only [id_eq]
  ring

/-- The standardized sum under the global tilt is exactly the convolution
power of the actual standardized one-coordinate tilted law. -/
theorem normalized_sum_map {μ : Measure ℝ} [IsProbabilityMeasure μ] {t : ℝ}
    (ht : t ∈ interior (integrableExpSet id μ)) (n : ℕ) :
    ((sumLaw μ n).tilted (fun x ↦ t * x)).map
      (fun x ↦ (x - (n : ℝ) * deriv (cgf id μ) t) / Real.sqrt (iteratedDeriv 2 (cgf id μ) t)) =
      sumLaw (law μ t) n := by
  have htSum := interior_integrableExpSet_sumLaw ht n
  have hiSum : Integrable (fun x : ℝ ↦ Real.exp (t * x)) (sumLaw μ n) :=
    interior_subset (s := integrableExpSet id (sumLaw μ n)) htSum
  haveI := isProbabilityMeasure_tilted hiSum
  haveI := law_probability ht
  let m := deriv (cgf id μ) t
  let σ := Real.sqrt (iteratedDeriv 2 (cgf id μ) t)
  let X : ℝ → ℝ := fun x ↦ (x - (n : ℝ) * m) / σ
  have heq : X = fun x ↦ σ⁻¹ * id x + (-(n : ℝ) * m * σ⁻¹) := by
    funext x
    dsimp [X]
    ring
  have hM : mgf X ((sumLaw μ n).tilted (fun x ↦ t * x)) = mgf id (sumLaw (law μ t) n) := by
    funext u
    rw [heq, mgf_affine, mgf_id_exponential_tilt, mgf_sumLaw, mgf_sumLaw, mgf_sumLaw, mgf_law,
      mul_pow, div_pow]
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [σ, m]
    ring
  have h0 : 0 ∈ interior (integrableExpSet X ((sumLaw μ n).tilted (fun x ↦ t * x))) := by
    rw [heq]
    exact cramer_affine (cramer_tilt htSum) σ⁻¹ (-(n : ℝ) * m * σ⁻¹)
  have h := map_eq_of_mgf (show AEMeasurable X _ by dsimp [X]; fun_prop) aemeasurable_id h0 hM
  simpa only [Measure.map_id] using h

lemma cgf_sumLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (t : ℝ) :
    cgf id (sumLaw μ n) t = (n : ℝ) * cgf id μ t := by
  rw [cgf, mgf_sumLaw, Real.log_pow]
  rfl

end GaussianTilt.StandardizedTilt
