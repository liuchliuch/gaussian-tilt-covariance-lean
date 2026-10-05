import GaussianTilt.LaplaceComparison
import Mathlib.Probability.Moments.Tilted

/-! # Analytic estimates for a general Cramér law

Only the original probability, centering, variance and local exponential-moment
assumptions are used. Local Taylor estimates are derived from the actual CGF.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal Topology
namespace GaussianTilt.CramerAnalytic

/-- The normalized hypotheses of the Cramér–Petrov theorem. -/
structure StandardCramer (μ : Measure ℝ) : Prop where
  mean_zero : ∫ x, x ∂μ = 0
  variance_one : variance id μ = 1
  cramer : 0 ∈ interior (integrableExpSet id μ)

lemma cgf_deriv_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : StandardCramer μ) :
    deriv (cgf id μ) 0 = 0 := by
  rw [deriv_cgf_zero hμ.cramer]
  simpa using hμ.mean_zero

lemma cgf_second_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : StandardCramer μ) :
    iteratedDeriv 2 (cgf id μ) 0 = 1 := by
  rw [← variance_tilted_mul hμ.cramer]
  simpa using hμ.variance_one

/-- Three local Taylor controls derived solely from analyticity and a bounded
third derivative. The constants need not be sharp. -/
lemma analytic_cubic_control {f : ℝ → ℝ} {η C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ x ∈ Set.Icc (0 : ℝ) η, AnalyticAt ℝ f x)
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0) (hf2 : iteratedDeriv 2 f 0 = 1)
    (hthird : ∀ x ∈ Set.Icc (0 : ℝ) η, |iteratedDeriv 3 f x| ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) η,
      |iteratedDeriv 2 f t - 1| ≤ C * t ∧
      |deriv f t - t| ≤ C * t ^ 2 ∧
      |f t - t ^ 2 / 2| ≤ C * t ^ 3 := by
  have hsecond (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) η) :
      |iteratedDeriv 2 f t - 1| ≤ C * t := by
    have hdiff (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) t) :
        DifferentiableAt ℝ (iteratedDeriv 2 f) x := by
      have h := (ha x ⟨hx.1, hx.2.trans ht.2⟩).deriv.deriv.differentiableAt
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h
    have hb (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) t) :
        ‖deriv (iteratedDeriv 2 f) x‖ ≤ C := by
      simpa only [← iteratedDeriv_succ, Real.norm_eq_abs] using hthird x ⟨hx.1, hx.2.trans ht.2⟩
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb (convex_Icc 0 t)
      (x := 0) (y := t) ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩
    simpa only [hf2, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] using h
  have hfirst (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) η) :
      |deriv f t - t| ≤ C * t ^ 2 := by
    let g : ℝ → ℝ := fun x ↦ deriv f x - x
    have hg (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) t) :
        HasDerivAt g (iteratedDeriv 2 f x - 1) x := by
      convert (ha x ⟨hx.1, hx.2.trans ht.2⟩).deriv.differentiableAt.hasDerivAt.sub (hasDerivAt_id x) using 1
      simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    have hb (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) t) : ‖deriv g x‖ ≤ C * t := by
      rw [(hg x hx).deriv, Real.norm_eq_abs]
      exact (hsecond x ⟨hx.1, hx.2.trans ht.2⟩).trans (mul_le_mul_of_nonneg_left hx.2 hC)
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (fun x hx ↦ (hg x hx).differentiableAt)
      hb (convex_Icc 0 t) (x := 0) (y := t) ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩
    simpa only [g, hf1, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1, mul_assoc, ← pow_two] using h
  intro t ht
  refine ⟨hsecond t ht, hfirst t ht, ?_⟩
  let g : ℝ → ℝ := fun x ↦ f x - x ^ 2 / 2
  have hg (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) t) :
      HasDerivAt g (deriv f x - x) x := by
    convert (ha x ⟨hx.1, hx.2.trans ht.2⟩).differentiableAt.hasDerivAt.sub
      (((hasDerivAt_id x).pow 2).div_const 2) using 1
    dsimp
    ring
  have hb (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) t) : ‖deriv g x‖ ≤ C * t ^ 2 := by
    rw [(hg x hx).deriv, Real.norm_eq_abs]
    exact (hfirst x ⟨hx.1, hx.2.trans ht.2⟩).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hx.2 2) hC)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (fun x hx ↦ (hg x hx).differentiableAt)
    hb (convex_Icc 0 t) (x := 0) (y := t) ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩
  convert h using 1
  · simp [g, hf0, Real.norm_eq_abs]
  · rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1]
    ring

/-- Existence of all local cumulant controls, derived from the Cramér
exponential-moment assumption rather than postulated as analytic inputs. -/
theorem exists_cgf_local_control {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : StandardCramer μ) :
    ∃ η C : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < C ∧
      ∀ t ∈ Set.Icc (0 : ℝ) η,
        t ∈ interior (integrableExpSet id μ) ∧
        |iteratedDeriv 2 (cgf id μ) t - 1| ≤ C * t ∧
        |deriv (cgf id μ) t - t| ≤ C * t ^ 2 ∧
        |cgf id μ t - t ^ 2 / 2| ≤ C * t ^ 3 ∧
        (1 / 2 : ℝ) ≤ iteratedDeriv 2 (cgf id μ) t ∧
        iteratedDeriv 2 (cgf id μ) t ≤ 2 ∧
        t / 2 ≤ deriv (cgf id μ) t ∧ deriv (cgf id μ) t ≤ 2 * t := by
  have hn : interior (integrableExpSet id μ) ∈ 𝓝 (0 : ℝ) :=
    isOpen_interior.mem_nhds hμ.cramer
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  let b : ℝ := min 1 (r / 2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbi : Set.Icc (0 : ℝ) b ⊆ interior (integrableExpSet id μ) := by
    intro t ht
    apply hball
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    have hh : b ≤ r / 2 := min_le_right _ _
    linarith [ht.2]
  have ha (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) : AnalyticAt ℝ (cgf id μ) t :=
    analyticAt_cgf (hbi ht)
  have hcont : ContinuousOn (iteratedDeriv 3 (cgf id μ)) (Set.Icc (0 : ℝ) b) := by
    intro t ht
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (ha t ht).deriv.deriv.deriv.continuousAt.continuousWithinAt (s := Set.Icc (0 : ℝ) b)
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let C : ℝ := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hthird (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) : |iteratedDeriv 3 (cgf id μ) t| ≤ C :=
    (hC₀ t ht).trans (le_max_left _ _)
  have hTaylor := analytic_cubic_control hC.le ha (by simp) (cgf_deriv_zero hμ)
    (cgf_second_zero hμ) hthird
  let η : ℝ := min b (1 / (2 * C))
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, C, hη, (min_le_left _ _).trans (min_le_left _ _), hC, ?_⟩
  intro t ht
  have htb : t ∈ Set.Icc (0 : ℝ) b := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have hct : C * t ≤ 1 / 2 := by
    have hh := ht.2.trans (min_le_right b (1 / (2 * C)))
    have hi := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp hh
    nlinarith
  obtain ⟨h2, h1, h0⟩ := hTaylor t htb
  have hh2 := abs_le.mp h2
  have hh1 := abs_le.mp h1
  have hm : C * t ^ 2 ≤ t / 2 := by nlinarith [mul_le_mul_of_nonneg_right hct ht.1]
  exact ⟨hbi htb, h2, h1, h0, by linarith, by linarith, by linarith, by linarith⟩

end GaussianTilt.CramerAnalytic
