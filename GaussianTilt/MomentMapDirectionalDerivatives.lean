import GaussianTilt.MomentMapConvexDifferentiability

/-! # Measurable directional derivatives of finite convex potentials

Both one-sided directional derivatives are constructed as limits of the
continuous rational-step difference quotients. Their measurability is proved
before any Fubini step is applied to the differentiability set.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

def affineLine (φ : E n → ℝ) (v x : E n) (t : ℝ) : ℝ := φ (x + t • v)
def rightDirectional (φ : E n → ℝ) (v x : E n) : ℝ :=
  derivWithin (affineLine φ v x) (Ioi 0) 0
def leftDirectional (φ : E n → ℝ) (v x : E n) : ℝ :=
  derivWithin (affineLine φ v x) (Iio 0) 0

lemma convex_affineLine {φ : E n → ℝ} (hφ : ConvexOn ℝ univ φ) (v x : E n) :
    ConvexOn ℝ univ (affineLine φ v x) := by
  refine ⟨convex_univ, ?_⟩
  intro s _ t _ a b ha hb hab
  have he : a • (x + s • v) + b • (x + t • v) = x + (a * s + b * t) • v := by
    calc
      _ = (a + b) • x + (a * s + b * t) • v := by module
      _ = _ := by rw [hab, one_smul]
  have h := hφ.2 (mem_univ (x + s • v)) (mem_univ (x + t • v)) ha hb hab
  simpa only [he, affineLine, smul_eq_mul] using h

lemma convex_potential_continuous {φ : E n → ℝ} (hφ : ConvexOn ℝ univ φ) : Continuous φ :=
  continuousOn_univ.mp (hφ.continuousOn isOpen_univ)

lemma reciprocal_tendsto_right_zero :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝[Ioi 0] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop), ?_⟩
  exact Filter.Eventually.of_forall (fun k => by simp only [mem_Ioi]; positivity)

lemma neg_reciprocal_tendsto_left_zero :
    Tendsto (fun k : ℕ => -((k : ℝ) + 1)⁻¹) atTop (𝓝[Iio 0] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (tendsto_nhdsWithin_iff.mp reciprocal_tendsto_right_zero).1.neg
  · exact Filter.Eventually.of_forall (fun k =>
      neg_neg_of_pos (by positivity : 0 < ((k : ℝ) + 1)⁻¹))

theorem measurable_rightDirectional {φ : E n → ℝ} (hφ : ConvexOn ℝ univ φ) (v : E n) :
    Measurable (rightDirectional φ v) := by
  let F : ℕ → E n → ℝ := fun k x =>
    (φ (x + ((k : ℝ) + 1)⁻¹ • v) - φ x) / ((k : ℝ) + 1)⁻¹
  have hm (k : ℕ) : Measurable (F k) := by
    have hcont := convex_potential_continuous hφ
    dsimp [F]
    fun_prop
  apply measurable_of_tendsto_metrizable hm
  apply tendsto_pi_nhds.mpr
  intro x
  have h := (convex_affineLine hφ v x).hasDerivWithinAt_rightDeriv_of_mem_interior
    (by simp : (0 : ℝ) ∈ interior (univ : Set ℝ))
  have ht := ((hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp h).comp reciprocal_tendsto_right_zero
  simpa only [Function.comp_def, F, rightDirectional, slope_def_field, sub_zero, affineLine,
    zero_smul, add_zero] using ht

theorem measurable_leftDirectional {φ : E n → ℝ} (hφ : ConvexOn ℝ univ φ) (v : E n) :
    Measurable (leftDirectional φ v) := by
  let F : ℕ → E n → ℝ := fun k x =>
    (φ (x + (-((k : ℝ) + 1)⁻¹) • v) - φ x) / (-((k : ℝ) + 1)⁻¹)
  have hm (k : ℕ) : Measurable (F k) := by
    have hcont := convex_potential_continuous hφ
    dsimp [F]
    fun_prop
  apply measurable_of_tendsto_metrizable hm
  apply tendsto_pi_nhds.mpr
  intro x
  have h := (convex_affineLine hφ v x).hasDerivWithinAt_leftDeriv_of_mem_interior
    (by simp : (0 : ℝ) ∈ interior (univ : Set ℝ))
  have ht := ((hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp h).comp neg_reciprocal_tendsto_left_zero
  simpa only [Function.comp_def, F, leftDirectional, slope_def_field, sub_zero, affineLine,
    zero_smul, add_zero] using ht

lemma differentiable_affineLine_iff {φ : E n → ℝ} (hφ : ConvexOn ℝ univ φ) (v x : E n) :
    DifferentiableAt ℝ (affineLine φ v x) 0 ↔ leftDirectional φ v x = rightDirectional φ v x := by
  constructor
  · intro h
    have hl := h.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio 0)
    have hr := h.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0)
    exact hl.trans hr.symm
  · intro h
    exact (convex_hasDerivAt_of_left_eq_right (convex_affineLine hφ v x) 0 h).differentiableAt

theorem measurableSet_differentiable_affineLine {φ : E n → ℝ} (hφ : ConvexOn ℝ univ φ) (v : E n) :
    MeasurableSet {x | DifferentiableAt ℝ (affineLine φ v x) 0} := by
  simp only [differentiable_affineLine_iff hφ]
  exact measurableSet_eq_fun (measurable_leftDirectional hφ v) (measurable_rightDirectional hφ v)

end GaussianTilt.MomentMapCoercivity
