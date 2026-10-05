import GaussianTilt.UnboundedBrascampLieb
import GaussianTilt.EuclideanBrascampLieb

/-!
# Extended-valued convex potentials and their actual densities

`ConvexExtended` is the Jensen definition of convexity for ℝ ∪ {+∞},
represented in `EReal`; proper potentials exclude the value −∞. The density
is `(EReal.exp (-W x)).toReal`, which is exactly zero at `W x = +∞` and the
ordinary exponential at finite values. Lower semicontinuity supplies
measurability. Finite positive partition mass supplies integrability and
normalization, and strong extended convexity is converted to the density
hypothesis of the proved nonsmooth Brascamp–Lieb theorem.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.ExtendedPotential

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- Standard extended-real Jensen convexity, with `0 * (+∞) = 0`. -/
def ConvexExtended (V : E → EReal) : Prop :=
  ∀ x y : E, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → α + β = 1 →
    V (α • x + β • y) ≤ (α : EReal) * V x + (β : EReal) * V y

/-- A proper extended-real potential is never −∞ and is finite somewhere. -/
def Proper (W : E → EReal) : Prop := (∀ x, W x ≠ ⊥) ∧ ∃ x, W x ≠ ⊤

/-- Actual unnormalized Boltzmann density, including infinite potentials. -/
def density (W : E → EReal) (x : E) : ℝ := (EReal.exp (-W x)).toReal

lemma density_nonneg (W : E → EReal) (x : E) : 0 ≤ density W x := ENNReal.toReal_nonneg

lemma density_of_coe {W : E → EReal} {x : E} {r : ℝ} (hx : W x = (r : EReal)) :
    density W x = Real.exp (-r) := by
  simp only [density, hx, ← EReal.coe_neg, EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_nonneg _)]

lemma density_of_top {W : E → EReal} {x : E} (hx : W x = ⊤) : density W x = 0 := by
  simp [density, hx]

lemma exp_neg_lt_top {W : E → EReal} (hW : ∀ x, W x ≠ ⊥) (x : E) : EReal.exp (-W x) < ⊤ :=
  EReal.exp_lt_top_iff.mpr (lt_top_iff_ne_top.mpr (fun h ↦ hW x (EReal.neg_eq_top_iff.mp h)))

/-- Multiplicative logconcavity follows from the ordinary extended-valued
convexity inequality, including every combination involving infinite values. -/
theorem density_logconcave {V : E → EReal} (hV : ∀ x, V x ≠ ⊥) (hc : ConvexExtended V) :
    LogConcaveMarginal.IsLogConcave (density V) := by
  refine ⟨density_nonneg V, ?_⟩
  intro x y α β hα hβ hαβ
  by_cases hα0 : α = 0
  · have hβ1 : β = 1 := by linarith
    simp [hα0, hβ1]
  by_cases hβ0 : β = 0
  · have hα1 : α = 1 := by linarith
    simp [hβ0, hα1]
  by_cases hx : V x = ⊤
  · rw [density_of_top hx, Real.zero_rpow hα0, zero_mul]
    exact density_nonneg _ _
  by_cases hy : V y = ⊤
  · rw [density_of_top hy, Real.zero_rpow hβ0, mul_zero]
    exact density_nonneg _ _
  have hxe : V x = ((V x).toReal : EReal) := (EReal.coe_toReal hx (hV x)).symm
  have hye : V y = ((V y).toReal : EReal) := (EReal.coe_toReal hy (hV y)).symm
  have hj := hc x y α β hα hβ hαβ
  rw [hxe, hye, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hj
  have hz : V (α • x + β • y) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hj
  have hze : V (α • x + β • y) = ((V (α • x + β • y)).toReal : EReal) :=
    (EReal.coe_toReal hz (hV _)).symm
  rw [hze] at hj
  have hj' := EReal.coe_le_coe_iff.mp hj
  rw [density_of_coe hxe, density_of_coe hye, density_of_coe hze,
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

lemma sub_coe_ne_bot {w : EReal} (hw : w ≠ ⊥) (c : ℝ) : w - (c : EReal) ≠ ⊥ := by
  induction w using EReal.rec with
  | bot => exact False.elim (hw rfl)
  | coe r => simpa only [← EReal.coe_sub] using EReal.coe_ne_bot (r - c)
  | top => simp

lemma exp_neg_sub_coe_toReal (w : EReal) (c : ℝ) :
    (EReal.exp (-(w - (c : EReal)))).toReal = (EReal.exp (-w)).toReal * Real.exp c := by
  induction w using EReal.rec with
  | bot => simp
  | top => simp
  | coe r =>
    simp only [← EReal.coe_sub, ← EReal.coe_neg, EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    rw [show -(r - c) = -r + c by ring, Real.exp_add]

/-- The density strong-logconcavity convention used by the analytic theorem
is exactly the standard extended-potential assumption `W - κ q/2` convex. -/
theorem density_stronglyLogConcave {W : E → EReal} {q : E → ℝ} {κ : ℝ}
    (hW : ∀ x, W x ≠ ⊥)
    (hc : ConvexExtended (fun x ↦ W x - (κ / 2 * q x : ℝ))) :
    LogConcaveMarginal.IsStronglyLogConcave q κ (density W) := by
  have h := density_logconcave (fun x ↦ sub_coe_ne_bot (hW x) _) hc
  have he : density (fun x ↦ W x - (κ / 2 * q x : ℝ)) =
      (fun x ↦ density W x * Real.exp (κ / 2 * q x)) := by
    funext x
    exact exp_neg_sub_coe_toReal _ _
  rwa [he] at h

section Measurability
variable [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]

lemma density_measurable {W : E → EReal} (hW : LowerSemicontinuous W) : Measurable (density W) :=
  ENNReal.measurable_toReal.comp (EReal.measurable_exp.comp hW.measurable.neg)

lemma density_integrable {W : E → EReal} {μ : Measure E}
    (hW : LowerSemicontinuous W) (hp : ∀ x, W x ≠ ⊥)
    (hZ : (∫⁻ x, EReal.exp (-W x) ∂μ) < ⊤) : Integrable (density W) μ :=
  (integrable_toReal_iff (EReal.measurable_exp.comp hW.measurable.neg).aemeasurable
    (Filter.Eventually.of_forall (fun x ↦ (exp_neg_lt_top hp x).ne))).mpr hZ.ne

lemma density_integral_pos {W : E → EReal} {μ : Measure E}
    (hW : LowerSemicontinuous W) (hp : ∀ x, W x ≠ ⊥)
    (hZpos : 0 < ∫⁻ x, EReal.exp (-W x) ∂μ)
    (hZfin : (∫⁻ x, EReal.exp (-W x) ∂μ) < ⊤) : 0 < ∫ x, density W x ∂μ := by
  change 0 < ∫ x, (EReal.exp (-W x)).toReal ∂μ
  rw [integral_toReal (μ := μ) (f := fun x ↦ EReal.exp (-W x)) (EReal.measurable_exp.comp hW.measurable.neg).aemeasurable
    (Filter.Eventually.of_forall (exp_neg_lt_top hp))]
  exact ENNReal.toReal_pos hZpos.ne' hZfin.ne

/-- Complete input bridge from the proper, lower-semicontinuous,
extended-valued formulation in the paper to the proved density theorem. -/
theorem density_inputs {W : E → EReal} {q : E → ℝ} {κ : ℝ} {μ : Measure E}
    (hp : Proper W) (hW : LowerSemicontinuous W)
    (hc : ConvexExtended (fun x ↦ W x - (κ / 2 * q x : ℝ)))
    (hZpos : 0 < ∫⁻ x, EReal.exp (-W x) ∂μ)
    (hZfin : (∫⁻ x, EReal.exp (-W x) ∂μ) < ⊤) :
    LogConcaveMarginal.IsStronglyLogConcave q κ (density W) ∧ Measurable (density W) ∧
      Integrable (density W) μ ∧ 0 < ∫ x, density W x ∂μ :=
  ⟨density_stronglyLogConcave hp.1 hc, density_measurable hW,
    density_integrable hW hp.1 hZfin, density_integral_pos hW hp.1 hZpos hZfin⟩


/-- The probability law specified by the paper, using its actual normalized
Lebesgue density. -/
def normalizedLaw (W : E → EReal) (μ : Measure E) : Measure E :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (density W x / ∫ y, density W y ∂μ))

lemma normalizedLaw_probability {W : E → EReal} {μ : Measure E}
    (hm : Measurable (density W)) (hi : Integrable (density W) μ)
    (hZ : 0 < ∫ x, density W x ∂μ) : IsProbabilityMeasure (normalizedLaw W μ) := by
  apply isProbabilityMeasure_iff.mpr
  rw [normalizedLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (Filter.Eventually.of_forall (fun x ↦ div_nonneg (density_nonneg W x) hZ.le)),
    integral_div, div_self hZ.ne', ENNReal.ofReal_one]

lemma integral_normalizedLaw {W : E → EReal} {μ : Measure E}
    (hm : Measurable (density W)) (hZ : 0 < ∫ x, density W x ∂μ) (g : E → ℝ) :
    (∫ x, g x ∂normalizedLaw W μ) = (∫ x, g x * density W x ∂μ) / (∫ x, density W x ∂μ) := by
  rw [normalizedLaw, integral_withDensity_eq_integral_toReal_smul
    ((hm.div_const _).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (density_nonneg W _) hZ.le), smul_eq_mul]
  have he : (fun x ↦ (density W x / (∫ y, density W y ∂μ)) * g x) =
      (fun x ↦ (g x * density W x) / (∫ y, density W y ∂μ)) := by funext x; ring
  rw [he, integral_div]


lemma integrable_normalizedLaw {W : E → EReal} {μ : Measure E}
    (hm : Measurable (density W)) (hZ : 0 < ∫ x, density W x ∂μ) {g : E → ℝ}
    (hi : Integrable (fun x ↦ g x * density W x) μ) : Integrable g (normalizedLaw W μ) := by
  apply (integrable_withDensity_iff_integrable_smul'
    ((hm.div_const _).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))).mpr
  convert hi.div_const (∫ x, density W x ∂μ) using 1
  funext x
  simp only [ENNReal.toReal_ofReal (div_nonneg (density_nonneg W x) hZ.le), smul_eq_mul]
  ring

end Measurability

/-- The full nonsmooth extended-potential Brascamp–Lieb covariance bound,
in the equivalent directional formulation stated in the paper. This allows
arbitrary unbounded convex supports and proves the actual normalized law is
a probability measure. -/
theorem brascamp_lieb_extended {n : ℕ} {W : Reference.Space n → EReal} {κ : ℝ}
    (hp : Proper W) (hW : LowerSemicontinuous W) (hκ : 0 < κ)
    (hc : ConvexExtended (fun x ↦ W x - (κ / 2 * ‖x‖ ^ 2 : ℝ)))
    (hZpos : 0 < ∫⁻ x, EReal.exp (-W x))
    (hZfin : (∫⁻ x, EReal.exp (-W x)) < ⊤) :
    IsProbabilityMeasure (normalizedLaw W volume) ∧
      ∀ u : Reference.Space n,
        (∫ x, (inner ℝ u x) ^ 2 ∂normalizedLaw W volume) -
          (∫ x, inner ℝ u x ∂normalizedLaw W volume) ^ 2 ≤ κ⁻¹ * ‖u‖ ^ 2 := by
  obtain ⟨hf, hm, hi, hZ⟩ := density_inputs hp hW hc hZpos hZfin
  refine ⟨normalizedLaw_probability hm hi hZ, ?_⟩
  intro u
  rw [integral_normalizedLaw hm hZ, integral_normalizedLaw hm hZ]
  exact EuclideanBrascampLieb.directional_variance_le_inv_of_integrable hκ hf hm hi hZ u


/-- Original Theorem 2.5 with literal probability variance and finite second
moments. Proper lower-semicontinuous extended-valued strongly convex
potentials are allowed on arbitrary, possibly unbounded convex supports. -/
theorem brascamp_lieb_extended_variance {n : ℕ} {W : Reference.Space n → EReal} {κ : ℝ}
    (hp : Proper W) (hW : LowerSemicontinuous W) (hκ : 0 < κ)
    (hc : ConvexExtended (fun x ↦ W x - (κ / 2 * ‖x‖ ^ 2 : ℝ)))
    (hZpos : 0 < ∫⁻ x, EReal.exp (-W x))
    (hZfin : (∫⁻ x, EReal.exp (-W x)) < ⊤) :
    IsProbabilityMeasure (normalizedLaw W volume) ∧
      ∀ u : Reference.Space n,
        MemLp (fun x ↦ inner ℝ u x) 2 (normalizedLaw W volume) ∧
          ProbabilityTheory.variance (fun x ↦ inner ℝ u x) (normalizedLaw W volume) ≤ κ⁻¹ * ‖u‖ ^ 2 := by
  obtain ⟨hf, hm, hi, hZ⟩ := density_inputs hp hW hc hZpos hZfin
  have hlaw := normalizedLaw_probability hm hi hZ
  refine ⟨hlaw, ?_⟩
  intro u
  letI : IsProbabilityMeasure (normalizedLaw W volume) := hlaw
  obtain ⟨hi₁, hi₂⟩ := EuclideanBrascampLieb.directional_moments_integrable hκ hf hm hi hZ u
  have h₁ := integrable_normalizedLaw hm hZ hi₁
  have h₂ := integrable_normalizedLaw hm hZ hi₂
  have hLp : MemLp (fun x ↦ inner ℝ u x) 2 (normalizedLaw W volume) :=
    (memLp_two_iff_integrable_sq h₁.aestronglyMeasurable).mpr h₂
  refine ⟨hLp, ?_⟩
  rw [ProbabilityTheory.variance_eq_sub hLp]
  exact (brascamp_lieb_extended hp hW hκ hc hZpos hZfin).2 u

end GaussianTilt.ExtendedPotential
