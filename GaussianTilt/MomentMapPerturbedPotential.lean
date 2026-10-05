import GaussianTilt.MomentMapVariationalWitness
import GaussianTilt.MomentMapEnvelopeLipschitz

/-! # Actual perturbed moment-source potentials

Bounded target perturbations produce finite globally Lipschitz convex source
envelopes with integrable exponential densities. Young's inequality holds
against the actual target-integrable extended dual, including infinite
boundary values.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ} {K : Set (E n)} {q : E n → ℝ} {R : ℝ}

def perturbedSource (K : Set (E n)) (ψ b : E n → ℝ) (t : ℝ) (x : E n) : ℝ :=
  (extendedCompactEnvelope (fun y : K => momentPayoff ψ x y.val) (fun y : K => b y.val) t).toReal

variable (W : VariationalWitness K q R) (hKc : IsCompact K) (hKn : K.Nonempty)
  (hK : ∀ y ∈ K, ‖y‖ ≤ R) {b : E n → ℝ} {M : ℝ≥0} (hM : ∀ y ∈ K, |b y| ≤ M)

include hKc hKn hK hM

theorem perturbedSource_finite (t : ℝ) (x : E n) :
    extendedCompactEnvelope (fun y : K => momentPayoff W.potential x y.val) (fun y : K => b y.val) t ≠ ⊤ ∧
    extendedCompactEnvelope (fun y : K => momentPayoff W.potential x y.val) (fun y : K => b y.val) t ≠ ⊥ := by
  obtain ⟨y, hy, heq⟩ := exists_attaining_momentPayoff hKc hKn hK W.zero_at_origin W.nonneg W.recovered_lower x
  exact extendedCompactEnvelope_finite (fun y : K => hM y y.property)
    (fun y : K => momentPayoff_le W.nonneg x y) (y₀ := ⟨y, hy⟩) heq t

theorem coe_perturbedSource (t : ℝ) (x : E n) :
    (perturbedSource K W.potential b t x : EReal) =
      extendedCompactEnvelope (fun y : K => momentPayoff W.potential x y.val) (fun y : K => b y.val) t :=
  EReal.coe_toReal (perturbedSource_finite W hKc hKn hK hM t x).1
    (perturbedSource_finite W hKc hKn hK hM t x).2

theorem perturbedSource_zero (x : E n) : perturbedSource K W.potential b 0 x = W.potential x := by
  obtain ⟨y, hy, heq⟩ := exists_attaining_momentPayoff hKc hKn hK W.zero_at_origin W.nonneg W.recovered_lower x
  have hen : extendedCompactEnvelope (fun y : K => momentPayoff W.potential x y.val) (fun y : K => b y.val) 0 =
      (W.potential x : EReal) := by
    apply le_antisymm
    · apply sSup_le
      rintro a ⟨z, rfl⟩
      simpa only [zero_mul, EReal.coe_zero, sub_zero] using momentPayoff_le W.nonneg x z
    · have h := le_sSup (mem_range_self (⟨y, hy⟩ : K))
        (s := Set.range (fun z : K => momentPayoff W.potential x z.val - ((0 : ℝ) * b z.val : ℝ)))
      simpa only [extendedCompactEnvelope, zero_mul, EReal.coe_zero, sub_zero, heq] using h
  rw [perturbedSource, hen, EReal.toReal_coe]

theorem perturbedSource_parameter_lipschitz (x : E n) :
    LipschitzWith M (fun t => perturbedSource K W.potential b t x) := by
  obtain ⟨y, hy, heq⟩ := exists_attaining_momentPayoff hKc hKn hK W.zero_at_origin W.nonneg W.recovered_lower x
  exact extendedCompactEnvelope_lipschitz (fun y : K => hM y y.property)
    (fun y : K => momentPayoff_le W.nonneg x y) (y₀ := ⟨y, hy⟩) heq

theorem perturbedSource_parameter_bound (t : ℝ) (x : E n) :
    |perturbedSource K W.potential b t x - W.potential x| ≤ (M : ℝ) * |t| := by
  have h := (perturbedSource_parameter_lipschitz W hKc hKn hK hM x).dist_le_mul t 0
  simpa only [Real.dist_eq, sub_zero, perturbedSource_zero W hKc hKn hK hM] using h

theorem finite_payoff_le_perturbedSource (t : ℝ) (x : E n) {y : E n} (hy : y ∈ K)
    (hfin : extendedDual W.potential y ≠ ⊤) :
    ⟪x, y⟫_ℝ - (extendedDual W.potential y).toReal - t * b y ≤ perturbedSource K W.potential b t x := by
  have h := le_sSup (mem_range_self (⟨y, hy⟩ : K))
    (s := Set.range (fun z : K => momentPayoff W.potential x z.val - (t * b z.val : ℝ)))
  change momentPayoff W.potential x y - (t * b y : ℝ) ≤
    extendedCompactEnvelope (fun y : K => momentPayoff W.potential x y.val) (fun y : K => b y.val) t at h
  rw [← coe_perturbedSource W hKc hKn hK hM t x, momentPayoff,
    ← EReal.coe_ennreal_toReal hfin, ← EReal.coe_sub, ← EReal.coe_sub] at h
  exact EReal.coe_le_coe_iff.mp h

theorem perturbedSource_le_of_finite_payoff_le (t : ℝ) (x : E n) {C : ℝ}
    (hC : ∀ y ∈ K, extendedDual W.potential y ≠ ⊤ →
      ⟪x, y⟫_ℝ - (extendedDual W.potential y).toReal - t * b y ≤ C) :
    perturbedSource K W.potential b t x ≤ C := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_perturbedSource W hKc hKn hK hM]
  apply sSup_le
  rintro a ⟨y, rfl⟩
  change momentPayoff W.potential x y.val - (t * b y.val : ℝ) ≤ (C : EReal)
  by_cases hy : extendedDual W.potential y.val = ⊤
  · simp [momentPayoff, hy]
  · rw [momentPayoff, ← EReal.coe_ennreal_toReal hy, ← EReal.coe_sub, ← EReal.coe_sub]
    exact EReal.coe_le_coe_iff.mpr (hC y y.property hy)

theorem perturbedSource_one_sided_lipschitz (t : ℝ) (x z : E n) :
    perturbedSource K W.potential b t x ≤ perturbedSource K W.potential b t z + R * ‖x - z‖ := by
  apply perturbedSource_le_of_finite_payoff_le W hKc hKn hK hM
  intro y hy hfin
  have hz := finite_payoff_le_perturbedSource W hKc hKn hK hM t z hy hfin
  have hi := real_inner_le_norm (x - z) y
  have hn := mul_le_mul_of_nonneg_left (hK y hy) (norm_nonneg (x - z))
  rw [inner_sub_left] at hi
  nlinarith

theorem perturbedSource_lipschitz (t : ℝ) : LipschitzWith R.toNNReal (perturbedSource K W.potential b t) := by
  apply LipschitzWith.of_dist_le'
  intro x z
  rw [Real.dist_eq, dist_eq_norm, abs_le]
  have h₁ := perturbedSource_one_sided_lipschitz W hKc hKn hK hM t x z
  have h₂ := perturbedSource_one_sided_lipschitz W hKc hKn hK hM t z x
  rw [norm_sub_rev z x] at h₂
  constructor <;> linarith

theorem perturbedSource_convex (t : ℝ) : ConvexOn ℝ univ (perturbedSource K W.potential b t) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a d ha hd had
  apply perturbedSource_le_of_finite_payoff_le W hKc hKn hK hM
  intro y hy hfin
  have hx := mul_le_mul_of_nonneg_left (finite_payoff_le_perturbedSource W hKc hKn hK hM t x hy hfin) ha
  have hz := mul_le_mul_of_nonneg_left (finite_payoff_le_perturbedSource W hKc hKn hK hM t z hy hfin) hd
  have heq : a * ((extendedDual W.potential y).toReal + t * b y) +
      d * ((extendedDual W.potential y).toReal + t * b y) = (extendedDual W.potential y).toReal + t * b y := by
    rw [← add_mul, had, one_mul]
  simp only [inner_add_left, inner_smul_left, conj_trivial, smul_eq_mul]
  nlinarith

theorem perturbedSource_exp_integrable (t : ℝ) :
    Integrable (fun x => Real.exp (-perturbedSource K W.potential b t x)) := by
  have hc := (perturbedSource_lipschitz W hKc hKn hK hM t).continuous
  apply (W.source_integrable.const_mul (Real.exp ((M : ℝ) * |t|))).mono'
    (Real.continuous_exp.comp hc.neg).aestronglyMeasurable
  apply ae_of_all
  intro x
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := (abs_le.mp (perturbedSource_parameter_bound W hKc hKn hK hM t x)).1
  linarith

end GaussianTilt.MomentMapCoercivity
