import GaussianTilt.MomentMapDanskinExtended

/-! # Global parameter control for extended Fenchel envelopes

Uniform boundedness of the perturbing observable controls the actual
supremum for all real parameters, even when the payoff is minus infinity.
-/
noncomputable section
open Filter Set
open scoped Topology NNReal

namespace GaussianTilt.MomentMapCoercivity

lemma extended_payoff_parameter_identity (a : EReal) (b s t : ℝ) :
    a - (t * b : ℝ) = (a - (s * b : ℝ)) + ((s - t) * b : ℝ) := by
  simp only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add]
  congr 1
  congr 1
  ring

theorem extendedCompactEnvelope_le_add {α : Type*} {a : α → EReal} {b : α → ℝ}
    {M : ℝ≥0} (hM : ∀ y, |b y| ≤ M) (s t : ℝ) :
    extendedCompactEnvelope a b t ≤ extendedCompactEnvelope a b s + ((M : ℝ) * |t - s| : ℝ) := by
  apply sSup_le
  rintro r ⟨y, rfl⟩
  dsimp only
  rw [extended_payoff_parameter_identity (a y) (b y) s t]
  apply add_le_add (show a y - (s * b y : ℝ) ≤ extendedCompactEnvelope a b s from
    le_sSup (mem_range_self y))
  apply EReal.coe_le_coe_iff.mpr
  have h : (s - t) * b y ≤ |s - t| * (M : ℝ) := calc
    _ ≤ |(s - t) * b y| := le_abs_self _
    _ = |s - t| * |b y| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hM y) (abs_nonneg _)
  simpa only [abs_sub_comm, mul_comm] using h

theorem extendedCompactEnvelope_finite {α : Type*} {a : α → EReal} {b : α → ℝ}
    {M : ℝ≥0} (hM : ∀ y, |b y| ≤ M) {U A : ℝ}
    (hU : ∀ y, a y ≤ (U : EReal)) {y₀ : α} (hA : a y₀ = (A : EReal)) (t : ℝ) :
    extendedCompactEnvelope a b t ≠ ⊤ ∧ extendedCompactEnvelope a b t ≠ ⊥ := by
  have hzero : extendedCompactEnvelope a b 0 ≤ (U : EReal) := by
    apply sSup_le
    rintro r ⟨y, rfl⟩
    dsimp only
    simpa only [zero_mul, EReal.coe_zero, sub_zero] using hU y
  have htop : extendedCompactEnvelope a b t < ⊤ := by
    have h := (extendedCompactEnvelope_le_add hM 0 t).trans
      (add_le_add_right hzero ((M : ℝ) * |t - 0| : ℝ))
    rw [← EReal.coe_add] at h
    exact h.trans_lt (EReal.coe_lt_top _)
  have hbot : ⊥ < extendedCompactEnvelope a b t := by
    have h : a y₀ - (t * b y₀ : ℝ) ≤ extendedCompactEnvelope a b t := le_sSup (mem_range_self y₀)
    rw [hA, ← EReal.coe_sub] at h
    exact (EReal.bot_lt_coe _).trans_le h
  exact ⟨htop.ne, hbot.ne'⟩

/-- Every bounded perturbation has its true uniform parameter-Lipschitz
constant; no maximizer, continuity or finiteness of boundary values is assumed. -/
theorem extendedCompactEnvelope_lipschitz {α : Type*} {a : α → EReal} {b : α → ℝ}
    {M : ℝ≥0} (hM : ∀ y, |b y| ≤ M) {U A : ℝ}
    (hU : ∀ y, a y ≤ (U : EReal)) {y₀ : α} (hA : a y₀ = (A : EReal)) :
    LipschitzWith M (fun t : ℝ ↦ (extendedCompactEnvelope a b t).toReal) := by
  have hc (t : ℝ) : ((extendedCompactEnvelope a b t).toReal : EReal) =
      extendedCompactEnvelope a b t :=
    EReal.coe_toReal (extendedCompactEnvelope_finite hM hU hA t).1
      (extendedCompactEnvelope_finite hM hU hA t).2
  have hle (s t : ℝ) : (extendedCompactEnvelope a b t).toReal ≤
      (extendedCompactEnvelope a b s).toReal + (M : ℝ) * |t - s| := by
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_add, hc, hc]
    exact extendedCompactEnvelope_le_add hM s t
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [Real.dist_eq]
  apply abs_sub_le_iff.mpr
  have hst := hle s t
  have hts := hle t s
  rw [abs_sub_comm t s] at hst
  constructor <;> linarith

end GaussianTilt.MomentMapCoercivity
