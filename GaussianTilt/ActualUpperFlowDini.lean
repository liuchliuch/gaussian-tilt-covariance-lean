import GaussianTilt.ActualUpperFlow

/-!
# The upper right Dini estimate for the actual log operator norm

The eventual strict-slope formulation below is the full upper-Dini bound.
It is stronger than the frequently-slope interface needed by Grönwall and
does not assume differentiability of the operator norm or a simple top eigenvalue.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped Topology Matrix.Norms.L2Operator

namespace GaussianTilt.UpperDynamics

/-- The upper right Dini derivative, using the actual extended-real limsup. -/
def UpperRightDiniLE (f : ℝ → ℝ) (t D : ℝ) : Prop :=
  Filter.limsup (fun z ↦ (((z - t)⁻¹ * (f z - f t) : ℝ) : EReal)) (𝓝[>] t) ≤ (D : EReal)

/-- Exact equivalence with the eventual strict-slope criterion. -/
lemma upperRightDiniLE_iff {f : ℝ → ℝ} {t D : ℝ} :
    UpperRightDiniLE f t D ↔
      ∀ r > D, ∀ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (f z - f t) < r := by
  constructor
  · intro h r hr
    have he := ((Filter.limsup_le_iff).mp h) (r : EReal) (EReal.coe_lt_coe_iff.mpr hr)
    simpa only [EReal.coe_lt_coe_iff] using he
  · intro h
    apply (Filter.limsup_le_iff).mpr
    intro a ha
    obtain ⟨r, hr, hra⟩ := EReal.lt_iff_exists_real_btwn.mp ha
    filter_upwards [h r (EReal.coe_lt_coe_iff.mp hr)] with z hz
    exact (EReal.coe_lt_coe_iff.mpr hz).trans hra

/-- The logarithm of a nonvanishing norm satisfies the upper-Dini chain rule
at any point where the underlying vector-valued map is differentiable. -/
theorem upperRightDiniLE_log_norm_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {t D : ℝ}
    (hf : HasDerivAt f f' t) (hp : ∀ z, 0 < ‖f z‖)
    (hb : ‖f'‖ ≤ D * ‖f t‖) :
    UpperRightDiniLE (fun z ↦ Real.log ‖f z‖) t D := by
  rw [upperRightDiniLE_iff]
  intro r hr
  have hdr : ‖f'‖ < r * ‖f t‖ := hb.trans_lt (mul_lt_mul_of_pos_right hr (hp t))
  have h := (hf.hasDerivWithinAt (s := Ioi t)).limsup_slope_norm_le hdr
  filter_upwards [h, self_mem_nhdsWithin] with z hz hzt
  have hzt' : 0 < z - t := sub_pos.mpr hzt
  rw [Real.norm_eq_abs, abs_of_pos hzt'] at hz
  have hlog : Real.log ‖f z‖ - Real.log ‖f t‖ ≤ (‖f z‖ - ‖f t‖) / ‖f t‖ := by
    have hl := Real.log_le_sub_one_of_pos (div_pos (hp z) (hp t))
    rw [Real.log_div (hp z).ne' (hp t).ne'] at hl
    convert hl using 1
    field_simp [(hp t).ne']
  have hh := mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hzt'.le)
  have hd : (z - t)⁻¹ * ((‖f z‖ - ‖f t‖) / ‖f t‖) < r := by
    rw [← mul_div_assoc, div_lt_iff₀ (hp t)]
    exact hz
  exact hh.trans_lt hd

end GaussianTilt.UpperDynamics

namespace GaussianTilt.CompactProbability
variable {n : ℕ} (P : CompactProbability n)

/-- Equation (24), in the exact eventual formulation of the upper Dini derivative. -/
theorem log_momentOperatorNorm_upperRightDini_of_quadratic_bound
    (hi : Reference.isotropic P.measure) (hn : 0 < n) {t : ℝ}
    (hquad : ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian →
      ProbabilityTheory.variance (fun x : Point n ↦ matrixQuadratic B (fun i ↦ x i))
        (P.tilt t) ≤ 10 * Matrix.trace ((B * P.momentMatrix t) ^ 2)) :
    UpperDynamics.UpperRightDiniLE (fun s ↦ Real.log ‖P.momentMatrix s‖) t
      (10 * P.momentHS t) := by
  apply UpperDynamics.upperRightDiniLE_log_norm_of_hasDerivAt (P.momentMatrix_hasDerivAt t)
    (fun s ↦ P.secondMoment_opNorm_pos hi hn s)
  convert P.momentDerivative_bound_of_quadratic_bound hquad using 1
  ring

/-- All three differential assertions of Lemma 3.2, retaining precisely its
quadratic-variance input. The logarithmic HS estimate is proved in absolute value. -/
theorem differential_estimates_of_quadratic_variance
    (hi : Reference.isotropic P.measure) (hn : 0 < n)
    (hquad : P.QuadraticVarianceAlongTilt) {t : ℝ} (ht : 0 ≤ t) :
    P.variance t energy ≤ 10 * P.momentHS t ^ 2 ∧
    |deriv (fun s ↦ Real.log (P.momentHS s)) t| ≤ 10 * ‖P.momentMatrix t‖ ∧
    UpperDynamics.UpperRightDiniLE (fun s ↦ Real.log ‖P.momentMatrix s‖) t
      (10 * P.momentHS t) := by
  refine ⟨?_, P.log_momentHS_bound_of_quadratic_bound hi hn (hquad t ht),
    P.log_momentOperatorNorm_upperRightDini_of_quadratic_bound hi hn (hquad t ht)⟩
  rw [P.variance_eq_probabilityVariance (P.memLp_continuous_tilt continuous_energy t 2),
    momentHS, Real.sq_sqrt (P.momentHSSquare_nonneg t)]
  exact P.radial_variance_of_quadratic_bound (hquad t ht)

end GaussianTilt.CompactProbability
