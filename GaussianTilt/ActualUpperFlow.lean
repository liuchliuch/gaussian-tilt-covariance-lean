import GaussianTilt.IntegratedDynamics
import GaussianTilt.PaourisTiltedSpectral
import GaussianTilt.GaussianBrascampLieb

/-!
# Upper-flow assembly for the genuine Gaussian-tilt path

All scalar, spectral, continuity, and initial-moment hypotheses are discharged
for the actual path. The only inputs retained below are the quadratic-variance
inequality and its sharper initial isotropic specialization. These conditional
assembly lemmas are not claims that Letwin's theorem has been proved.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator

namespace GaussianTilt.CompactProbability
variable {n : ℕ} (P : CompactProbability n)

lemma momentMatrix_zero_of_isotropic (hi : Reference.isotropic P.measure) :
    P.momentMatrix 0 = 1 := by
  ext i j
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A i j) hi.2
  simpa only [momentMatrix, secondMomentMatrix, P.tilt_zero, Reference.covariance,
    P.isotropic_integral_coordinate hi, zero_mul, sub_zero] using h

lemma momentHS_nonneg (t : ℝ) : 0 ≤ P.momentHS t := Real.sqrt_nonneg _

/-- Centering decreases the operator norm of the actual second-moment matrix. -/
lemma covariance_opNorm_le_momentMatrix (t : ℝ) :
    ‖Reference.covariance (P.tilt t)‖ ≤ ‖P.momentMatrix t‖ := by
  apply symmetric_opNorm_le_of_quadratic (P.covariance_posSemidef t).1 (norm_nonneg _)
  intro v hv
  have hn : 0 ≤ matrixQuadratic (Reference.covariance (P.tilt t)) (fun i ↦ v i) := by
    simpa only [matrixQuadratic, star_trivial] using
      (P.covariance_posSemidef t).2 (fun i ↦ v i)
  rw [abs_of_nonneg hn]
  have hdecomp := secondMomentMatrix_eq_covariance_add_rankOne
    (fun i ↦ P.memLp_continuous_tilt (f := fun x : Point n ↦ x i) (by fun_prop) t 2)
  rw [← P.reference_covariance_eq_covarianceMatrix t] at hdecomp
  have hq : matrixQuadratic (Reference.covariance (P.tilt t)) (fun i ↦ v i) ≤
      matrixQuadratic (P.momentMatrix t) (fun i ↦ v i) := by
    change _ ≤ matrixQuadratic (secondMomentMatrix _ _) _
    rw [hdecomp]
    simp only [matrixQuadratic, Matrix.add_mulVec, dotProduct_add]
    have hpos := posSemidef_vecMulVec_self_star
      (meanVector (P.tilt t) (fun x : Point n ↦ fun i ↦ x i))
    have hh := hpos.2 (fun i ↦ v i)
    simp only [star_trivial] at hh
    exact le_add_of_nonneg_right hh
  apply hq.trans
  simpa only [hv, one_pow, mul_one] using matrixQuadratic_le_opNorm (P.momentMatrix t) v

/-- The precise variance input that remains in the nonlinear upper flow. -/
def QuadraticVarianceAlongTilt : Prop :=
  ∀ t ≥ 0, ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian →
    ProbabilityTheory.variance (fun x : Point n ↦ matrixQuadratic B (fun i ↦ x i))
      (P.tilt t) ≤ 10 * Matrix.trace ((B * P.momentMatrix t) ^ 2)

/-- Actual scalar flow, retaining only the two precise variance inputs. -/
theorem scalarFlowInputs_of_quadratic_variance
    (hl : Reference.logconcave P.measure) (hi : Reference.isotropic P.measure)
    (hn : 0 < n) (hquad : P.QuadraticVarianceAlongTilt)
    (hinit : P.variance 0 energy ≤ 8 * (n : ℝ)) :
    UpperDynamics.ScalarFlowInputs (n : ℝ) Paouris.spectralTiltConstant 2
      (fun t ↦ ‖P.momentMatrix t‖) P.momentHS P.entropy (fun t ↦ P.variance t energy) := by
  refine ⟨P.momentMatrix_continuous.norm.continuousOn,
    P.momentHS_continuous.continuousOn, fun _ _ ↦ norm_nonneg _,
    fun t _ ↦ P.momentHS_nonneg t, ?_, ?_, ?_, ?_, P.entropy_zero,
    P.continuous_variance_energy.continuousAt.continuousWithinAt, hinit,
    fun t _ ↦ P.hasDerivAt_entropy t, ?_, ?_⟩
  · rw [P.momentMatrix_zero_of_isotropic hi]
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    simp
  · intro b hb
    exact P.momentOperatorNorm_rightSlope_of_quadratic_bound
      (fun t ht ↦ hquad t ht.1)
  · intro b hb
    exact P.momentHS_rightSlope_of_quadratic_bound hi hn
      (fun t ht ↦ hquad t ht.1)
  · exact continuous_iff_continuousAt.mpr
      (fun t ↦ (P.hasDerivAt_entropy t).continuousAt) |>.continuousOn
  · intro t ht
    rw [P.variance_eq_probabilityVariance (P.memLp_continuous_tilt continuous_energy t 2),
      momentHS, Real.sq_sqrt (P.momentHSSquare_nonneg t)]
    exact P.radial_variance_of_quadratic_bound (hquad t ht)
  · intro T q hT hq hreq hqn
    have hmax : 1 ≤ max 1 (max (P.entropy T) (T * Real.sqrt (n : ℝ))) := le_max_left _ _
    have hq2 : 2 ≤ q := by linarith
    have hH : P.entropy T ≤ q := by
      have hHmax : P.entropy T ≤ max 1 (max (P.entropy T) (T * Real.sqrt (n : ℝ))) :=
        (le_max_left _ _).trans (le_max_right _ _)
      linarith
    exact ⟨P.earlier_time_opNorm_le hl hi hT hq2 hH,
      UpperDynamics.spectral_hs_simplification Paouris.spectralTiltConstant_pos.le
        (Nat.cast_nonneg n) hqn (P.earlier_time_momentHS_le hl hi hT hq2 hH)⟩

/-- Actual short-time stability; only the quadratic variance inequality is an input. -/
theorem short_time_stability_of_quadratic_variance
    (hi : Reference.isotropic P.measure) (hn : 0 < n)
    (hquad : P.QuadraticVarianceAlongTilt) {a b α β : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hα : 0 < α) (hβ : 0 < β)
    (hua : ‖P.momentMatrix a‖ ≤ α) (hSa : P.momentHS a ≤ β)
    (hαtime : 20 * α * (b - a) < Real.log 2)
    (hβtime : 20 * β * (b - a) < Real.log 2) :
    ∀ t ∈ Icc a b, ‖P.momentMatrix t‖ ≤ 2 * α ∧ P.momentHS t ≤ 2 * β := by
  exact UpperDynamics.short_time_stability hab hα hβ
    P.momentMatrix_continuous.norm.continuousOn P.momentHS_continuous.continuousOn
    (fun _ _ ↦ norm_nonneg _) (fun t _ ↦ P.momentHS_nonneg t) hua hSa
    (P.momentOperatorNorm_rightSlope_of_quadratic_bound (fun t ht ↦ hquad t (ha.trans ht.1)))
    (P.momentHS_rightSlope_of_quadratic_bound hi hn (fun t ht ↦ hquad t (ha.trans ht.1)))
    hαtime hβtime

end GaussianTilt.CompactProbability
