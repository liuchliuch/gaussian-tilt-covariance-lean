import GaussianTilt.ActualUpperFlowVariance

/-! # The endpoint propagation constants for the genuine tilted measure -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped Topology Matrix.Norms.L2Operator

namespace GaussianTilt.CompactProbability

/-- Lemma 3.8 with constants independent of both the dimension and the law.
Only the isotropic quadratic-variance theorem remains an input. -/
theorem endpoint_constants_of_isotropic_bound
    (hL : Reference.IsotropicQuadraticVarianceBound) :
    ∃ ε Cstar Csp : ℝ, 0 < ε ∧ 0 < Cstar ∧ 0 < Csp ∧
      ∀ (n : ℕ) (P : CompactProbability n),
        Reference.logconcave P.measure → Reference.isotropic P.measure →
        ∀ T q : ℝ, 0 < T →
          Csp * max 1 (max (P.entropy T) (T * Real.sqrt (n : ℝ))) ≤ q →
          q ^ 4 ≤ (n : ℝ) → T * q ≤ ε →
          ‖P.momentMatrix T‖ ≤ Cstar * q ^ 2 ∧ P.momentHS T ≤ Cstar * Real.sqrt (n : ℝ) := by
  obtain ⟨ε, Csp, κ, hε0, hsp, hspB, hε, hspTime, hκ5, hκ⟩ :=
    UpperDynamics.choose_propagation_constants (B := 2) Paouris.spectralTiltConstant_pos
  have hsp0 : 0 < Csp := by linarith
  refine ⟨ε, 4 * Paouris.spectralTiltConstant, Csp, hε0,
    mul_pos (by norm_num) Paouris.spectralTiltConstant_pos, hsp0, ?_⟩
  intro n P hl hi T q hT hreq hqn hTq
  have hm : 1 ≤ max 1 (max (P.entropy T) (T * Real.sqrt (n : ℝ))) := le_max_left _ _
  have hqsp : Csp ≤ q := by
    have h := mul_le_mul_of_nonneg_left hm hsp0.le
    nlinarith
  have hq2 : 2 ≤ q := hsp.trans hqsp
  have hq1 : 1 < q := by linarith
  have hq0 : 0 < q := by linarith
  have hnR : 0 < (n : ℝ) := (pow_pos hq0 4).trans_le hqn
  have hn : 0 < n := by exact_mod_cast hnR
  have hHq : P.entropy T ≤ q := by
    have hHmax : P.entropy T ≤ max 1 (max (P.entropy T) (T * Real.sqrt (n : ℝ))) :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hmax0 : 0 ≤ max 1 (max (P.entropy T) (T * Real.sqrt (n : ℝ))) := by linarith
    have hle := mul_le_mul_of_nonneg_right hsp hmax0
    nlinarith
  have ha0 : 0 ≤ T * (1 - 1 / q) := by
    have hh : 1 / q ≤ 1 := (div_le_one hq0).2 (by linarith)
    exact mul_nonneg hT.le (sub_nonneg.mpr hh)
  have hqscale : Csp * (T * Real.sqrt (n : ℝ)) ≤ q := by
    have hh : T * Real.sqrt (n : ℝ) ≤ max 1 (max (P.entropy T) (T * Real.sqrt (n : ℝ))) :=
      (le_max_right _ _).trans (le_max_right _ _)
    exact (mul_le_mul_of_nonneg_left hh hsp0.le).trans hreq
  have hquad := P.quadraticVarianceAlongTilt_of_isotropic_bound hL hl hi
  exact UpperDynamics.endpoint_estimate hT hq1 hnR Paouris.spectralTiltConstant_pos
    hsp0 hε hspTime hTq hqscale
    P.momentMatrix_continuous.norm.continuousOn P.momentHS_continuous.continuousOn
    (fun _ _ ↦ norm_nonneg _) (fun s _ ↦ P.momentHS_nonneg s)
    (P.earlier_time_opNorm_le hl hi hT hq2 hHq)
    (UpperDynamics.spectral_hs_simplification Paouris.spectralTiltConstant_pos.le
      (Nat.cast_nonneg n) hqn (P.earlier_time_momentHS_le hl hi hT hq2 hHq))
    (P.momentOperatorNorm_rightSlope_of_quadratic_bound
      (fun s hs ↦ hquad s (ha0.trans hs.1)))
    (P.momentHS_rightSlope_of_quadratic_bound hi hn
      (fun s hs ↦ hquad s (ha0.trans hs.1)))

end GaussianTilt.CompactProbability
