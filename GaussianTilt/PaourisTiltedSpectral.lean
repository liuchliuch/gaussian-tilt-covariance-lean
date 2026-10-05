import GaussianTilt.PaourisTiltedProjection

/-!
# Corollary 3.6: the actual earlier-time spectral profile

The proved projection estimates are applied to the actual leading-eigenspace
projections of the tilted second-moment matrix. This yields the sorted
individual eigenvalue, operator-norm, and Hilbert–Schmidt estimates.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator

namespace GaussianTilt.Paouris

def spectralTiltConstant : ℝ := 2 * projectedTiltConstant

lemma spectralTiltConstant_pos : 0 < spectralTiltConstant :=
  mul_pos (by norm_num) projectedTiltConstant_pos

end GaussianTilt.Paouris

namespace GaussianTilt.CompactProbability
open Paouris
variable {n : ℕ} (Q : CompactProbability n)

lemma momentMatrix_posSemidef (t : ℝ) : (Q.momentMatrix t).PosSemidef :=
  secondMomentMatrix_posSemidef (fun i ↦ Q.memLp_continuous_tilt
    (f := fun x : Point n ↦ x i) (by fun_prop) t 2)

/-- The actual nonincreasing sequence of eigenvalues, indexed from zero. -/
def orderedMomentEigenvalue (t : ℝ) (j : Fin n) : ℝ :=
  (Q.momentMatrix_posSemidef t).isHermitian.eigenvalues₀
    (Fin.cast (Fintype.card_fin n).symm j)

/-- The individual eigenvalue assertion of Corollary 3.6. -/
theorem earlier_time_eigenvalue_le
    (hl : Reference.logconcave Q.measure) (hi : Reference.isotropic Q.measure)
    {T q : ℝ} (hT : 0 < T) (hq : 2 ≤ q) (hHq : Q.entropy T ≤ q) (j : Fin n) :
    Q.orderedMomentEigenvalue (T * (1 - 1 / q)) j ≤
      projectedTiltConstant * (1 + q ^ 2 / ((j.val : ℝ) + 1)) := by
  exact GaussianTilt.matrix_spectral_profile_of_projected_trace
    (Q.momentMatrix_posSemidef (T * (1 - 1 / q))).isHermitian
    (fun P hPH hPP ↦ (Q.projected_secondMoment_estimate hl hi hT hq hHq P hPH hPP).2)
    (Fin.cast (Fintype.card_fin n).symm j)

/-- The operator norm at the earlier time is controlled by `q²`. -/
theorem earlier_time_opNorm_le
    (hl : Reference.logconcave Q.measure) (hi : Reference.isotropic Q.measure)
    {T q : ℝ} (hT : 0 < T) (hq : 2 ≤ q) (hHq : Q.entropy T ≤ q) :
    ‖Q.momentMatrix (T * (1 - 1 / q))‖ ≤ spectralTiltConstant * q ^ 2 := by
  have h := GaussianTilt.matrix_opNorm_le_of_projected_trace
    (Q.momentMatrix_posSemidef (T * (1 - 1 / q))) projectedTiltConstant_pos.le
    (fun P hPH hPP ↦ (Q.projected_secondMoment_estimate hl hi hT hq hHq P hPH hPP).2)
  apply h.trans
  unfold spectralTiltConstant
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  nlinarith [projectedTiltConstant_pos]

/-- The Hilbert–Schmidt norm at the earlier time has the paper's dimension
and fourth-power profile, including dimension zero. -/
theorem earlier_time_momentHS_le
    (hl : Reference.logconcave Q.measure) (hi : Reference.isotropic Q.measure)
    {T q : ℝ} (hT : 0 < T) (hq : 2 ≤ q) (hHq : Q.entropy T ≤ q) :
    Q.momentHS (T * (1 - 1 / q)) ≤ spectralTiltConstant * Real.sqrt ((n : ℝ) + q ^ 4) := by
  have h := GaussianTilt.matrix_hilbertSchmidt_le_of_projected_trace
    (Q.momentMatrix_posSemidef (T * (1 - 1 / q))) projectedTiltConstant_pos.le
    (fun P hPH hPP ↦ (Q.projected_secondMoment_estimate hl hi hT hq hHq P hPH hPP).2)
  simpa only [momentHS, Q.momentHSSquare_eq_trace_square, Fintype.card_fin,
    spectralTiltConstant] using h

/-- The complete spectral conclusion of Corollary 3.6 for the genuine tilted
second-moment trajectory. -/
theorem earlier_time_spectral_profile
    (hl : Reference.logconcave Q.measure) (hi : Reference.isotropic Q.measure)
    {T q : ℝ} (hT : 0 < T) (hq : 2 ≤ q) (hHq : Q.entropy T ≤ q) :
    (∀ j : Fin n, Q.orderedMomentEigenvalue (T * (1 - 1 / q)) j ≤
      projectedTiltConstant * (1 + q ^ 2 / ((j.val : ℝ) + 1))) ∧
    ‖Q.momentMatrix (T * (1 - 1 / q))‖ ≤ spectralTiltConstant * q ^ 2 ∧
    Q.momentHS (T * (1 - 1 / q)) ≤ spectralTiltConstant * Real.sqrt ((n : ℝ) + q ^ 4) :=
  ⟨Q.earlier_time_eigenvalue_le hl hi hT hq hHq,
    Q.earlier_time_opNorm_le hl hi hT hq hHq,
    Q.earlier_time_momentHS_le hl hi hT hq hHq⟩

end GaussianTilt.CompactProbability

namespace GaussianTilt.Reference
open Paouris
variable {n : ℕ}

/-- Original Corollary 3.6, fully discharged for the independent measure
specification. `eigenvalues₀` is the actual nonincreasing spectral sequence. -/
theorem earlier_time_spectral_profile
    (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hc : compactlySupported μ) (hl : logconcave μ) (hi : isotropic μ)
    {T q : ℝ} (hT : 0 < T) (hq : 2 ≤ q) (hHq : entropy (gaussianTilt μ T) μ ≤ q) :
    let A := secondMomentMatrix (gaussianTilt μ (T * (1 - 1 / q)))
      (fun x : Space n ↦ fun i ↦ x i)
    ∃ hA : A.IsHermitian,
      (∀ j : Fin n, hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm j) ≤
        projectedTiltConstant * (1 + q ^ 2 / ((j.val : ℝ) + 1))) ∧
      ‖A‖ ≤ spectralTiltConstant * q ^ 2 ∧
      Real.sqrt (Matrix.trace (A ^ 2)) ≤ spectralTiltConstant * Real.sqrt ((n : ℝ) + q ^ 4) := by
  obtain ⟨Q, rfl⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported μ hc
  refine ⟨(Q.momentMatrix_posSemidef _).isHermitian, ?_, ?_, ?_⟩
  · exact Q.earlier_time_eigenvalue_le hl hi hT hq hHq
  · exact Q.earlier_time_opNorm_le hl hi hT hq hHq
  · simpa only [CompactProbability.momentHS, Q.momentHSSquare_eq_trace_square] using
      Q.earlier_time_momentHS_le hl hi hT hq hHq

end GaussianTilt.Reference
