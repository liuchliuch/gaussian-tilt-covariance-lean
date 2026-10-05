import GaussianTilt.PaourisProjection
import GaussianTilt.MomentDynamics

/-!
# Lemma 3.5: projected second moments at the earlier tilt time

The projected Paouris estimate is combined with the actual Gaussian-tilt
Radon–Nikodym Hölder estimate. Every moment premise is discharged for the
original compact isotropic logconcave law.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace GaussianTilt.Paouris
variable {n : ℕ}

lemma orthogonal_matrix_norm_sq (P : Matrix (Fin n) (Fin n) ℝ)
    (hH : P.IsHermitian) (hP : P * P = P) (x : Reference.Space n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, P i j * (x j * x i) := by
  let A : Reference.Space n →L[ℝ] Reference.Space n := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P
  have hAA : A * A = A := by
    dsimp only [A]
    rw [← map_mul, hP]
  have hAAx : A (A x) = A x := congrArg (fun T : Reference.Space n →L[ℝ] Reference.Space n ↦ T x) hAA
  have hsym (u v : Reference.Space n) : ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ :=
    (Matrix.isHermitian_iff_isSymmetric.mp hH) u v
  calc
    ‖A x‖ ^ 2 = ⟪A x, A x⟫_ℝ := (real_inner_self_eq_norm_sq _).symm
    _ = ⟪x, A x⟫_ℝ := by rw [hsym, hAAx]
    _ = _ := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real]
      change (∑ i, (P.mulVec (WithLp.ofLp x)) i * x i) = _
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
      rfl

/-- The actual projected second moment is the projected matrix trace. -/
theorem trace_projection_secondMoment
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hH : P.IsHermitian) (hP : P * P = P) :
    Matrix.trace (P * secondMomentMatrix μ (fun x : Reference.Space n ↦ fun i ↦ x i)) =
      ∫ x, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ 2 ∂μ := by
  simp_rw [orthogonal_matrix_norm_sq P hH hP]
  have hf (i j : Fin n) : Integrable (fun x : Reference.Space n ↦ P i j * (x j * x i)) μ :=
    compact_continuous_integrable μ hc (by fun_prop)
  rw [integral_finset_sum _ (fun i _ ↦ integrable_finset_sum _ (fun j _ ↦ hf i j))]
  simp_rw [integral_finset_sum _ (fun j _ ↦ hf _ j), integral_const_mul]
  rfl

/-- A fixed universal factor for Lemma 3.5. -/
def projectedTiltConstant : ℝ := Real.exp 1 * (8 * generalCompactPaourisMomentConstant ^ 2)

lemma projectedTiltConstant_pos : 0 < projectedTiltConstant := by
  unfold projectedTiltConstant
  exact mul_pos (Real.exp_pos _) (mul_pos (by norm_num) (sq_pos_of_pos generalCompactPaourisMomentConstant_pos))

end GaussianTilt.Paouris

namespace GaussianTilt.CompactProbability
open Paouris
variable {n : ℕ} (Q : CompactProbability n)

/-- The full earlier-time projected expectation bound, with no unproved
moment or density-norm premise. -/
theorem projected_expectation_le
    (hl : Reference.logconcave Q.measure) (hi : Reference.isotropic Q.measure)
    {T q : ℝ} (hT : 0 < T) (hq : 2 ≤ q) (hHq : Q.entropy T ≤ q)
    (P : Matrix (Fin n) (Fin n) ℝ) (hPH : P.IsHermitian) (hPP : P * P = P) :
    Q.expectation (T * (1 - 1 / q))
      (fun x ↦ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ 2) ≤
      projectedTiltConstant * ((P.rank : ℝ) + q ^ 2) := by
  have hq1 : 1 < q := by linarith
  have hq0 : 0 < q := by linarith
  have hf : MemLp (fun x : Point n ↦ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ 2)
      (ENNReal.ofReal q) Q.measure := compact_memLp_continuous Q.measure Q.reference_compactlySupported
        (by fun_prop) _
  have h := GaussianTilt.expectation_le_exp_entropy_mul_moment Q hT hq1
    (Eventually.of_forall fun x ↦ sq_nonneg _) hf
  have ht : T / (q / (q - 1)) = T * (1 - 1 / q) := by field_simp
  rw [ht] at h
  have hmoment := compact_projected_square_moment_le Q.measure Q.reference_compactlySupported
    hl hi P hPH hPP (by linarith : 1 ≤ q)
  have he : Real.exp (Q.entropy T / q) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr ((div_le_one hq0).mpr hHq)
  calc
    _ ≤ Real.exp (Q.entropy T / q) *
        (∫ x, (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ 2) ^ q ∂Q.measure) ^ (1 / q) := h
    _ ≤ Real.exp 1 *
        ((8 * generalCompactPaourisMomentConstant ^ 2) * ((P.rank : ℝ) + q ^ 2)) := by
      apply mul_le_mul he hmoment
      · exact Real.rpow_nonneg (integral_nonneg fun x ↦ by positivity) _
      · exact (Real.exp_pos _).le
    _ = projectedTiltConstant * ((P.rank : ℝ) + q ^ 2) := by
      unfold projectedTiltConstant
      ring

/-- Lemma 3.5 including its exact trace/expectation identity. -/
theorem projected_secondMoment_estimate
    (hl : Reference.logconcave Q.measure) (hi : Reference.isotropic Q.measure)
    {T q : ℝ} (hT : 0 < T) (hq : 2 ≤ q) (hHq : Q.entropy T ≤ q)
    (P : Matrix (Fin n) (Fin n) ℝ) (hPH : P.IsHermitian) (hPP : P * P = P) :
    Matrix.trace (P * Q.momentMatrix (T * (1 - 1 / q))) =
      Q.expectation (T * (1 - 1 / q))
        (fun x ↦ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ 2) ∧
    Matrix.trace (P * Q.momentMatrix (T * (1 - 1 / q))) ≤
      projectedTiltConstant * ((P.rank : ℝ) + q ^ 2) := by
  have hid := trace_projection_secondMoment (Q.tilt (T * (1 - 1 / q)))
    (Q.reference_tilt_compactlySupported _) P hPH hPP
  rw [Q.integral_tilt] at hid
  exact ⟨hid, hid.trans_le (Q.projected_expectation_le hl hi hT hq hHq P hPH hPP)⟩

end GaussianTilt.CompactProbability

namespace GaussianTilt.Reference
open Paouris
variable {n : ℕ}

/-- Original Lemma 3.5 for the independent measure specification. -/
theorem projected_second_moment_estimate
    (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hc : compactlySupported μ) (hl : logconcave μ) (hi : isotropic μ)
    {T q : ℝ} (hT : 0 < T) (hq : 2 ≤ q) (hHq : entropy (gaussianTilt μ T) μ ≤ q)
    (P : Matrix (Fin n) (Fin n) ℝ) (hPH : P.IsHermitian) (hPP : P * P = P) :
    Matrix.trace (P * secondMomentMatrix (gaussianTilt μ (T * (1 - 1 / q)))
      (fun x : Space n ↦ fun i ↦ x i)) =
      (∫ x, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ 2
        ∂gaussianTilt μ (T * (1 - 1 / q))) ∧
    Matrix.trace (P * secondMomentMatrix (gaussianTilt μ (T * (1 - 1 / q)))
      (fun x : Space n ↦ fun i ↦ x i)) ≤ projectedTiltConstant * ((P.rank : ℝ) + q ^ 2) := by
  obtain ⟨Q, rfl⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported μ hc
  simpa only [Q.reference_gaussianTilt, Q.integral_tilt, CompactProbability.momentMatrix] using
    Q.projected_secondMoment_estimate hl hi hT hq hHq P hPH hPP

end GaussianTilt.Reference
