import GaussianTilt.LetwinMatrixCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact elliptic linearization after second-order moment-map regularity

The coefficient in the finite-difference equation is the integral of the
inverse of the segment of actual Hessians.  Jacobi's formula and the
fundamental theorem of calculus prove this identity using only C² source
regularity. No C³ regularity or elliptic regularity theorem is assumed.

This module supplies the linearization, not an interior Schauder theorem.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.Letwin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The affine segment between two matrices. -/
def matrixSegment (A B : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  (1 - t) • A + t • B

@[simp] lemma matrixSegment_zero (A B : Matrix ι ι ℝ) : matrixSegment A B 0 = A := by
  simp [matrixSegment]

@[simp] lemma matrixSegment_one (A B : Matrix ι ι ℝ) : matrixSegment A B 1 = B := by
  simp [matrixSegment]

lemma matrixSegment_posDef {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (matrixSegment A B t).PosDef := by
  rcases eq_or_lt_of_le ht.2 with ht1 | ht1
  · simpa [ht1] using hB
  · exact (hA.smul (sub_pos.mpr ht1)).add_posSemidef (hB.posSemidef.smul ht.1)

lemma continuous_matrixSegment (A B : Matrix ι ι ℝ) : Continuous (matrixSegment A B) :=
  (continuous_const.sub continuous_id).smul continuous_const |>.add
    (continuous_id.smul continuous_const)

lemma hasDerivAt_matrixSegment (A B : Matrix ι ι ℝ) (t : ℝ) :
    HasDerivAt (matrixSegment A B) (B - A) t := by
  convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const A).add
    ((hasDerivAt_id t).smul_const B) using 1
  simp [sub_eq_add_neg, add_comm]

/-- Jacobi's formula along a differentiable matrix curve. -/
lemma hasDerivAt_logdet {H : ℝ → Matrix ι ι ℝ} {D : Matrix ι ι ℝ} {t : ℝ}
    (hH : HasDerivAt H D t) (hdet : (H t).det ≠ 0) :
    HasDerivAt (fun s => Real.log (H s).det) (Matrix.trace ((H t)⁻¹ * D)) t := by
  have hd := ((determinantMultilinear.hasFDerivAt (H t)).comp_hasDerivAt t hH)
  have he : (determinantMultilinear.linearDeriv (H t)) D =
      Matrix.trace ((H t).adjugate * D) := by
    rw [← (determinantMultilinear.hasFDerivAt (H t)).fderiv]
    exact fderiv_determinant_apply (H t) D
  have hl := hd.log hdet
  rw [he] at hl
  convert hl using 1
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.trace_smul]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm, Function.comp_apply, determinantMultilinear_apply]

lemma continuousOn_inv_matrixSegment {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    ContinuousOn (fun t => (matrixSegment A B t)⁻¹) (Icc 0 1) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  apply (continuousAt_matrix_inv (matrixSegment A B t) ?_).comp
    (continuous_matrixSegment A B).continuousAt
  simpa only [Ring.inverse_eq_inv'] using
    (continuousAt_inv₀ (matrixSegment_posDef hA hB ht).det_pos.ne')

/-- The actual averaged inverse coefficient, entry by entry. -/
def averagedInverse (A B : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => ∫ t in (0 : ℝ)..1, (matrixSegment A B t)⁻¹ i j

lemma intervalIntegrable_inv_matrixSegment {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (i j : ι) :
    IntervalIntegrable (fun t => (matrixSegment A B t)⁻¹ i j) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
    ((continuous_apply j).comp (continuous_apply i)).comp_continuousOn
      (continuousOn_inv_matrixSegment hA hB)

set_option maxHeartbeats 1000000 in
/-- Exact finite-increment Jacobi identity with the integrated inverse.
The two Hessian values need only be positive definite. -/
theorem logdet_sub_eq_trace_averagedInverse {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    Real.log B.det - Real.log A.det = Matrix.trace (averagedInverse A B * (B - A)) := by
  have hint : IntervalIntegrable
      (fun t => Matrix.trace ((matrixSegment A B t)⁻¹ * (B - A))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact ((continuous_id.matrix_mul continuous_const).matrix_trace).comp_continuousOn
      (continuousOn_inv_matrixSegment hA hB)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => Real.log (matrixSegment A B t).det)
    (f' := fun t => Matrix.trace ((matrixSegment A B t)⁻¹ * (B - A)))
    (a := 0) (b := 1) (fun t ht => hasDerivAt_logdet (hasDerivAt_matrixSegment A B t)
      (matrixSegment_posDef hA hB (by simpa using ht)).det_pos.ne') hint
  simp only [matrixSegment_zero, matrixSegment_one] at hFTC
  rw [← hFTC]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, averagedInverse]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j _
      exact intervalIntegral.integral_mul_const _ _
    · intro j _
      exact (intervalIntegrable_inv_matrixSegment hA hB i j).mul_const _
  · intro i _
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ
      (f := fun j t => (matrixSegment A B t)⁻¹ i j * (B - A) j i)
      (fun j _ => (intervalIntegrable_inv_matrixSegment hA hB i j).mul_const ((B - A) j i))

end GaussianTilt.MomentMapSchauder
