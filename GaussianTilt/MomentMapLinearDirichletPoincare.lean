import GaussianTilt.EllipticRegularitySobolev
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# A derived Poincaré inequality for bounded-domain Dirichlet tests

The proof integrates the actual derivative of `xᵢ u²`. Compact support
eliminates the boundary term, and L² Cauchy--Schwarz bounds the remaining
pairing. No domain Poincaré or Dirichlet-solvability theorem is assumed.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Multiplication of a genuine smooth compact test by one coordinate. -/
def coordinateProductCore (i : Fin n) (u : smoothCompactCore n) : smoothCompactCore n :=
  ⟨fun x => x i * u.1 x,
    (by have hu := u.2.1; fun_prop), u.2.2.mul_left⟩

lemma norm_smoothCompactToL2_sq (u : smoothCompactCore n) :
    ‖smoothCompactToL2 volume u‖ ^ 2 = ∫ x, u.1 x ^ 2 :=
  norm_toLp_sq_eq_integral (smooth_compact_memLp u.2.1 u.2.2)

/-- Exact integrated dilation identity from the actual compact test. -/
theorem smoothCompact_coordinate_dilation_identity (u : smoothCompactCore n) (i : Fin n) :
    ‖smoothCompactToL2 volume u‖ ^ 2 = -2 *
      inner ℝ (smoothCompactToL2 volume (coordinateProductCore i u))
        (smoothCompactToL2 volume (smoothCompactDerivative i u)) := by
  let V : CoordinateSpace n → ℝ := fun x => x i * u.1 x * u.1 x
  have hVc : ContDiff ℝ ∞ V := by have hu := u.2.1; dsimp [V]; fun_prop
  have hVs : HasCompactSupport V := u.2.2.mul_left.mul_right
  have hu : Differentiable ℝ u.1 := u.2.1.differentiable (by simp)
  have hDV (x : CoordinateSpace n) :
      coordinateDerivative i V x = u.1 x ^ 2 + 2 * (x i * u.1 x * coordinateDerivative i u.1 x) := by
    have hh := ((hasFDerivAt_apply i x).mul (hu x).hasFDerivAt).mul (hu x).hasFDerivAt
    unfold coordinateDerivative
    change fderiv ℝ (((fun y : CoordinateSpace n => y i) * u.1) * u.1) x (Pi.single i 1) = _
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.proj_apply, Pi.single_eq_same, Pi.mul_apply]
    ring
  have hz := integral_partial_eq_zero i (hVc.differentiable (by simp))
    (hVc.continuous.integrable_of_hasCompactSupport hVs)
    ((smooth_coordinateDerivative hVc i).continuous.integrable_of_hasCompactSupport
      (hVs.fderiv_apply ℝ (Pi.single i 1)))
  have hU2 : Integrable (fun x => u.1 x ^ 2) :=
    (smooth_compact_memLp u.2.1 u.2.2 : MemLp u.1 2 volume).integrable_sq
  have hCross : Integrable (fun x => x i * u.1 x * coordinateDerivative i u.1 x) :=
    (((by fun_prop : Continuous (fun x : CoordinateSpace n => x i)).mul u.2.1.continuous).mul
      (smooth_coordinateDerivative u.2.1 i).continuous).integrable_of_hasCompactSupport
        u.2.2.mul_left.mul_right
  simp_rw [hDV] at hz
  rw [integral_add hU2 (hCross.const_mul 2), integral_const_mul] at hz
  rw [norm_smoothCompactToL2_sq, inner_smoothCompactToL2]
  change (∫ x, u.1 x ^ 2) = -2 * ∫ x, (x i * u.1 x) * coordinateDerivative i u.1 x
  linarith

/-- A support strip bounds the L² norm of coordinate multiplication. -/
lemma norm_coordinateProductCore_le (u : smoothCompactCore n) (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ tsupport u.1, |x i| ≤ R) :
    ‖smoothCompactToL2 volume (coordinateProductCore i u)‖ ≤
      R * ‖smoothCompactToL2 volume u‖ := by
  have hpoint (x : CoordinateSpace n) : (x i * u.1 x) ^ 2 ≤ R ^ 2 * u.1 x ^ 2 := by
    by_cases hx : x ∈ tsupport u.1
    · have hh : |x i * u.1 x| ≤ R * |u.1 x| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hstrip x hx) (abs_nonneg _)
      have hs := pow_le_pow_left₀ (abs_nonneg (x i * u.1 x)) hh 2
      simpa only [mul_pow, sq_abs] using hs
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have hI1 : Integrable (fun x => (coordinateProductCore i u).1 x ^ 2) :=
    (smooth_compact_memLp (coordinateProductCore i u).2.1 (coordinateProductCore i u).2.2 :
      MemLp (coordinateProductCore i u).1 2 volume).integrable_sq
  have hI2 : Integrable (fun x => u.1 x ^ 2) :=
    (smooth_compact_memLp u.2.1 u.2.2 : MemLp u.1 2 volume).integrable_sq
  have hbound := integral_mono hI1 (hI2.const_mul (R ^ 2)) hpoint
  rw [integral_const_mul, ← norm_smoothCompactToL2_sq, ← norm_smoothCompactToL2_sq] at hbound
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg _))).mp
  simpa only [mul_pow] using hbound

/-- Genuine bounded-domain Poincaré inequality on actual compact smooth
Dirichlet tests. A single bounded coordinate strip suffices. -/
theorem smoothCompact_poincare_strip (u : smoothCompactCore n) (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ tsupport u.1, |x i| ≤ R) :
    ‖smoothCompactToL2 volume u‖ ≤
      2 * R * ‖smoothCompactToL2 volume (smoothCompactDerivative i u)‖ := by
  have hid := smoothCompact_coordinate_dilation_identity u i
  have hp := norm_coordinateProductCore_le u i hR hstrip
  have hinner := abs_real_inner_le_norm
    (smoothCompactToL2 volume (coordinateProductCore i u))
    (smoothCompactToL2 volume (smoothCompactDerivative i u))
  have hbound : ‖smoothCompactToL2 volume u‖ ^ 2 ≤
      2 * R * ‖smoothCompactToL2 volume u‖ *
        ‖smoothCompactToL2 volume (smoothCompactDerivative i u)‖ := by
    have hprod := mul_le_mul_of_nonneg_right hp
      (norm_nonneg (smoothCompactToL2 volume (smoothCompactDerivative i u)))
    have hneg := neg_le_abs (inner ℝ (smoothCompactToL2 volume (coordinateProductCore i u))
      (smoothCompactToL2 volume (smoothCompactDerivative i u)))
    nlinarith
  by_cases hz : ‖smoothCompactToL2 volume u‖ = 0
  · rw [hz]
    positivity
  · have hpos : 0 < ‖smoothCompactToL2 (volume : Measure (CoordinateSpace n)) u‖ := by
      exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_left hpos).mp
    nlinarith

end GaussianTilt.MomentMapLinearDirichlet
