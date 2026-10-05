import GaussianTilt.MomentMapBoundaryRegularityNegativeContact
import GaussianTilt.MomentMapClassicalDirichletMixedCalculus

/-!
# The first genuine critical-density estimate

A quadratic barrier and the negative-contact ABP theorem show that an
actual nonnegative supersolution which is small somewhere in the half-ball
has a quantitatively large low-value set. No regularity or Harnack estimate
is supplied as a premise.
-/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped Topology BigOperators ContDiff Gradient ENNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma trace_le_of_upper_ellipticity {A : Matrix (Fin n) (Fin n) ℝ} {Λ : ℝ}
    (hA : ∀ v : CoordinateSpace n, v ⬝ᵥ (A *ᵥ v) ≤ Λ * (v ⬝ᵥ v)) :
    A.trace ≤ (n : ℝ) * Λ := by
  have hd (i : Fin n) : A i i ≤ Λ := by
    have h := hA (Pi.single i 1)
    simpa only [Matrix.mulVec_single, MulOpposite.op_one, one_smul,
      single_dotProduct, Matrix.col_apply, one_mul, Pi.single_eq_same, mul_one] using h
  calc
    _ ≤ ∑ _i : Fin n, Λ := Finset.sum_le_sum (fun i _ => hd i)
    _ = _ := by simp

def abpCriticalCoefficient (n : ℕ) (lam Λ : ℝ) : ℝ :=
  (n.factorial : ℝ) * ((1 + 8 * (n : ℝ) * Λ) / lam)^n

lemma abpCriticalCoefficient_pos {lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) :
    0 < abpCriticalCoefficient n lam Λ := by
  unfold abpCriticalCoefficient
  positivity

/-- Actual measurable-coefficient critical-density estimate on the unit
ball. The coefficient field may be entirely discontinuous. -/
theorem elliptic_critical_density_unit_ball {u : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) {lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ)
    {A : E n → Matrix (Fin n) (Fin n) ℝ}
    (hlo : ∀ y ∈ Metric.ball (0 : E n) 1,
      (A y - lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hup : ∀ y ∈ Metric.ball (0 : E n) 1, ∀ v : CoordinateSpace n,
      v ⬝ᵥ (A y *ᵥ v) ≤ Λ * (v ⬝ᵥ v))
    (hLu : ∀ y ∈ Metric.ball (0 : E n) 1,
      linearizedMA (A y) (coordinatePullback u) (coordinateEquiv n y) ≤ 1)
    (hun : ∀ y ∈ Metric.closedBall (0 : E n) 1, 0 ≤ u y)
    (hsmall : ∃ x ∈ Metric.closedBall (0 : E n) (1/2), u x ≤ 1) :
    volume (Metric.ball (0 : E n) (1/2)) ≤ ENNReal.ofReal (abpCriticalCoefficient n lam Λ) *
      volume {y | y ∈ Metric.ball (0 : E n) 1 ∧ u y < 4} := by
  let e := coordinateEquiv n
  let η := calabiBallCutoff (0 : CoordinateSpace n) 1
  let w : E n → ℝ := fun y => u y - 4 * η (e y)
  have hη : ContDiff ℝ ∞ η := contDiff_calabiBallCutoff _ _
  have hw : ContDiff ℝ ∞ w := hu.sub (contDiff_const.mul (hη.comp e.contDiff))
  have hηeq (y : E n) : η (e y) = 1 - ‖y‖^2 := by
    dsimp only [η]
    rw [calabiBallCutoff_eq_norm]
    simp [e]
  have hwp : coordinatePullback w = fun z => coordinatePullback u z - 4 * η z := by
    funext z
    simp [coordinatePullback, w, e]
  have hin : interior (Metric.closedBall (0 : E n) 1) = Metric.ball 0 1 :=
    interior_closedBall _ one_ne_zero
  obtain ⟨x, hx, hux⟩ := hsmall
  have hxn : ‖x‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hxS : x ∈ Metric.closedBall (0 : E n) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hwx : w x ≤ -2 := by
    dsimp only [w]
    rw [hηeq]
    nlinarith [norm_nonneg x]
  have hb : ∀ y ∈ frontier (Metric.closedBall (0 : E n) 1), 0 ≤ w y := by
    intro y hy
    rw [frontier_closedBall _ one_ne_zero] at hy
    have hyn : ‖y‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hy
    have hyS : y ∈ Metric.closedBall (0 : E n) 1 := by simpa [Metric.mem_closedBall, hyn]
    dsimp only [w]
    rw [hηeq, hyn]
    simpa using hun y hyS
  have hnear (y : E n) (hy : y ∈ negativeLowerContactSet (Metric.closedBall 0 1) w) :
      y ∈ Metric.ball (0 : E n) 1 := by
    exact hin ▸ hy.1.1
  have hLw (y : E n) (hy : y ∈ negativeLowerContactSet (Metric.closedBall 0 1) w) :
      linearizedMA (A y) (coordinatePullback w) (e y) ≤ 1 + 8 * (n : ℝ) * Λ := by
    have hU : ContDiffAt ℝ 2 (coordinatePullback u) (e y) :=
      ((contDiff_infty.mp hu 2).comp e.symm.contDiff).contDiffAt
    rw [hwp, linearizedMA_sub_at _ hU
      (contDiffAt_const.mul (contDiff_infty.mp hη 2).contDiffAt),
      linearizedMA_const_mul_at _ (contDiff_infty.mp hη 2).contDiffAt,
      linearizedMA_calabiBallCutoff]
    have ht := trace_le_of_upper_ellipticity (hup y (hnear y hy))
    have hlu := hLu y (hnear y hy)
    linarith
  have hlow : negativeLowerContactSet (Metric.closedBall (0 : E n) 1) w ⊆
      {y | y ∈ Metric.ball (0 : E n) 1 ∧ u y < 4} := by
    intro y hy
    refine ⟨hnear y hy, ?_⟩
    have hn := hy.2
    change u y - 4 * η (e y) < 0 at hn
    rw [hηeq] at hn
    nlinarith [sq_nonneg ‖y‖]
  have habp := smooth_abp_negative_contact_measure (isCompact_closedBall (0 : E n) 1) hw hxS
    (show 0 < (2 : ℝ) by norm_num) (by simpa using Metric.diam_closedBall (x := (0 : E n)) (by norm_num : (0 : ℝ) ≤ 1))
    hlam (by positivity : 0 ≤ 1 + 8 * (n : ℝ) * Λ) (by linarith : w x < 0) hb
    (fun y hy => hlo y (hnear y hy)) hLw
  have hr : (1/2 : ℝ) ≤ -w x / (2 * 2) := by linarith
  calc
    _ ≤ volume (Metric.ball (0 : E n) (-w x / (2 * 2))) := measure_mono (Metric.ball_subset_ball hr)
    _ ≤ _ := habp.trans (mul_le_mul_left' (measure_mono hlow) _)

end GaussianTilt.MomentMapRegularity
