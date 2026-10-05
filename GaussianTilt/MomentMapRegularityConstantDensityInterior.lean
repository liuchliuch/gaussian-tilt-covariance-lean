import GaussianTilt.MomentMapRegularityConstantDensityPogorelov
import GaussianTilt.MomentMapRegularityHessian

/-!
# Depth-weighted interior Hessian bounds for smooth unit-density solutions

The logarithmic maximum is actually attained: its exponential extends
continuously to the compact section and vanishes on the boundary. This
turns the local Pogorelov calculation into a uniform interior estimate.
-/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The continuous exponential form of the Pogorelov test. -/
def pogorelovWeight (u : CoordinateSpace n → ℝ) (i : Fin n) (y : CoordinateSpace n) : ℝ :=
  (-u y) * coordinateHessian u y i i * Real.exp ((coordinateDerivative i u y)^2 / 2)

lemma continuous_pogorelovWeight {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (i : Fin n) : Continuous (pogorelovWeight u i) :=
  (hu.continuous.neg.mul (smooth_coordinateHessian hu i i).continuous).mul
    (Real.continuous_exp.comp (((smooth_coordinateDerivative hu i).continuous.pow 2).div_const 2))

lemma log_pogorelovWeight {u : CoordinateSpace n → ℝ} {i : Fin n} {x : CoordinateSpace n}
    (hx : u x < 0) (hw : 0 < coordinateHessian u x i i) :
    Real.log (pogorelovWeight u i x) = pogorelovTest u i x := by
  unfold pogorelovWeight pogorelovTest
  rw [Real.log_mul (mul_ne_zero (neg_ne_zero.mpr hx.ne) hw.ne') (Real.exp_ne_zero _),
    Real.log_mul (neg_ne_zero.mpr hx.ne) hw.ne', Real.log_exp, Real.log_neg_eq_log]
  ring

lemma coordinateHessian_diagonal_pos {u : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hH : (coordinateHessian u x).PosDef) (i : Fin n) : 0 < coordinateHessian u x i i := by
  have he : (Pi.single i (1 : ℝ) : CoordinateSpace n) ≠ 0 := by
    intro hz
    have hi := congrFun hz i
    simpa using hi
  have hp := hH.2 (Pi.single i 1) he
  simpa [Matrix.mulVec_single_one, single_dotProduct, Matrix.col] using hp

/-- A priori depth-weighted Hessian bound on a genuine zero-boundary smooth
unit-density section. The first-derivative bound is a lower-order input;
the second-derivative estimate is derived from the equation. -/
theorem pogorelov_weighted_hessian_bound_on_section {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    (hzero : ∀ y ∈ frontier S, u y = 0)
    (hneg : ∀ y ∈ interior S, u y < 0)
    (hH : ∀ y ∈ interior S, (coordinateHessian u y).PosDef)
    (hMA : ∀ y ∈ interior S, (coordinateHessian u y).det = 1)
    {M : ℝ} (hM : 0 ≤ M) (hDu : ∀ y ∈ S, ∀ i : Fin n, |coordinateDerivative i u y| ≤ M) :
    ∀ x ∈ interior S, ∀ i : Fin n,
      (-u x) * coordinateHessian u x i i ≤ ((n : ℝ) + M) * Real.exp (M^2 / 2) := by
  intro x hx i
  have hxw : 0 < coordinateHessian u x i i := coordinateHessian_diagonal_pos (hH x hx) i
  have hxF : 0 < pogorelovWeight u i x :=
    mul_pos (mul_pos (neg_pos.mpr (hneg x hx)) hxw) (Real.exp_pos _)
  obtain ⟨z, hz, hmax⟩ := hS.exists_isMaxOn ⟨x, interior_subset hx⟩
    (continuous_pogorelovWeight hu i).continuousOn
  have hzx : pogorelovWeight u i x ≤ pogorelovWeight u i z := hmax (interior_subset hx)
  have hzi : z ∈ interior S := by
    by_contra hnot
    have hzb : z ∈ frontier S := ⟨subset_closure hz, hnot⟩
    have hzF : pogorelovWeight u i z = 0 := by simp [pogorelovWeight, hzero z hzb]
    rw [hzF] at hzx
    exact hxF.not_ge hzx
  have hzw : 0 < coordinateHessian u z i i := coordinateHessian_diagonal_pos (hH z hzi) i
  have hlocal := hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hzi)
  have hQmax : IsLocalMax (pogorelovTest u i) z := by
    have hun : ∀ᶠ y in 𝓝 z, u y < 0 := hu.continuous.continuousAt.eventually
      (eventually_lt_nhds (hneg z hzi))
    have hwp : ∀ᶠ y in 𝓝 z, 0 < coordinateHessian u y i i :=
      (smooth_coordinateHessian hu i i).continuous.continuousAt.eventually (eventually_gt_nhds hzw)
    filter_upwards [hlocal, hun, hwp] with y hy hyn hyw
    rw [← log_pogorelovWeight hyn hyw, ← log_pogorelovWeight (hneg z hzi) hzw]
    exact Real.log_le_log (mul_pos (mul_pos (neg_pos.mpr hyn) hyw) (Real.exp_pos _)) hy
  have hnearMA : ∀ᶠ y in 𝓝 z, (coordinateHessian u y).det = 1 := by
    filter_upwards [isOpen_interior.mem_nhds hzi] with y hy
    exact hMA y hy
  have hzbound := pogorelov_weighted_hessian_bound_at_max hu i (hH z hzi) (hneg z hzi) hnearMA hQmax
  have hd : |coordinateDerivative i u z| ≤ M := hDu z hz i
  have hd2 : (coordinateDerivative i u z)^2 ≤ M^2 := by
    simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg (coordinateDerivative i u z)) hd 2)
  have hzwBound : (-u z) * coordinateHessian u z i i ≤ (n : ℝ) + M :=
    hzbound.trans (add_le_add_left hd _)
  have hFbound : pogorelovWeight u i z ≤ ((n : ℝ) + M) * Real.exp (M^2 / 2) := by
    exact mul_le_mul hzwBound (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
      (by positivity)
  have hexp : (1 : ℝ) ≤ Real.exp ((coordinateDerivative i u x)^2 / 2) :=
    Real.one_le_exp_iff.mpr (by positivity)
  calc
    (-u x) * coordinateHessian u x i i ≤ pogorelovWeight u i x := by
      exact le_mul_of_one_le_right (mul_nonneg (neg_pos.mpr (hneg x hx)).le hxw.le) hexp
    _ ≤ pogorelovWeight u i z := hzx
    _ ≤ _ := hFbound

/-- Interior diagonal Hessian bounds follow at any positive depth from the
boundary plane. -/
theorem pogorelov_hessian_diagonal_bound_at_depth {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    (hzero : ∀ y ∈ frontier S, u y = 0)
    (hneg : ∀ y ∈ interior S, u y < 0)
    (hH : ∀ y ∈ interior S, (coordinateHessian u y).PosDef)
    (hMA : ∀ y ∈ interior S, (coordinateHessian u y).det = 1)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hDu : ∀ y ∈ S, ∀ i : Fin n, |coordinateDerivative i u y| ≤ M)
    {x : CoordinateSpace n} (hx : x ∈ interior S) (hdepth : δ ≤ -u x) (i : Fin n) :
    coordinateHessian u x i i ≤ (((n : ℝ) + M) * Real.exp (M^2 / 2)) / δ := by
  apply (le_div_iff₀ hδ).mpr
  have hw := (coordinateHessian_diagonal_pos (hH x hx) i).le
  calc
    coordinateHessian u x i i * δ ≤ (-u x) * coordinateHessian u x i i := by
      nlinarith
    _ ≤ _ := pogorelov_weighted_hessian_bound_on_section hu hS hzero hneg hH hMA hM hDu x hx i

/-- The quantitative interior estimate controls every Hessian entry, using
positive semidefiniteness to recover mixed entries from diagonal bounds. -/
theorem pogorelov_hessian_entry_bound_at_depth {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    (hzero : ∀ y ∈ frontier S, u y = 0)
    (hneg : ∀ y ∈ interior S, u y < 0)
    (hH : ∀ y ∈ interior S, (coordinateHessian u y).PosDef)
    (hMA : ∀ y ∈ interior S, (coordinateHessian u y).det = 1)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hDu : ∀ y ∈ S, ∀ i : Fin n, |coordinateDerivative i u y| ≤ M)
    {x : CoordinateSpace n} (hx : x ∈ interior S) (hdepth : δ ≤ -u x) (i j : Fin n) :
    |coordinateHessian u x i j| ≤ (((n : ℝ) + M) * Real.exp (M^2 / 2)) / δ := by
  exact abs_entry_le_of_posSemidef_diagonal_bound (hH x hx).posSemidef
    (fun k => pogorelov_hessian_diagonal_bound_at_depth hu hS hzero hneg hH hMA hM hδ hDu hx hdepth k) i j

end GaussianTilt.MomentMapRegularity
