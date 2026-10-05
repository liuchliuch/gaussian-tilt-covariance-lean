import GaussianTilt.MomentMapLinearDirichletHalfBallGeometry

/-! # Genuine zero-boundary half-ball Poisson corrections

Two separately proved quadratic barriers control the spherical and flat
pieces. Their continuous minimum supplies true zero boundary continuity,
without pretending the corner has a smooth strictly subharmonic definer.
-/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def halfBallJointBarrier (j : Fin n) (F R : ℝ) (x : CoordinateSpace n) : ℝ :=
  min |halfBallRadialBarrier F R x| |halfBallNormalBarrier j F R x|

lemma halfBallJointBarrier_nonneg (j : Fin n) (F R : ℝ) (x : CoordinateSpace n) :
    0 ≤ halfBallJointBarrier j F R x := le_min (abs_nonneg _) (abs_nonneg _)

lemma halfBallJointBarrier_continuous (j : Fin n) (F R : ℝ) :
    Continuous (halfBallJointBarrier j F R) :=
  (halfBallRadialBarrier_smooth F R).continuous.abs.inf (halfBallNormalBarrier_smooth j F R).continuous.abs

lemma halfBallJointBarrier_frontier (j : Fin n) (F R : ℝ) {x : CoordinateSpace n}
    (hx : x ∈ frontier (coordinateHalfBall j R)) : halfBallJointBarrier j F R x = 0 := by
  obtain ⟨_, _, hr | hj⟩ := coordinateHalfBall_frontier hx
  · have hz : halfBallRadialBarrier F R x = 0 := by
      rw [halfBallRadialBarrier, calabiBallCutoff_eq_norm]
      simp only [map_zero, sub_zero, hr, sub_self, mul_zero]
    simp only [halfBallJointBarrier, hz, abs_zero]
    exact min_eq_left (abs_nonneg (halfBallNormalBarrier j F R x))
  · have hz : halfBallNormalBarrier j F R x = 0 := by simp only [halfBallNormalBarrier, hj, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
    simp only [halfBallJointBarrier, hz, abs_zero]
    exact min_eq_right (abs_nonneg (halfBallRadialBarrier F R x))

/-- The actual correction exists with dimension-independent sup and height
bounds, is genuinely continuous and zero on both boundary pieces, and
solves the pointwise Poisson equation in the half-ball. -/
theorem exists_halfBall_poisson_correction_with_weak_identity [NeZero n]
    (j : Fin n) {R F α H : ℝ} (hR : 0 < R) (hF : 0 ≤ F)
    (f : CoordinateSpace n → ℝ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α)
    (hfb : ∀ x ∈ coordinateHalfBall j R, |f x| ≤ F) :
    ∃ v : CoordinateSpace n → ℝ, Continuous v ∧ MemLp v 2 volume ∧
      (∀ x ∈ coordinateHalfBall j R, ContDiffAt ℝ 2 v x) ∧
      (∀ x ∈ coordinateHalfBall j R, euclideanLaplacian v x = -f x) ∧
      (∀ x ∉ coordinateHalfBall j R, v x = 0) ∧
      (∀ x, |v x| ≤ F * R ^ 2) ∧
      (∀ x, |v x| ≤ 2 * F * R * |x j|) ∧
      (∀ ψ : CoordinateSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ coordinateHalfBall j R →
        (∫ x, v x * euclideanLaplacian ψ x) = -(∫ x, f x * ψ x)) := by
  let Ω := coordinateHalfBall j R
  have hΩ := isOpen_coordinateHalfBall j R
  have hΩb := isBounded_coordinateHalfBall j R
  have hstrip : ∀ x ∈ Ω, |x j| ≤ R := fun _ hx => coordinateHalfBall_strip j j hx
  let fL := (hfc.memLp_of_hasCompactSupport hfs (p := 2) (μ := (volume : Measure (CoordinateSpace n)))).toLp f
  let u := weakDirichletLaplaceSolution j hR.le hstrip fL
  have hforce : ∀ᵐ x ∂volume, x ∈ Ω → |fL x| ≤ F := by
    filter_upwards [(hfc.memLp_of_hasCompactSupport hfs (p := 2) (μ := volume)).coeFn_toLp] with x hx hxΩ
    rw [show fL x = f x from hx]
    exact hfb x hxΩ
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hrad : ∀ᵐ x ∂volume, x ∈ Ω → |dirichletValue Ω u x| ≤ halfBallRadialBarrier F R x := by
    apply weakDirichletLaplaceSolution_abs_le_global_smooth_barrier hΩ hΩb j hR.le hstrip fL
      (halfBallRadialBarrier_smooth F R) (fun x hx => (halfBallRadialBarrier_bounds hF hR hx).1)
    filter_upwards [hforce] with x hx hxΩ
    rw [halfBallRadialBarrier_laplacian]
    exact (hx hxΩ).trans (by nlinarith [mul_nonneg hF (show 0 ≤ (n : ℝ) - 1 by linarith)])
  have hnormal : ∀ᵐ x ∂volume, x ∈ Ω → |dirichletValue Ω u x| ≤ halfBallNormalBarrier j F R x := by
    apply weakDirichletLaplaceSolution_abs_le_global_smooth_barrier hΩ hΩb j hR.le hstrip fL
      (halfBallNormalBarrier_smooth j F R) (fun x hx => (halfBallNormalBarrier_bounds hF hR hx).1)
    filter_upwards [hforce] with x hx hxΩ
    rw [halfBallNormalBarrier_laplacian]
    exact (hx hxΩ).trans (by linarith)
  have hweak : ∀ᵐ x ∂volume, x ∈ Ω → |dirichletValue Ω u x| ≤ |halfBallJointBarrier j F R x| := by
    filter_upwards [hrad, hnormal] with x hx hy hxΩ
    rw [abs_of_nonneg (halfBallJointBarrier_nonneg j F R x)]
    exact le_min ((hx hxΩ).trans (le_abs_self _)) ((hy hxΩ).trans (le_abs_self _))
  obtain ⟨v, hv, hvC2, hvP, hv0, hvB, hvAE⟩ := exists_classicalDirichletLaplaceSolution_of_weak_barrier
    hΩ hΩb j hR.le hstrip f hfc hfs hα hα1 hH hholder
    (halfBallJointBarrier_continuous j F R) (fun x hx => halfBallJointBarrier_frontier j F R hx) hweak
  have hvLp : MemLp v 2 volume := (memLp_congr_ae hvAE).mpr (Lp.memLp (dirichletValue Ω u))
  refine ⟨v, hv, hvLp, hvC2, hvP, hv0, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ Ω
    · have hb := hvB x
      rw [abs_of_nonneg (halfBallJointBarrier_nonneg j F R x)] at hb
      have hradx := halfBallRadialBarrier_bounds hF hR hx
      exact (hb.trans (min_le_left _ _)).trans
        (by simpa only [abs_of_nonneg hradx.1] using hradx.2)
    · rw [hv0 x hx, abs_zero]
      exact mul_nonneg hF (sq_nonneg R)
  · intro x
    by_cases hx : x ∈ Ω
    · have hb := hvB x
      rw [abs_of_nonneg (halfBallJointBarrier_nonneg j F R x)] at hb
      have hnormalx := halfBallNormalBarrier_bounds hF hR hx
      have hh := (hb.trans (min_le_right _ _)).trans
        (by simpa only [abs_of_nonneg hnormalx.1] using hnormalx.2)
      exact hh.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
    · rw [hv0 x hx, abs_zero]
      positivity

  · intro ψ hψ hψc hψΩ
    calc
      _ = ∫ x, dirichletValue Ω u x * euclideanLaplacian ψ x := by
        apply integral_congr_ae
        filter_upwards [hvAE] with x hx
        rw [hx]
      _ = -(∫ x, fL x * ψ x) := weakDirichletLaplaceSolution_distribution j hR.le hstrip fL hψ hψc hψΩ
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [(hfc.memLp_of_hasCompactSupport hfs (p := 2) (μ := volume)).coeFn_toLp] with x hx
        rw [show fL x = f x from hx]

theorem exists_halfBall_poisson_correction [NeZero n]
    (j : Fin n) {R F α H : ℝ} (hR : 0 < R) (hF : 0 ≤ F)
    (f : CoordinateSpace n → ℝ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α)
    (hfb : ∀ x ∈ coordinateHalfBall j R, |f x| ≤ F) :
    ∃ v : CoordinateSpace n → ℝ, Continuous v ∧ MemLp v 2 volume ∧
      (∀ x ∈ coordinateHalfBall j R, ContDiffAt ℝ 2 v x) ∧
      (∀ x ∈ coordinateHalfBall j R, euclideanLaplacian v x = -f x) ∧
      (∀ x ∉ coordinateHalfBall j R, v x = 0) ∧
      (∀ x, |v x| ≤ F * R ^ 2) ∧
      (∀ x, |v x| ≤ 2 * F * R * |x j|) := by
  obtain ⟨v, hv, hl, hc, hp, hz, hb, hh, _⟩ := exists_halfBall_poisson_correction_with_weak_identity
    j hR hF f hfc hfs hα hα1 hH hholder hfb
  exact ⟨v, hv, hl, hc, hp, hz, hb, hh⟩

end GaussianTilt.MomentMapLinearDirichlet
