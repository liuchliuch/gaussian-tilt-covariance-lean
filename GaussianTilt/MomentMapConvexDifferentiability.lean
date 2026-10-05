import GaussianTilt.MomentMapExtendedDual

/-! # Differentiability of finite convex potentials: scalar foundation

A finite convex real function fails to be differentiable at only countably
many points. A rational number inside each left/right derivative gap gives
an injective encoding of the exceptional set.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
namespace GaussianTilt.MomentMapCoercivity

lemma convex_hasDerivAt_of_left_eq_right {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (x : ℝ)
    (heq : derivWithin f (Iio x) x = derivWithin f (Ioi x) x) :
    HasDerivAt f (derivWithin f (Ioi x) x) x := by
  have hl := hf.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp : x ∈ interior (univ : Set ℝ))
  have hr := hf.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp : x ∈ interior (univ : Set ℝ))
  rw [heq] at hl
  apply hasDerivAt_iff_tendsto_slope_left_right.mpr
  exact ⟨(hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hl,
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hr⟩

lemma convex_derivative_gap_of_not_differentiable {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    {x : ℝ} (hx : ¬ DifferentiableAt ℝ f x) :
    derivWithin f (Iio x) x < derivWithin f (Ioi x) x := by
  apply lt_of_le_of_ne
  · exact hf.leftDeriv_le_rightDeriv_of_mem_interior (by simp)
  · intro heq
    exact hx (convex_hasDerivAt_of_left_eq_right hf x heq).differentiableAt

lemma convex_rightDeriv_le_leftDeriv {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    {x y : ℝ} (hxy : x < y) :
    derivWithin f (Ioi x) x ≤ derivWithin f (Iio y) y :=
  (hf.rightDeriv_le_slope_of_mem_interior (by simp) (mem_univ y) hxy).trans
    (hf.slope_le_leftDeriv_of_mem_interior (mem_univ x) (by simp) hxy)

theorem convex_countable_not_differentiable {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    {x | ¬ DifferentiableAt ℝ f x}.Countable := by
  let S := {x | ¬ DifferentiableAt ℝ f x}
  have hrat (x : S) : ∃ r : ℚ, derivWithin f (Iio x.val) x.val < r ∧
      (r : ℝ) < derivWithin f (Ioi x.val) x.val :=
    exists_rat_btwn (convex_derivative_gap_of_not_differentiable hf x.property)
  choose r hrleft hrright using hrat
  have hinj : Function.Injective r := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := convex_rightDeriv_le_leftDeriv hf hlt
      have hxl := hrright x
      have hyr := hrleft y
      rw [hxy] at hxl
      linarith
    · have h := convex_rightDeriv_le_leftDeriv hf hgt
      have hyl := hrright y
      have hxr := hrleft x
      rw [hxy] at hxr
      linarith
  haveI : Countable S := hinj.countable
  exact Set.to_countable S

/-- The one-dimensional almost-everywhere differentiability theorem is
proved from convexity, rather than assumed as an analytic input. -/
theorem convex_ae_differentiable_real {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ f x := by
  apply ae_iff.mpr
  exact (convex_countable_not_differentiable hf).measure_zero volume

end GaussianTilt.MomentMapCoercivity
