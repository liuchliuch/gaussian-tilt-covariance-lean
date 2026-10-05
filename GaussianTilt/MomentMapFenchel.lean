import GaussianTilt.MomentMapCoercivity

/-! # Actual bounded-target Fenchel potentials

The source candidate is an ordinary supremum of affine functions on the
bounded target. Its finiteness, convexity, Lipschitz regularity, and coercive
lower bound are proved. No conjugacy or analytic identity is postulated.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators InnerProductSpace
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

def fenchelValues (K : Set (E n)) (u : E n → ℝ) (x : E n) : Set ℝ :=
  (fun y => ⟪x, y⟫_ℝ - u y) '' K

def fenchel (K : Set (E n)) (u : E n → ℝ) (x : E n) : ℝ :=
  sSup (fenchelValues K u x)

lemma fenchelValues_nonempty {K : Set (E n)} (hK : K.Nonempty) (u : E n → ℝ) (x : E n) :
    (fenchelValues K u x).Nonempty := hK.image _

lemma fenchelValues_bddAbove {K : Set (E n)} {u : E n → ℝ} {R : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ y ∈ K, 0 ≤ u y) (x : E n) :
    BddAbove (fenchelValues K u x) := by
  refine ⟨‖x‖ * R, ?_⟩
  rintro a ⟨y, hy, rfl⟩
  have hi := real_inner_le_norm x y
  have hn := mul_le_mul_of_nonneg_left (hK y hy) (norm_nonneg x)
  linarith [hu y hy]

theorem fenchel_young {K : Set (E n)} {u : E n → ℝ} {R : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ y ∈ K, 0 ≤ u y) (x : E n)
    {y : E n} (hy : y ∈ K) : ⟪x, y⟫_ℝ - u y ≤ fenchel K u x :=
  le_csSup (fenchelValues_bddAbove hK hu x) ⟨y, hy, rfl⟩

theorem fenchel_nonneg {K : Set (E n)} {u : E n → ℝ} {R : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ y ∈ K, 0 ≤ u y)
    (h0 : (0 : E n) ∈ K) (hu0 : u 0 = 0) (x : E n) : 0 ≤ fenchel K u x := by
  simpa [hu0] using fenchel_young hK hu x h0

theorem fenchel_convex {K : Set (E n)} {u : E n → ℝ} {R : ℝ}
    (hKn : K.Nonempty) (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ y ∈ K, 0 ≤ u y) :
    ConvexOn ℝ univ (fenchel K u) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  apply csSup_le (fenchelValues_nonempty hKn _ _)
  rintro v ⟨y, hy, rfl⟩
  have hx := mul_le_mul_of_nonneg_left (fenchel_young hK hu x hy) ha
  have hz := mul_le_mul_of_nonneg_left (fenchel_young hK hu z hy) hb
  have hsum : a * u y + b * u y = u y := by rw [← add_mul, hab, one_mul]
  simp only [inner_add_left, inner_smul_left, conj_trivial, smul_eq_mul]
  nlinarith

lemma fenchel_one_sided_lipschitz {K : Set (E n)} {u : E n → ℝ} {R : ℝ}
    (hKn : K.Nonempty) (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ y ∈ K, 0 ≤ u y)
    (x z : E n) : fenchel K u x ≤ fenchel K u z + R * ‖x - z‖ := by
  apply csSup_le (fenchelValues_nonempty hKn _ _)
  rintro v ⟨y, hy, rfl⟩
  have hz := fenchel_young hK hu z hy
  have hi := real_inner_le_norm (x - z) y
  have hn := mul_le_mul_of_nonneg_left (hK y hy) (norm_nonneg (x - z))
  rw [inner_sub_left] at hi
  nlinarith

theorem fenchel_lipschitz {K : Set (E n)} {u : E n → ℝ} {R : ℝ}
    (hKn : K.Nonempty) (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ y ∈ K, 0 ≤ u y) :
    LipschitzWith R.toNNReal (fenchel K u) := by
  apply LipschitzWith.of_dist_le'
  intro x z
  rw [Real.dist_eq, dist_eq_norm, abs_le]
  have hx := fenchel_one_sided_lipschitz hKn hK hu x z
  have hz := fenchel_one_sided_lipschitz hKn hK hu z x
  rw [norm_sub_rev z x] at hz
  constructor <;> linarith

/-- A bounded dual potential on an inner ball gives a linear lower bound
for its actual Fenchel supremum. -/
theorem fenchel_linear_lower_bound {K : Set (E n)} {u : E n → ℝ} {R r B : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ y ∈ K, 0 ≤ u y)
    (hr : 0 < r) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (huB : ∀ y ∈ Metric.closedBall (0 : E n) r, u y ≤ B)
    (x : E n) : r * ‖x‖ - B ≤ fenchel K u x := by
  by_cases hx : x = 0
  · subst x
    have h0 : (0 : E n) ∈ Metric.closedBall 0 r := Metric.mem_closedBall_self hr.le
    have h := fenchel_young hK hu 0 (hball h0)
    simp only [inner_zero_left, zero_sub, norm_zero, mul_zero] at h ⊢
    linarith [huB 0 h0]
  · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let y := (r / ‖x‖) • x
    have hy : y ∈ Metric.closedBall (0 : E n) r := by
      simp only [Metric.mem_closedBall, dist_zero_right, y, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hr hxn), div_mul_cancel₀ _ hxn.ne', le_rfl]
    have h := fenchel_young hK hu x (hball hy)
    have hinner : ⟪x, y⟫_ℝ = r * ‖x‖ := by
      dsimp only [y]
      rw [inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    rw [hinner] at h
    linarith [huB y hy]

/-- A normalized source candidate has a lower bound whose intercept is
fixed; the inverse slope grows only linearly with the dual budget. -/
theorem fenchel_budget_lower_bound {K : Set (E n)} {u : E n → ℝ} {R r B : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ y ∈ K, 0 ≤ u y)
    (hr : 0 < r) (hB : 0 ≤ B) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hu0 : u 0 = 0) (huB : ∀ y ∈ Metric.closedBall (0 : E n) r, u y ≤ B)
    (x : E n) : r / (B + 1) * ‖x‖ - 1 ≤ fenchel K u x := by
  have hp : 0 < B + 1 := by positivity
  have h0 := fenchel_nonneg hK hu (hball (Metric.mem_closedBall_self hr.le)) hu0 x
  have hlin := fenchel_linear_lower_bound hK hu hr hball huB x
  have heq : r / (B + 1) * ‖x‖ - 1 = (r * ‖x‖ - (B + 1)) / (B + 1) := by
    field_simp
  rw [heq]
  apply (div_le_iff₀ hp).mpr
  nlinarith [mul_nonneg hB h0]

end GaussianTilt.MomentMapCoercivity
