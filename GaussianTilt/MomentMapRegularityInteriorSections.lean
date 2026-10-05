import GaussianTilt.MomentMapRegularityInteriorSupport
import GaussianTilt.MomentMapAlexandrovMaximum

/-!
# Genuine strict-convex sections for interior regularity

A strict supporting gap is positive off the contact point. Compactness of
a sphere and convexity along rays then give coercivity of the gap, compact
positive-height sections, and convergence of these sections to their center.
These qualitative facts do not assume a Monge--Ampère regularity theorem.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- The nonnegative error above the actual supporting plane at `x`. -/
def supportResidual (φ : E n → ℝ) (p x y : E n) : ℝ :=
  φ y - φ x - inner ℝ p (y - x)

/-- A closed section of height `h` above an actual supporting plane. -/
def supportSection (φ : E n → ℝ) (p x : E n) (h : ℝ) : Set (E n) :=
  {y | supportResidual φ p x y ≤ h}

lemma supportResidual_self (φ : E n → ℝ) (p x : E n) :
    supportResidual φ p x x = 0 := by simp [supportResidual]

lemma supportResidual_nonneg {φ : E n → ℝ} {p x : E n}
    (hp : SupportsAt φ p x) (y : E n) : 0 ≤ supportResidual φ p x y := by
  have h := hp y
  dsimp [supportResidual]
  linarith

lemma supportResidual_eq_tilt (φ : E n → ℝ) (p x y : E n) :
    supportResidual φ p x y =
      (φ y - inner ℝ p y) - (φ x - inner ℝ p x) := by
  simp only [supportResidual, inner_sub_right]
  ring

lemma continuous_supportResidual {φ : E n → ℝ} (hφ : Continuous φ) (p x : E n) :
    Continuous (supportResidual φ p x) := by
  unfold supportResidual
  exact (hφ.sub continuous_const).sub
    (continuous_const.inner (continuous_id.sub continuous_const))

lemma convexOn_supportResidual {φ : E n → ℝ} (hc : ConvexOn ℝ univ φ) (p x : E n) :
    ConvexOn ℝ univ (supportResidual φ p x) := by
  have he : supportResidual φ p x = fun y => (φ y - inner ℝ p y) - (φ x - inner ℝ p x) :=
    funext (supportResidual_eq_tilt φ p x)
  rw [he]
  exact (alexandrov_convex_tilt hc p).sub (concaveOn_const _ convex_univ)

lemma convex_supportSection {φ : E n → ℝ} (hc : ConvexOn ℝ univ φ)
    (p x : E n) (h : ℝ) : Convex ℝ (supportSection φ p x h) := by
  simpa only [supportSection, mem_univ, true_and] using
    (convexOn_supportResidual hc p x).convex_le h

lemma strict_supportResidual_pos {φ : E n → ℝ} (hc : StrictConvexOn ℝ univ φ)
    {p x y : E n} (hp : SupportsAt φ p x) (hy : y ≠ x) :
    0 < supportResidual φ p x y := by
  have hs := hc.2 (mem_univ x) (mem_univ y) hy.symm
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hp' := hp ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
  simp only [smul_eq_mul] at hs
  simp only [inner_sub_right, inner_add_right, inner_smul_right] at hp'
  dsimp [supportResidual]
  rw [inner_sub_right]
  linarith

/-- Strict convexity makes each fixed supporting plane touch at only one
source point. This is the converse of the localization strictness criterion. -/
lemma subsingleton_contactSet_of_strictConvexOn {φ : E n → ℝ}
    (hc : StrictConvexOn ℝ univ φ) (p : E n) : (contactSet φ p).Subsingleton := by
  intro x hx y hy
  by_contra hne
  have hpos := strict_supportResidual_pos hc hx (Ne.symm hne)
  have hxy := hx y
  have hyx := hy x
  have he : inner ℝ p (x - y) = -inner ℝ p (y - x) := by
    rw [← inner_neg_right, neg_sub]
  rw [he] at hyx
  dsimp [supportResidual] at hpos
  linarith

/-- The lower bound on a sphere propagates linearly along every outgoing
ray of a nonnegative convex function vanishing at the center. -/
lemma convex_ray_lower_bound {F : E n → ℝ} (hc : ConvexOn ℝ univ F)
    {x : E n} (hx : F x = 0) {r δ : ℝ} (hr : 0 < r)
    (hδ : ∀ z ∈ Metric.sphere x r, δ ≤ F z) {y : E n} (hy : r ≤ ‖y - x‖) :
    δ * ‖y - x‖ ≤ r * F y := by
  let d := ‖y - x‖
  have hd : 0 < d := hr.trans_le hy
  let t := r / d
  have ht0 : 0 ≤ t := (div_pos hr hd).le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr hy
  let z := (1 - t) • x + t • y
  have he : z - x = t • (y - x) := by dsimp [z]; module
  have hz : z ∈ Metric.sphere x r := by
    rw [Metric.mem_sphere, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact div_mul_cancel₀ r hd.ne'
  have hcv := hc.2 (mem_univ x) (mem_univ y) (sub_nonneg.mpr ht1) ht0 (by ring)
  simp only [smul_eq_mul, hx, mul_zero, zero_add] at hcv
  have hdz : δ ≤ t * F y := (hδ z hz).trans hcv
  have hmul := mul_le_mul_of_nonneg_right hdz hd.le
  change δ * d ≤ r * F y
  calc
    δ * d ≤ t * F y * d := hmul
    _ = r * F y := by dsimp [t]; field_simp

/-- Every strict supporting gap has a positive linear growth rate outside
any prescribed ball. The rate is constructed by minimizing on its sphere. -/
theorem strict_supportResidual_linear_growth {φ : E n → ℝ}
    (hc : StrictConvexOn ℝ univ φ) {p x : E n} (hp : SupportsAt φ p x)
    {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y, r ≤ ‖y - x‖ →
      δ * ‖y - x‖ ≤ r * supportResidual φ p x y := by
  by_cases hn : n = 0
  · subst n
    refine ⟨1, zero_lt_one, ?_⟩
    intro y hy
    have he : y = x := Subsingleton.elim _ _
    rw [he, sub_self, norm_zero] at hy
    exact (not_le_of_gt hr hy).elim
  · letI : NeZero n := ⟨hn⟩
    have hφ : Continuous φ := continuousOn_univ.mp (hc.convexOn.continuousOn isOpen_univ)
    obtain ⟨z, hz, hmin⟩ := (isCompact_sphere x r).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr hr.le) (continuous_supportResidual hφ p x).continuousOn
    have hzx : z ≠ x := by
      intro he
      have hz0 : (0 : ℝ) = r := by simpa only [he, Metric.mem_sphere, dist_self] using hz
      exact hr.ne' hz0.symm
    refine ⟨supportResidual φ p x z, strict_supportResidual_pos hc hp hzx, ?_⟩
    intro y hy
    exact convex_ray_lower_bound (convexOn_supportResidual hc.convexOn p x)
      (supportResidual_self φ p x) hr (fun w hw => hmin hw) hy

/-- Every section over a genuine support of a strictly convex finite
function is compact. No source transport law is needed. -/
theorem isCompact_supportSection_of_strictConvexOn {φ : E n → ℝ}
    (hc : StrictConvexOn ℝ univ φ) {p x : E n} (hp : SupportsAt φ p x) (h : ℝ) :
    IsCompact (supportSection φ p x h) := by
  have hφ : Continuous φ := continuousOn_univ.mp (hc.convexOn.continuousOn isOpen_univ)
  obtain ⟨δ, hδ, hbound⟩ := strict_supportResidual_linear_growth hc hp (r := 1) zero_lt_one
  apply Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (continuous_supportResidual hφ p x) continuous_const)
  apply (Metric.isBounded_closedBall (x := x) (r := max 1 (h / δ))).subset
  intro y hy
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_cases hry : 1 ≤ ‖y - x‖
  · apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ hδ).mpr
    have hh := hbound y hry
    change supportResidual φ p x y ≤ h at hy
    nlinarith
  · exact (le_of_lt (lt_of_not_ge hry)).trans (le_max_left _ _)

/-- Strict-convex sections shrink to their center. Both the positive
height threshold and compactness of every section have been derived. -/
theorem small_supportSection_subset_ball {φ : E n → ℝ}
    (hc : StrictConvexOn ℝ univ φ) {p x : E n} (hp : SupportsAt φ p x)
    {r : ℝ} (hr : 0 < r) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, h < h₀ →
      supportSection φ p x h ⊆ Metric.ball x r := by
  obtain ⟨δ, hδ, hbound⟩ := strict_supportResidual_linear_growth hc hp hr
  refine ⟨δ, hδ, ?_⟩
  intro h hh y hy
  rw [Metric.mem_ball, dist_eq_norm]
  by_contra hfar
  have hdist : r ≤ ‖y - x‖ := le_of_not_gt hfar
  have hg := hbound y hdist
  have hl := mul_le_mul_of_nonneg_left hdist hδ.le
  change supportResidual φ p x y ≤ h at hy
  have hu := mul_le_mul_of_nonneg_left hy hr.le
  have hlt := mul_lt_mul_of_pos_left hh hr
  nlinarith

lemma center_mem_interior_supportSection {φ : E n → ℝ}
    (hφ : Continuous φ) (p x : E n) {h : ℝ} (hh : 0 < h) :
    x ∈ interior (supportSection φ p x h) := by
  apply mem_interior.mpr
  refine ⟨{y | supportResidual φ p x y < h}, ?_, ?_, ?_⟩
  · exact fun y hy => show supportResidual φ p x y ≤ h from hy.le
  · exact isOpen_lt (continuous_supportResidual hφ p x) continuous_const
  · simpa only [mem_setOf_eq, supportResidual_self] using hh

lemma supportResidual_eq_height_on_frontier {φ : E n → ℝ}
    (hφ : Continuous φ) (p x : E n) (h : ℝ) :
    ∀ y ∈ frontier (supportSection φ p x h), supportResidual φ p x y = h :=
  frontier_le_subset_eq (continuous_supportResidual hφ p x) continuous_const

end GaussianTilt.MomentMapRegularity
