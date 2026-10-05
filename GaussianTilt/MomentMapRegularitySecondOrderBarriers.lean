import GaussianTilt.MomentMapRegularitySecondOrderPerturbation

/-!
# Quadratic barriers for unit Alexandrov density

The unit paraboloid has literal subgradient image equal to its source set.
Comparison with this paraboloid and a constant bounds the Dirichlet solution
on a normalized section and makes the uniform perturbation estimate explicit.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- The supporting slopes of the unit paraboloid are computed directly
from the inner-product identity, without a Jacobian formula. -/
lemma supportsAt_unit_paraboloid_iff (c : ℝ) (p x : E n) :
    SupportsAt (fun y => ‖y‖ ^ 2 / 2 + c) p x ↔ p = x := by
  constructor
  · intro hs
    have h := hs p
    change ‖x‖ ^ 2 / 2 + c + inner ℝ p (p - x) ≤ ‖p‖ ^ 2 / 2 + c at h
    rw [inner_sub_right, real_inner_self_eq_norm_sq] at h
    have he := norm_sub_sq_real p x
    have hn : ‖p - x‖ = 0 := by nlinarith [norm_nonneg (p - x)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  · intro hp y
    rw [hp]
    change ‖x‖ ^ 2 / 2 + c + inner ℝ x (y - x) ≤ ‖y‖ ^ 2 / 2 + c
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
    have he := norm_sub_sq_real x y
    nlinarith [sq_nonneg ‖x - y‖]

/-- The explicit supporting planes also prove convexity of the paraboloid. -/
lemma convexOn_unit_paraboloid (c : ℝ) :
    ConvexOn ℝ univ (fun y : E n => ‖y‖ ^ 2 / 2 + c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z : E n := a • x + b • y
  have hx := (supportsAt_unit_paraboloid_iff c z z).mpr rfl x
  have hy := (supportsAt_unit_paraboloid_iff c z z).mpr rfl y
  have hx' := mul_le_mul_of_nonneg_left hx ha
  have hy' := mul_le_mul_of_nonneg_left hy hb
  have hi : a * inner ℝ z (x - z) + b * inner ℝ z (y - z) = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right]
    have he : a • (x - z) + b • (y - z) = 0 := by
      rw [smul_sub, smul_sub]
      calc
        a • x - a • z + (b • y - b • z) = z - (a + b) • z := by
          dsimp [z]; module
        _ = 0 := by rw [hab, one_smul, sub_self]
    rw [he, inner_zero_right]
  change ‖z‖ ^ 2 / 2 + c ≤ a * (‖x‖ ^ 2 / 2 + c) + b * (‖y‖ ^ 2 / 2 + c)
  have he := congrArg (fun t : ℝ => t * (‖z‖ ^ 2 / 2 + c)) hab
  dsimp at he
  nlinarith

/-- Exact Alexandrov identity for the unit paraboloid, on every source set. -/
theorem subgradientImage_unit_paraboloid (c : ℝ) (A : Set (E n)) :
    subgradientImage (fun y => ‖y‖ ^ 2 / 2 + c) A = A := by
  ext p
  constructor
  · rintro ⟨x, hx, hs⟩
    have he := (supportsAt_unit_paraboloid_iff c p x).mp hs
    simpa only [he] using hx
  · intro hp
    exact ⟨p, hp, (supportsAt_unit_paraboloid_iff c p p).mpr rfl⟩

lemma supportsAt_constant_iff (c : ℝ) (p x : E n) :
    SupportsAt (fun _ => c) p x ↔ p = 0 := by
  constructor
  · intro hs
    have h := hs (x + p)
    change c + inner ℝ p (x + p - x) ≤ c at h
    rw [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg p])
  · rintro rfl y
    simp only [inner_zero_left, add_zero, le_refl]

lemma volume_subgradientImage_constant [NeZero n] (c : ℝ) (A : Set (E n)) :
    volume (subgradientImage (fun _ => c) A) = 0 := by
  have hs : subgradientImage (fun _ => c) A ⊆ {0} := by
    rintro p ⟨x, _, hp⟩
    exact (supportsAt_constant_iff c p x).mp hp
  apply le_antisymm _ (zero_le _)
  exact (measure_mono hs).trans_eq (measure_singleton 0)

/-- A unit-density zero-boundary Alexandrov solution on a set contained in
`closedBall 0 R` lies between the paraboloid barrier and zero. -/
theorem alexandrov_unit_density_barriers [NeZero n] {v : E n → ℝ}
    (hv : ConvexOn ℝ univ v) (hvc : Continuous v)
    {S : Set (E n)} (hS : IsCompact S) {R : ℝ} (hR : 0 ≤ R)
    (hSR : S ⊆ Metric.closedBall (0 : E n) R)
    (hbv : ∀ y ∈ frontier S, v y = 0)
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ S → volume (subgradientImage v A) = volume A) :
    ∀ x ∈ S, ‖x‖ ^ 2 / 2 - R ^ 2 / 2 ≤ v x ∧ v x ≤ 0 := by
  let q : E n → ℝ := fun y => ‖y‖ ^ 2 / 2 - R ^ 2 / 2
  have hqc : Continuous q := by fun_prop
  have hvid' : ∀ A : Set (E n), IsCompact A → A ⊆ S → volume (subgradientImage v A) =
      (volume.withDensity (fun _ => ENNReal.ofReal (1 : ℝ))) A := by simpa using hvid
  have hqid : ∀ A : Set (E n), IsCompact A → A ⊆ S → volume (subgradientImage q A) =
      (volume.withDensity (fun _ => ENNReal.ofReal (1 : ℝ))) A := by
    intro A _ _
    simpa [q, sub_eq_add_neg, subgradientImage_unit_paraboloid]
  have hqb : ∀ y ∈ frontier S, q y ≤ v y := by
    intro y hy
    rw [hbv y hy]
    have hn : ‖y‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hSR (hS.isClosed.closure_subset hy.1)
    dsimp [q]
    nlinarith [norm_nonneg y]
  have hlo := alexandrov_comparison_of_density_le hv hvc hqc hS hqb measurable_const
    (fun _ _ => zero_le_one) (fun _ _ => zero_lt_one) (fun _ _ => le_rfl) hvid' hqid
  have hzid : ∀ A : Set (E n), IsCompact A → A ⊆ S → volume (subgradientImage (fun _ => (0 : ℝ)) A) =
      (volume.withDensity (fun _ => ENNReal.ofReal (0 : ℝ))) A := by
    intro A _ _
    rw [volume_subgradientImage_constant]
    simp
  have hhi := alexandrov_comparison_of_density_le (convexOn_const (0 : ℝ) convex_univ)
    continuous_const hvc hS (fun y hy => (hbv y hy).le) measurable_const
    (fun _ _ => le_rfl) (fun _ _ => zero_lt_one) (fun _ _ => zero_le_one) hzid hvid'
  exact fun x hx => ⟨hlo x hx, hhi x hx⟩

/-- Dimension-only sup-norm control after affine section normalization. -/
theorem alexandrov_unit_density_abs_bound [NeZero n] {v : E n → ℝ}
    (hv : ConvexOn ℝ univ v) (hvc : Continuous v)
    {S : Set (E n)} (hS : IsCompact S) {R : ℝ} (hR : 0 ≤ R)
    (hSR : S ⊆ Metric.closedBall (0 : E n) R)
    (hbv : ∀ y ∈ frontier S, v y = 0)
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ S → volume (subgradientImage v A) = volume A) :
    ∀ x ∈ S, |v x| ≤ R ^ 2 / 2 := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := alexandrov_unit_density_barriers hv hvc hS hR hSR hbv hvid x hx
  rw [abs_of_nonpos hhi]
  nlinarith [sq_nonneg ‖x‖]

/-- Explicit stability on normalized sections: density oscillation `δ`
produces uniform error at most `δ R² / 2`. -/
theorem alexandrov_normalized_constant_density_perturbation [NeZero n] {u v f : E n → ℝ}
    (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    (huc : Continuous u) (hvc : Continuous v)
    {S : Set (E n)} (hS : IsCompact S) {R : ℝ} (hR : 0 ≤ R)
    (hSR : S ⊆ Metric.closedBall (0 : E n) R)
    (hbu : ∀ y ∈ frontier S, u y = 0) (hbv : ∀ y ∈ frontier S, v y = 0)
    (hfm : Measurable f) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hf : ∀ y ∈ interior S, |f y - 1| ≤ δ)
    (huid : ∀ A : Set (E n), IsCompact A → A ⊆ S →
      volume (subgradientImage u A) = (volume.withDensity (fun y => ENNReal.ofReal (f y))) A)
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ S → volume (subgradientImage v A) = volume A) :
    ∀ x ∈ S, |u x - v x| ≤ δ * R ^ 2 / 2 := by
  intro x hx
  have he := alexandrov_constant_density_perturbation hu hv huc hvc hS hbu hbv hfm hδ hδ1 hf huid hvid x hx
  have hvb := alexandrov_unit_density_abs_bound hv hvc hS hR hSR hbv hvid x hx
  exact he.trans (by nlinarith)

end GaussianTilt.MomentMapRegularity
