import GaussianTilt.MomentMapRegularityLocalization

/-! # Genuine supporting planes and the contact-set strictness criterion

Supporting slopes at every source point are constructed from the dense set
of genuine differentiability points and the compact closed support graph.
Strict convexity is then reduced exactly to singleton contact sets.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Every point of a finite globally Lipschitz convex function has a literal
global supporting plane. No differentiability at that point is assumed. -/
theorem exists_supportsAt_of_lipschitz_convex {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ) (x : E n) :
    ∃ p : E n, SupportsAt φ p x := by
  let G := (Metric.closedBall x 1 ×ˢ Metric.closedBall (0 : E n) (L : ℝ)) ∩
    {z : E n × E n | SupportsAt φ z.2 z.1}
  have hG : IsCompact G := ((isCompact_closedBall x 1).prod
    (isCompact_closedBall 0 (L : ℝ))).inter_right (isClosed_supportsAt_graph hL.continuous)
  have hclosed : IsClosed (Prod.fst '' G) := (hG.image continuous_fst).isClosed
  have hdense := volume.dense_of_ae (MomentMapCoercivity.convex_ae_differentiable hc)
  have hxcl : x ∈ closure (Prod.fst '' G) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨y, hyd, hyδ⟩ := (Metric.mem_closure_iff.mp (hdense x))
      (min 1 ε) (lt_min zero_lt_one hε)
    have hsupport := supportsAt_gradient hc hyd
    refine ⟨y, ?_, lt_of_lt_of_le hyδ (min_le_right _ _)⟩
    refine ⟨(y, gradient φ y), ⟨⟨?_, ?_⟩, hsupport⟩, rfl⟩
    · rw [Metric.mem_closedBall, dist_comm]
      exact (lt_of_lt_of_le hyδ (min_le_left _ _)).le
    · simpa only [Metric.mem_closedBall, dist_zero_right] using supportsAt_norm_le hL hsupport
  rw [hclosed.closure_eq] at hxcl
  obtain ⟨⟨y, p⟩, hmem, he⟩ := hxcl
  change y = x at he
  subst y
  exact ⟨p, hmem.2⟩

/-- Equality in a strict convex combination propagates its supporting
plane to both endpoints. -/
lemma supportsAt_endpoints_of_convex_combination_eq {φ : E n → ℝ}
    {x y p : E n} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hs : SupportsAt φ p (a • x + b • y))
    (he : φ (a • x + b • y) = a * φ x + b * φ y) :
    SupportsAt φ p x ∧ SupportsAt φ p y := by
  let z := a • x + b • y
  have hix : inner ℝ p z = a * inner ℝ p x + b * inner ℝ p y := by
    simp [z, inner_add_right, inner_smul_right]
  have hx := hs x
  have hy := hs y
  change φ z + inner ℝ p (x - z) ≤ φ x at hx
  change φ z + inner ℝ p (y - z) ≤ φ y at hy
  rw [inner_sub_right] at hx hy
  change φ z = a * φ x + b * φ y at he
  have hgx : 0 ≤ φ x - φ z - (inner ℝ p x - inner ℝ p z) := by linarith
  have hgy : 0 ≤ φ y - φ z - (inner ℝ p y - inner ℝ p z) := by linarith
  have hzero : a * (φ x - φ z - (inner ℝ p x - inner ℝ p z)) +
      b * (φ y - φ z - (inner ℝ p y - inner ℝ p z)) = 0 := by
    nlinarith [congrArg (fun t : ℝ => t * φ z) hab,
      congrArg (fun t : ℝ => t * inner ℝ p z) hab]
  have hex : φ x = φ z + inner ℝ p (x - z) := by
    rw [inner_sub_right]
    nlinarith [mul_nonneg hb.le hgy]
  have hey : φ y = φ z + inner ℝ p (y - z) := by
    rw [inner_sub_right]
    nlinarith [mul_nonneg ha.le hgx]
  constructor
  · intro w
    have hw := hs w
    change φ z + inner ℝ p (w - z) ≤ φ w at hw
    rw [hex, inner_sub_right, inner_sub_right]
    rw [inner_sub_right] at hw
    linarith
  · intro w
    have hw := hs w
    change φ z + inner ℝ p (w - z) ≤ φ w at hw
    rw [hey, inner_sub_right, inner_sub_right]
    rw [inner_sub_right] at hw
    linarith

/-- Exact strictness criterion for the moment-source localization step.
Every supporting plane was constructed above; no regularity theorem is
smuggled into the existence of slopes. -/
theorem strictConvexOn_of_subsingleton_contactSet {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    (hcontact : ∀ p : E n, (contactSet φ p).Subsingleton) :
    StrictConvexOn ℝ univ φ := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hle := hc.2 hx hy ha.le hb.le hab
  simp only [smul_eq_mul] at hle ⊢
  apply lt_of_le_of_ne hle
  intro he
  obtain ⟨p, hp⟩ := exists_supportsAt_of_lipschitz_convex hL hc (a • x + b • y)
  obtain ⟨hpx, hpy⟩ := supportsAt_endpoints_of_convex_combination_eq ha hb hab hp he
  exact hxy (hcontact p hpx hpy)

end GaussianTilt.MomentMapRegularity
