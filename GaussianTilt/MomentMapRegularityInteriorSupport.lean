import GaussianTilt.MomentMapRegularityLocalizationStrictness

/-!
# The differentiability endpoint for literal supporting planes

These finite-dimensional convex-analytic lemmas prove upper semicontinuity
of the actual support graph at singleton fibers, differentiability from
singleton fibers, and continuous differentiability from differentiability
everywhere. They are endpoint tools for interior Monge--Ampère regularity;
they do not assert that Alexandrov density bounds imply singleton fibers.
-/
noncomputable section
open MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- The error above one supporting plane is controlled by the difference
between supporting slopes at the two endpoints. -/
lemma supportsAt_remainder_bound {φ : E n → ℝ} {x y p q : E n}
    (hp : SupportsAt φ p x) (hq : SupportsAt φ q y) :
    |φ y - φ x - inner ℝ p (y - x)| ≤ ‖q - p‖ * ‖y - x‖ := by
  have hlo := hp y
  have hhi := hq x
  have he : inner ℝ q (x - y) = -inner ℝ q (y - x) := by
    rw [← inner_neg_right, neg_sub]
  rw [he] at hhi
  rw [abs_of_nonneg (by linarith)]
  calc
    _ ≤ inner ℝ (q - p) (y - x) := by rw [inner_sub_left]; linarith
    _ ≤ ‖q - p‖ * ‖y - x‖ := real_inner_le_norm _ _

/-- The complete support graph is upper semicontinuous: any open set
containing the whole support fiber at one point contains every nearby fiber.
This statement also applies before singleton fibers have been established. -/
theorem eventually_supportsAt_mem_open {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) {x : E n} {U : Set (E n)} (hU : IsOpen U)
    (hall : ∀ q, SupportsAt φ q x → q ∈ U) :
    ∀ᶠ y in 𝓝 x, ∀ q, SupportsAt φ q y → q ∈ U := by
  let G := ((Metric.closedBall x 1 ×ˢ Metric.closedBall (0 : E n) (L : ℝ)) ∩
    {z : E n × E n | SupportsAt φ z.2 z.1}) ∩ (Prod.snd ⁻¹' Uᶜ)
  have hG : IsCompact G :=
    (((isCompact_closedBall x 1).prod (isCompact_closedBall 0 (L : ℝ))).inter_right
      (isClosed_supportsAt_graph hL.continuous)).inter_right
      (hU.isClosed_compl.preimage continuous_snd)
  have hx : x ∉ Prod.fst '' G := by
    rintro ⟨⟨y, q⟩, ⟨⟨_, hq⟩, hqU⟩, he⟩
    change y = x at he
    subst y
    exact hqU (hall q hq)
  have hne : (Prod.fst '' G)ᶜ ∈ 𝓝 x := (hG.image continuous_fst).isClosed.isOpen_compl.mem_nhds hx
  filter_upwards [hne, Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy hyb q hq
  by_contra hqU
  apply hy
  refine ⟨(y, q), ⟨⟨⟨Metric.ball_subset_closedBall hyb, ?_⟩, hq⟩, hqU⟩, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using supportsAt_norm_le hL hq

/-- At a singleton support fiber, every nearby supporting slope is close
to the unique slope. Compactness is supplied by the given Lipschitz bound;
no differentiability or gradient continuity is assumed. -/
theorem eventually_supportsAt_near_of_unique {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) {x p : E n}
    (hunique : ∀ q, SupportsAt φ q x → q = p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ∀ q, SupportsAt φ q y → ‖q - p‖ < ε := by
  let G := ((Metric.closedBall x 1 ×ˢ Metric.closedBall (0 : E n) (L : ℝ)) ∩
    {z : E n × E n | SupportsAt φ z.2 z.1}) ∩
    {z : E n × E n | ε ≤ ‖z.2 - p‖}
  have hG : IsCompact G :=
    (((isCompact_closedBall x 1).prod (isCompact_closedBall 0 (L : ℝ))).inter_right
      (isClosed_supportsAt_graph hL.continuous)).inter_right
      (isClosed_le continuous_const ((continuous_snd.sub continuous_const).norm))
  have hx : x ∉ Prod.fst '' G := by
    rintro ⟨⟨y, q⟩, ⟨⟨_, hq⟩, hqe⟩, he⟩
    change y = x at he
    subst y
    change ε ≤ ‖q - p‖ at hqe
    rw [hunique q hq, sub_self, norm_zero] at hqe
    exact (not_le_of_gt hε) hqe
  have hne : (Prod.fst '' G)ᶜ ∈ 𝓝 x := (hG.image continuous_fst).isClosed.isOpen_compl.mem_nhds hx
  filter_upwards [hne, Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy hyb q hq
  by_contra hfar
  apply hy
  refine ⟨(y, q), ⟨⟨⟨Metric.ball_subset_closedBall hyb, ?_⟩, hq⟩,
    le_of_not_gt hfar⟩, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using supportsAt_norm_le hL hq

/-- A unique literal supporting slope is the genuine Fréchet derivative.
The proof sandwiches the remainder between the two supporting planes and
uses the compact support graph from the preceding theorem. -/
theorem hasFDerivAt_of_unique_support {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ) {x p : E n}
    (hp : SupportsAt φ p x) (hunique : ∀ q, SupportsAt φ q x → q = p) :
    HasFDerivAt φ (innerSL ℝ p) x := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hnear := eventually_supportsAt_near_of_unique hL hunique hε
  have ht : Tendsto (fun h : E n => x + h) (𝓝 0) (𝓝 x) := by
    simpa using continuous_const.add continuous_id |>.tendsto (0 : E n)
  filter_upwards [ht.eventually hnear] with h hh
  obtain ⟨q, hq⟩ := exists_supportsAt_of_lipschitz_convex hL hc (x + h)
  have hb := supportsAt_remainder_bound hp hq
  simp only [add_sub_cancel_left] at hb
  change ‖φ (x + h) - φ x - inner ℝ p h‖ ≤ ε * ‖h‖
  rw [Real.norm_eq_abs]
  exact hb.trans (mul_le_mul_of_nonneg_right (hh q hq).le (norm_nonneg h))

/-- Differentiability and the singleton-support property are equivalent for
finite globally Lipschitz convex functions. -/
theorem differentiableAt_iff_unique_support {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ) (x : E n) :
    DifferentiableAt ℝ φ x ↔ ∃ p, SupportsAt φ p x ∧
      ∀ q, SupportsAt φ q x → q = p := by
  constructor
  · intro hd
    refine ⟨gradient φ x, supportsAt_gradient hc hd, ?_⟩
    intro q hq
    exact (supporting_vector_eq_gradient hd hq).symm
  · rintro ⟨p, hp, huniq⟩
    exact (hasFDerivAt_of_unique_support hL hc hp huniq).differentiableAt

/-- Everywhere differentiable finite convex functions with a global
Lipschitz bound have continuous gradients, proved from their support graph. -/
theorem continuous_gradient_of_lipschitz_convex_differentiable
    {φ : E n → ℝ} {L : ℝ≥0} (hL : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ) :
    Continuous (gradient φ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_supportsAt_near_of_unique hL
    (fun q hq => (supporting_vector_eq_gradient (hd x) hq).symm) hε] with y hy
  simpa only [dist_eq_norm] using hy (gradient φ y) (supportsAt_gradient hc (hd y))

/-- The actual C¹ endpoint: in this convex setting, an everywhere
Fréchet-differentiability proof already gives continuous differentiability. -/
theorem contDiff_one_of_lipschitz_convex_differentiable
    {φ : E n → ℝ} {L : ℝ≥0} (hL : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ) :
    ContDiff ℝ 1 φ := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x => (InnerProductSpace.toDual ℝ (E n)) (gradient φ x), ?_, ?_⟩
  · exact (InnerProductSpace.toDual ℝ (E n)).continuous.comp
      (continuous_gradient_of_lipschitz_convex_differentiable hL hc hd)
  · intro x
    exact (hd x).hasGradientAt.hasFDerivAt

/-- Singleton support fibers everywhere imply C¹, with no continuity
assumption on a chosen slope field. -/
theorem contDiff_one_of_unique_supports {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    (hunique : ∀ x, ∃ p, SupportsAt φ p x ∧ ∀ q, SupportsAt φ q x → q = p) :
    ContDiff ℝ 1 φ := by
  apply contDiff_one_of_lipschitz_convex_differentiable hL hc
  intro x
  exact (differentiableAt_iff_unique_support hL hc x).mpr (hunique x)

end GaussianTilt.MomentMapRegularity
