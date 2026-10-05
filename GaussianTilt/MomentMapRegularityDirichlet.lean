import GaussianTilt.MomentMapRegularityLocalization
import GaussianTilt.MomentMapAlexandrovMaximum

/-! # Literal bounded-domain subgradients for the Dirichlet problem

A function on a bounded convex domain need not have a finite globally convex
extension. We therefore define its supporting slopes using only points in
the domain, and prove compactness of images on interior compact sets and the
actual boundary comparison inclusion in this local-domain formulation.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def SupportsOn (Ω : Set (E n)) (u : E n → ℝ) (p x : E n) : Prop :=
  ∀ y ∈ Ω, u x + inner ℝ p (y - x) ≤ u y

def subgradientImageOn (Ω : Set (E n)) (u : E n → ℝ) (A : Set (E n)) : Set (E n) :=
  {p | ∃ x ∈ A, SupportsOn Ω u p x}

lemma supportsOn_of_supportsAt {Ω : Set (E n)} {u : E n → ℝ} {p x : E n}
    (h : SupportsAt u p x) : SupportsOn Ω u p x := fun y _ => h y

lemma supportsOn_iff_supportsAt_of_mem_interior {Ω : Set (E n)} {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) {p x : E n} (hx : x ∈ interior Ω) :
    SupportsOn Ω u p x ↔ SupportsAt u p x := by
  constructor
  · intro h
    have hm : IsLocalMin (fun y => u y - inner ℝ p y) x := by
      filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
      have hh := h y hy
      rw [inner_sub_right] at hh
      linarith
    have hg := IsMinOn.of_isLocalMin_of_convex_univ hm (alexandrov_convex_tilt hu p)
    intro y
    have hh := hg y
    rw [inner_sub_right]
    linarith
  · exact supportsOn_of_supportsAt

lemma subgradientImageOn_eq_global {Ω A : Set (E n)} {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) (hA : A ⊆ interior Ω) :
    subgradientImageOn Ω u A = subgradientImage u A := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨x, hx, (supportsOn_iff_supportsAt_of_mem_interior hu (hA hx)).mp hp⟩
  · rintro ⟨x, hx, hp⟩
    exact ⟨x, hx, supportsOn_of_supportsAt hp⟩

lemma isClosed_supportsOn_graph {Ω : Set (E n)} {u : E n → ℝ} (hu : Continuous u) :
    IsClosed {z : E n × E n | SupportsOn Ω u z.2 z.1} := by
  simp only [SupportsOn, setOf_forall]
  apply isClosed_iInter
  intro y
  apply isClosed_iInter
  intro _
  exact isClosed_le ((hu.comp continuous_fst).add
    (continuous_snd.inner (continuous_const.sub continuous_fst))) continuous_const

/-- Interior supporting slopes have an explicit oscillation/distance bound;
no global Lipschitz bound on the bounded-domain solution is assumed. -/
lemma supportsOn_norm_bound {Ω : Set (E n)} {u : E n → ℝ} {p x : E n}
    (hp : SupportsOn Ω u p x) {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hb : Metric.closedBall x r ⊆ Ω) (hu : ∀ y ∈ Ω, |u y| ≤ M) : ‖p‖ ≤ 2 * M / r := by
  by_cases hp0 : p = 0
  · rw [hp0, norm_zero]; positivity
  have hpn := norm_pos_iff.mpr hp0
  let y := x + (r / ‖p‖) • p
  have hy : y ∈ Ω := by
    apply hb
    rw [Metric.mem_closedBall, dist_eq_norm]
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hpn)]
    exact le_of_eq (div_mul_cancel₀ r hpn.ne')
  have hx : x ∈ Ω := hb (Metric.mem_closedBall_self hr.le)
  have hh := hp y hy
  have hi : inner ℝ p (y - x) = r * ‖p‖ := by
    dsimp [y]
    rw [add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  rw [hi] at hh
  apply (le_div_iff₀ hr).mpr
  have hx' := (abs_le.mp (hu x hx)).1
  have hy' := (abs_le.mp (hu y hy)).2
  nlinarith

/-- Subgradient images of compact interior sets are compact for a continuous
bounded-domain potential, despite possible unbounded boundary slopes. -/
theorem isCompact_subgradientImageOn {Ω A : Set (E n)} {u : E n → ℝ}
    (hΩ : IsCompact Ω) (hu : Continuous u) (hA : IsCompact A) (hAO : A ⊆ interior Ω) :
    IsCompact (subgradientImageOn Ω u A) := by
  obtain ⟨r, hr, hthick⟩ := hA.exists_cthickening_subset_open isOpen_interior hAO
  obtain ⟨M, hM⟩ := hΩ.exists_bound_of_continuousOn hu.continuousOn
  let B := 2 * max M 0 / r
  have hbound {x p : E n} (hx : x ∈ A) (hp : SupportsOn Ω u p x) : ‖p‖ ≤ B := by
    apply supportsOn_norm_bound hp hr (le_max_right _ _)
      (((Metric.closedBall_subset_cthickening hx r).trans hthick).trans interior_subset)
    intro y hy
    exact (hM y hy).trans (le_max_left _ _)
  let G := (A ×ˢ Metric.closedBall (0 : E n) B) ∩
    {z : E n × E n | SupportsOn Ω u z.2 z.1}
  have hG : IsCompact G := (hA.prod (isCompact_closedBall 0 B)).inter_right (isClosed_supportsOn_graph hu)
  have he : subgradientImageOn Ω u A = Prod.snd '' G := by
    ext p
    constructor
    · rintro ⟨x, hx, hs⟩
      exact ⟨(x, p), ⟨⟨hx, by simpa using hbound hx hs⟩, hs⟩, rfl⟩
    · rintro ⟨⟨x, p⟩, ⟨⟨hx, _⟩, hs⟩, rfl⟩
      exact ⟨x, hx, hs⟩
  rw [he]
  exact hG.image continuous_snd

/-- The literal local-domain version of Alexandrov boundary comparison.
Compact minimization alone supplies the new supporting point; convexity
outside the domain is neither needed nor assumed. -/
theorem subgradientImageOn_strict_sublevel_subset {u v : E n → ℝ}
    {S : Set (E n)} (hS : IsCompact S) (huc : ContinuousOn u S)
    (hb : ∀ y ∈ frontier S, v y ≤ u y) :
    subgradientImageOn S v (interior S ∩ {y | u y < v y}) ⊆
      subgradientImageOn S u (interior S ∩ {y | u y < v y}) := by
  rintro p ⟨x, ⟨hxi, hxuv⟩, hpx⟩
  change u x < v x at hxuv
  let F := fun y => u y - inner ℝ p y
  have hF : ContinuousOn F S := huc.sub ((continuous_const.inner continuous_id).continuousOn)
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn ⟨x, interior_subset hxi⟩ hF
  have hzi : z ∈ interior S := by
    by_contra hzi
    have hzb : z ∈ frontier S := ⟨subset_closure hz, hzi⟩
    have hbound := hb z hzb
    have hsupport := hpx z hz
    have hm := hmin (interior_subset hxi)
    dsimp [F] at hm
    rw [inner_sub_right] at hsupport
    linarith
  have hzuv : u z < v z := by
    have hm := hmin (interior_subset hxi)
    have hs := hpx z hz
    dsimp [F] at hm
    rw [inner_sub_right] at hs
    linarith
  refine ⟨z, ⟨hzi, hzuv⟩, ?_⟩
  intro y hy
  have hm := hmin hy
  dsimp [F] at hm
  rw [inner_sub_right]
  linarith

lemma subgradientImageOn_iUnion (S : Set (E n)) (u : E n → ℝ) {ι : Type*} (A : ι → Set (E n)) :
    subgradientImageOn S u (⋃ i, A i) = ⋃ i, subgradientImageOn S u (A i) := by
  ext p
  simp only [subgradientImageOn, mem_setOf_eq, mem_iUnion, exists_and_left]
  aesop

end GaussianTilt.MomentMapRegularity
