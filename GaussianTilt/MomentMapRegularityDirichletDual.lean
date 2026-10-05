import GaussianTilt.MomentMapRegularityDirichlet

/-! # The genuine Alexandrov measure on a compact domain

The bounded-domain conjugate is finite and convex on all slope space. Its
proved a.e. differentiability gives a unique contact point for almost every
slope. Thus literal supporting images agree with a genuine pushforward
measure; countable additivity is derived, not assumed.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def domainConjugateValues (S : Set (E n)) (u : E n → ℝ) (p : E n) : Set ℝ :=
  (fun x => inner ℝ p x - u x) '' S

def domainConjugate (S : Set (E n)) (u : E n → ℝ) (p : E n) : ℝ :=
  sSup (domainConjugateValues S u p)

lemma domainConjugateValues_nonempty {S : Set (E n)} (hS : S.Nonempty) (u : E n → ℝ) (p : E n) :
    (domainConjugateValues S u p).Nonempty := hS.image _

lemma domainConjugateValues_bddAbove {S : Set (E n)} (hS : IsCompact S)
    {u : E n → ℝ} (hu : ContinuousOn u S) (p : E n) : BddAbove (domainConjugateValues S u p) :=
  (hS.image_of_continuousOn ((continuous_const.inner continuous_id).continuousOn.sub hu)).bddAbove

lemma domainConjugate_fenchel_le {S : Set (E n)} (hS : IsCompact S)
    {u : E n → ℝ} (hu : ContinuousOn u S) (p : E n) {x : E n} (hx : x ∈ S) :
    inner ℝ p x - u x ≤ domainConjugate S u p :=
  le_csSup (domainConjugateValues_bddAbove hS hu p) ⟨x, hx, rfl⟩

lemma domainConjugate_eq_of_support {S : Set (E n)} {u : E n → ℝ} {p x : E n}
    (hx : x ∈ S) (hp : SupportsOn S u p x) : domainConjugate S u p = inner ℝ p x - u x := by
  have hb : BddAbove (domainConjugateValues S u p) := by
    refine ⟨inner ℝ p x - u x, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h := hp y hy
    rw [inner_sub_right] at h
    linarith
  apply le_antisymm
  · apply csSup_le (domainConjugateValues_nonempty ⟨x, hx⟩ _ _)
    rintro _ ⟨y, hy, rfl⟩
    have h := hp y hy
    rw [inner_sub_right] at h
    linarith
  · exact le_csSup hb ⟨x, hx, rfl⟩

lemma domainConjugate_convex {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {u : E n → ℝ} (hu : ContinuousOn u S) : ConvexOn ℝ univ (domainConjugate S u) := by
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ a b ha hb hab
  apply csSup_le (domainConjugateValues_nonempty hSn _ _)
  rintro _ ⟨x, hx, rfl⟩
  have hp := mul_le_mul_of_nonneg_left (domainConjugate_fenchel_le hS hu p hx) ha
  have hq := mul_le_mul_of_nonneg_left (domainConjugate_fenchel_le hS hu q hx) hb
  have hsum : a * u x + b * u x = u x := by rw [← add_mul, hab, one_mul]
  simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
  nlinarith

lemma exists_supportsOn_compact {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {u : E n → ℝ} (hu : ContinuousOn u S) (p : E n) : ∃ x ∈ S, SupportsOn S u p x := by
  have hF : ContinuousOn (fun y => u y - inner ℝ p y) S :=
    hu.sub ((continuous_const.inner continuous_id : Continuous (fun y : E n => inner ℝ p y)).continuousOn)
  obtain ⟨x, hx, hm⟩ := hS.exists_isMinOn hSn hF
  refine ⟨x, hx, fun y hy => ?_⟩
  have h : u x - inner ℝ p x ≤ u y - inner ℝ p y := hm hy
  rw [inner_sub_right]
  linarith

lemma domainConjugate_gradient_eq_of_support {S : Set (E n)} (hS : IsCompact S)
    {u : E n → ℝ} (hu : ContinuousOn u S) {p x : E n}
    (hd : DifferentiableAt ℝ (domainConjugate S u) p) (hx : x ∈ S) (hp : SupportsOn S u p x) :
    gradient (domainConjugate S u) p = x := by
  apply supporting_vector_eq_gradient hd
  intro q
  rw [domainConjugate_eq_of_support hx hp, inner_sub_right]
  have hf := domainConjugate_fenchel_le hS hu q hx
  linarith [real_inner_comm x q, real_inner_comm x p]

/-- The actual dual gradient is the unique bounded-domain contact point at
almost every slope, for every continuous function on a compact domain. -/
theorem domainConjugate_ae_unique_contact {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {u : E n → ℝ} (hu : ContinuousOn u S) :
    ∀ᵐ p ∂volume, gradient (domainConjugate S u) p ∈ S ∧
      SupportsOn S u p (gradient (domainConjugate S u) p) ∧
      ∀ x ∈ S, SupportsOn S u p x → x = gradient (domainConjugate S u) p := by
  filter_upwards [MomentMapCoercivity.convex_ae_differentiable (domainConjugate_convex hS hSn hu)]
    with p hp
  obtain ⟨x, hx, hpx⟩ := exists_supportsOn_compact hS hSn hu p
  have he := domainConjugate_gradient_eq_of_support hS hu hp hx hpx
  refine ⟨he ▸ hx, he ▸ hpx, ?_⟩
  intro y hy hpy
  exact (domainConjugate_gradient_eq_of_support hS hu hp hy hpy).symm

/-- A genuine measure on source space, constructed from the a.e. unique
contact point rather than defined by an unproved countably-additive formula. -/
def alexandrovMeasureOn (S : Set (E n)) (u : E n → ℝ) : Measure (E n) :=
  volume.map (gradient (domainConjugate S u))

lemma subgradientImageOn_ae_eq_contact_preimage {S A : Set (E n)}
    (hS : IsCompact S) (hSn : S.Nonempty) {u : E n → ℝ} (hu : ContinuousOn u S)
    (hA : A ⊆ S) :
    subgradientImageOn S u A =ᵐ[volume] gradient (domainConjugate S u) ⁻¹' A := by
  filter_upwards [domainConjugate_ae_unique_contact hS hSn hu] with p hp
  apply propext
  constructor
  · rintro ⟨x, hx, hpx⟩
    change gradient (domainConjugate S u) p ∈ A
    rwa [← hp.2.2 x (hA hx) hpx]
  · intro hpa
    exact ⟨gradient (domainConjugate S u) p, hpa, hp.2.1⟩

/-- Literal bounded-domain image volume equals the constructed Alexandrov
measure on every measurable source set. -/
theorem alexandrovMeasureOn_apply {S A : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {u : E n → ℝ} (hu : ContinuousOn u S) (hA : MeasurableSet A) (hAS : A ⊆ S) :
    alexandrovMeasureOn S u A = volume (subgradientImageOn S u A) := by
  have hg : Measurable (gradient (domainConjugate S u)) :=
    (InnerProductSpace.toDual ℝ (E n)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ (domainConjugate S u))
  rw [alexandrovMeasureOn, Measure.map_apply hg hA]
  exact (measure_congr (subgradientImageOn_ae_eq_contact_preimage hS hSn hu hAS)).symm

end GaussianTilt.MomentMapRegularity
