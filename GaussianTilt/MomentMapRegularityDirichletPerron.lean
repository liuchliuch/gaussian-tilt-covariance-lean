import GaussianTilt.MomentMapRegularityDirichletDual
import GaussianTilt.MomentMapRegularityDirichletComparison

/-! # Genuine lattice properties for the Alexandrov Perron construction

Taking the maximum preserves the lower Alexandrov mass constraint. The
proof splits the source into the two active sets and uses the constructed
Alexandrov measure's actual additivity, not a presumed mass formula.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma supportsOn_max_of_left {S : Set (E n)} {u v : E n → ℝ} {p x : E n}
    (hs : SupportsOn S u p x) (hx : v x ≤ u x) : SupportsOn S (fun y => max (u y) (v y)) p x := by
  intro y hy
  change max (u x) (v x) + inner ℝ p (y - x) ≤ max (u y) (v y)
  rw [max_eq_left hx]
  exact (hs y hy).trans (le_max_left _ _)

lemma subgradientImageOn_subset_max_of_left {S A : Set (E n)} {u v : E n → ℝ}
    (ha : ∀ x ∈ A, v x ≤ u x) :
    subgradientImageOn S u A ⊆ subgradientImageOn S (fun y => max (u y) (v y)) A := by
  rintro p ⟨x, hx, hs⟩
  exact ⟨x, hx, supportsOn_max_of_left hs (ha x hx)⟩

lemma alexandrovMeasureOn_le_max_on_active {S A : Set (E n)} (hS : IsCompact S)
    (hSn : S.Nonempty) {u v : E n → ℝ} (hu : ContinuousOn u S) (hv : ContinuousOn v S)
    (hA : MeasurableSet A) (hAS : A ⊆ S) (ha : ∀ x ∈ A, v x ≤ u x) :
    alexandrovMeasureOn S u A ≤ alexandrovMeasureOn S (fun y => max (u y) (v y)) A := by
  rw [alexandrovMeasureOn_apply hS hSn hu hA hAS,
    alexandrovMeasureOn_apply hS hSn (hu.sup hv) hA hAS]
  exact measure_mono (subgradientImageOn_subset_max_of_left ha)

/-- The lower Monge--Ampère measure constraint used for Perron subsolutions.
It is stated for the genuinely constructed bounded-domain measure. -/
def AlexandrovLowerBoundOn (S : Set (E n)) (u : E n → ℝ) (μ : Measure (E n)) : Prop :=
  ∀ A : Set (E n), MeasurableSet A → A ⊆ interior S → μ A ≤ alexandrovMeasureOn S u A

/-- Closure under maximum is proved by active-set decomposition. This is
valid for arbitrary measures on the right, not only unit Lebesgue density. -/
theorem alexandrovLowerBoundOn_max {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {u v : E n → ℝ} (hu : Continuous u) (hv : Continuous v) {μ : Measure (E n)}
    (hulo : AlexandrovLowerBoundOn S u μ) (hvlo : AlexandrovLowerBoundOn S v μ) :
    AlexandrovLowerBoundOn S (fun y => max (u y) (v y)) μ := by
  intro A hA hAS
  let U := A ∩ {x | v x ≤ u x}
  let V := A ∩ {x | u x < v x}
  have hU : MeasurableSet U := hA.inter (isClosed_le hv hu).measurableSet
  have hV : MeasurableSet V := hA.inter (isOpen_lt hu hv).measurableSet
  have hdisj : Disjoint U V := by
    apply disjoint_left.mpr
    intro x hxU hxV
    exact (show u x < v x from hxV.2).not_ge (show v x ≤ u x from hxU.2)
  have he : U ∪ V = A := by
    ext x
    change ((x ∈ A ∧ v x ≤ u x) ∨ (x ∈ A ∧ u x < v x)) ↔ x ∈ A
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      rcases le_or_gt (v x) (u x) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hUS : U ⊆ S := inter_subset_left.trans (hAS.trans interior_subset)
  have hVS : V ⊆ S := inter_subset_left.trans (hAS.trans interior_subset)
  have hleft := alexandrovMeasureOn_le_max_on_active hS hSn hu.continuousOn hv.continuousOn
    hU hUS (fun x hx => hx.2)
  have hright := alexandrovMeasureOn_le_max_on_active hS hSn hv.continuousOn hu.continuousOn
    hV hVS (fun x hx => hx.2.le)
  have hright' : alexandrovMeasureOn S v V ≤ alexandrovMeasureOn S (fun y => max (u y) (v y)) V := by
    simpa only [max_comm] using hright
  calc
    μ A = μ U + μ V := by rw [← he, measure_union hdisj hV]
    _ ≤ alexandrovMeasureOn S u U + alexandrovMeasureOn S v V :=
      add_le_add (hulo U hU (inter_subset_left.trans hAS)) (hvlo V hV (inter_subset_left.trans hAS))
    _ ≤ alexandrovMeasureOn S (fun y => max (u y) (v y)) U +
        alexandrovMeasureOn S (fun y => max (u y) (v y)) V := add_le_add hleft hright'
    _ = alexandrovMeasureOn S (fun y => max (u y) (v y)) A := by rw [← measure_union hdisj hV, he]

end GaussianTilt.MomentMapRegularity
