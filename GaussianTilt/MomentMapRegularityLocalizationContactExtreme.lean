import GaussianTilt.MomentMapRegularityLocalization
import GaussianTilt.ConvexIntegrability

/-! # Extreme points of all source contact sets

Global exponential integrability yields compact source sublevels. On a
contact set the source potential is affine, so minimizing it gives a compact
exposed face. Krein--Milman then produces an extreme point of the entire
contact set, including for slopes on the target boundary.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Every nonempty contact set has a compact exposed face. This uses source
integrability, not compactness of the possibly boundary-slope contact set. -/
theorem contactSet_has_compact_exposed_face {φ : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ)
    (hi : Integrable (fun x => Real.exp (-φ x))) {p : E n}
    (hn : (contactSet φ p).Nonempty) :
    ∃ F : Set (E n), F.Nonempty ∧ IsCompact F ∧ IsExposed ℝ (contactSet φ p) F := by
  obtain ⟨x, hx⟩ := hn
  have hS : IsCompact (contactSet φ p ∩ {y | φ y ≤ φ x}) :=
    (ConvexIntegrability.convexPotential_compact_sublevel hφ hc hi (φ x)).inter_left
      (isClosed_contactSet hφ p)
  obtain ⟨a, ha, hamin⟩ := hS.exists_isMinOn ⟨x, hx, show φ x ≤ φ x from le_rfl⟩ hφ.continuousOn
  have hmin : ∀ y ∈ contactSet φ p, φ a ≤ φ y := by
    intro y hy
    by_cases hyx : φ y ≤ φ x
    · exact hamin ⟨hy, hyx⟩
    · exact ha.2.trans (le_of_not_ge hyx)
  have hlevel (y : E n) (hy : y ∈ contactSet φ p) :
      φ y - inner ℝ p y = φ a - inner ℝ p a := by
    simpa only [contactSet_eq_level ha.1, mem_setOf_eq] using hy
  have hlin : ∀ y ∈ contactSet φ p, inner ℝ p a ≤ inner ℝ p y := by
    intro y hy
    linarith [hlevel y hy, hmin y hy]
  let F := {y ∈ contactSet φ p | inner ℝ p y = inner ℝ p a}
  have hFn : F.Nonempty := ⟨a, ha.1, rfl⟩
  have hFc : IsClosed F := (isClosed_contactSet hφ p).inter
    (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  have hFsub : F ⊆ {y | φ y ≤ φ a} := by
    intro y hy
    have h := hlevel y hy.1
    rw [hy.2] at h
    dsimp
    linarith
  have hFk : IsCompact F :=
    (ConvexIntegrability.convexPotential_compact_sublevel hφ hc hi (φ a)).of_isClosed_subset hFc hFsub
  refine ⟨F, hFn, hFk, fun _ => ⟨-innerSL ℝ p, ?_⟩⟩
  ext y
  change (y ∈ contactSet φ p ∧ inner ℝ p y = inner ℝ p a) ↔
    y ∈ contactSet φ p ∧ ∀ z ∈ contactSet φ p, -inner ℝ p z ≤ -inner ℝ p y
  constructor
  · rintro ⟨hy, heq⟩
    exact ⟨hy, fun z hz => by rw [heq]; exact neg_le_neg (hlin z hz)⟩
  · rintro ⟨hy, hmax⟩
    refine ⟨hy, le_antisymm ?_ (hlin y hy)⟩
    have h := hmax a ha.1
    linarith

/-- Boundary supporting slopes are included: every nonempty contact set of
an integrable finite convex source has an extreme point. -/
theorem contactSet_extremePoints_nonempty {φ : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ)
    (hi : Integrable (fun x => Real.exp (-φ x))) {p : E n}
    (hn : (contactSet φ p).Nonempty) : ((contactSet φ p).extremePoints ℝ).Nonempty := by
  obtain ⟨F, hFn, hFk, hFe⟩ := contactSet_has_compact_exposed_face hφ hc hi hn
  obtain ⟨x, hx⟩ := hFk.extremePoints_nonempty hFn
  exact ⟨x, hFe.isExtreme.extremePoints_subset_extremePoints hx⟩

end GaussianTilt.MomentMapRegularity
