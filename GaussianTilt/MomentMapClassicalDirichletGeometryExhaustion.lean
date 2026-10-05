import GaussianTilt.MomentMapClassicalDirichletGeometryDomains

/-! # Nested smooth strongly convex exhaustion of a convex interior -/
noncomputable section
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- A genuine nested exhaustion by the constructed smooth strongly convex
sublevel domains. Every compact subset is eventually contained in them. -/
theorem exists_smoothInnerDomain_exhaustion {S : Set (E n)}
    (hS : IsCompact S) (hc : Convex ℝ S) (hSi : (interior S).Nonempty) :
    ∃ d : ℕ → SmoothInnerDomain S ∅,
      (∀ k, (d k).body ⊆ (d (k+1)).domain) ∧
      (⋃ k, (d k).domain) = interior S ∧
      (∀ A, IsCompact A → A ⊆ interior S → ∀ᶠ k in atTop, A ⊆ (d k).domain) := by
  letI : LocallyCompactSpace (interior S) := isOpen_interior.locallyCompactSpace
  let K := fun k => Subtype.val '' compactCovering (interior S) k
  have hK (k : ℕ) : IsCompact (K k) :=
    (isCompact_compactCovering (interior S) k).image continuous_subtype_val
  have hKS (k : ℕ) : K k ⊆ interior S := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hKU : (⋃ k, K k) = interior S := by
    apply Subset.antisymm (iUnion_subset hKS)
    intro x hx
    have hh : (⟨x, hx⟩ : interior S) ∈ ⋃ k, compactCovering (interior S) k := by
      rw [iUnion_compactCovering]
      exact mem_univ _
    obtain ⟨k, hk⟩ := mem_iUnion.mp hh
    exact mem_iUnion.mpr ⟨k, ⟨⟨x,hx⟩, hk, rfl⟩⟩
  let chooseD : ∀ A : Set (E n), IsCompact A → A ⊆ interior S → SmoothInnerDomain S A :=
    fun A hA hAS => Classical.choice (exists_smoothInnerDomain hS hc hSi hA hAS)
  let forget : ∀ {A : Set (E n)}, SmoothInnerDomain S A → SmoothInnerDomain S ∅ :=
    fun d => { d with contains := empty_subset _ }
  let d : ℕ → SmoothInnerDomain S ∅ :=
    Nat.rec (forget (chooseD (K 0) (hK 0) (hKS 0)))
      (fun k old => forget (chooseD (old.body ∪ K (k+1))
        (old.compact_sublevel.union (hK (k+1)))
        (union_subset old.sublevel_inside (hKS (k+1)))))
  have hcontains (k : ℕ) : K k ⊆ (d k).domain := by
    cases k with
    | zero => exact (chooseD (K 0) (hK 0) (hKS 0)).contains
    | succ k => exact fun x hx => (chooseD ((d k).body ∪ K (k+1))
        ((d k).compact_sublevel.union (hK (k+1)))
        (union_subset (d k).sublevel_inside (hKS (k+1)))).contains (Or.inr hx)
  have hnest (k : ℕ) : (d k).body ⊆ (d (k+1)).domain :=
    fun x hx => (chooseD ((d k).body ∪ K (k+1))
      ((d k).compact_sublevel.union (hK (k+1)))
      (union_subset (d k).sublevel_inside (hKS (k+1)))).contains (Or.inl hx)
  have hU : (⋃ k, (d k).domain) = interior S := by
    apply Subset.antisymm
    · refine iUnion_subset (fun k => ?_)
      exact (fun x hx => (d k).sublevel_inside (show (d k).defining x ≤ 0 from le_of_lt hx))
    · rw [← hKU]
      exact iUnion_mono hcontains
  have hmono : Monotone (fun k => (d k).domain) := monotone_nat_of_le_succ (fun k =>
    (show (d k).domain ⊆ (d k).body from fun x hx => show (d k).defining x ≤ 0 from le_of_lt hx).trans (hnest k))
  refine ⟨d, hnest, hU, ?_⟩
  intro A hA hAS
  have hcover : A ⊆ ⋃ k, (d k).domain := by rwa [hU]
  obtain ⟨k, hk⟩ := hA.elim_finite_subcover (fun k => (d k).domain)
    (fun k => (d k).isOpen_domain) hcover
  -- A finite subcover of a monotone family is contained in one member.
  let N := k.sup id
  filter_upwards [eventually_ge_atTop N] with m hm
  intro x hx
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hk hx)
  exact hmono ((Finset.le_sup (f:=id) hj).trans hm) hxj

end GaussianTilt.MomentMapRegularity
