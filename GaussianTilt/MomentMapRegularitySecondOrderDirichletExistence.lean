import GaussianTilt.MomentMapRegularitySecondOrderDirichletExistenceLimit
import GaussianTilt.MomentMapRegularityDirichletAtomicLaw

/-!
# The constructed unit-density Alexandrov Dirichlet solution

Finite atomic cell-height minimization is combined with actual interior
atomization, the boundary maximum principle, Arzelà--Ascoli and proved weak
continuity. No Dirichlet-solvability premise or classical regularity is used.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Every compact convex full-dimensional domain admits an actual
continuous convex unit-density Alexandrov solution with zero boundary
values. The representative is globally continuous by explicit zero extension;
its convexity and subgradient relation are asserted on the actual domain. -/
theorem exists_unit_density_alexandrov_dirichlet [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) (hSc : Convex ℝ S) (hi : (interior S).Nonempty) :
    ∃ u : E n → ℝ, Continuous u ∧ ConvexOn ℝ S u ∧
      (∀ x ∈ frontier S, u x = 0) ∧
      ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
        volume (subgradientImageOn S u A) = volume A := by
  classical
  obtain ⟨ms, hweak, hmass, hatoms⟩ := exists_unit_density_interior_atomizations hS hSc hi
  have hex (k : ℕ) : ∃ u : E n → ℝ, ContinuousOn u S ∧ ConvexOn ℝ S u ∧
      (∀ x ∈ frontier S, u x = 0) ∧
      ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
        volume (subgradientImageOn S u A) = (ms k : Measure (E n)) A := by
    obtain ⟨F, m, hF, hFm, hmeq⟩ := hatoms k
    letI : Nonempty {p // p ∈ F} := hF.to_subtype
    obtain ⟨u, huc, hu, hub, husol⟩ := exists_atomic_dirichlet_solution hS hSc
      (fun p : {p // p ∈ F} => p.val) Subtype.val_injective
      (fun p => (hFm p p.property).1) (fun p => m p) (fun p => (hFm p p.property).2)
    have hatomic : atomicMeasure (fun p : {p // p ∈ F} => p.val) (fun p => m p) =
        (ms k : Measure (E n)) := by
      rw [hmeq]
      simpa only [atomicMeasure] using Finset.sum_attach F
        (fun p => ENNReal.ofReal (m p) • Measure.dirac p)
    refine ⟨u, huc.continuousOn, hu.subset (subset_univ _) hSc, hub, ?_⟩
    intro A hA hAS
    rw [← hatomic]
    exact husol A hA.measurableSet hAS
  choose v hvc hv hb hsol using hex
  have hSn : S.Nonempty := hi.mono interior_subset
  have hmass' : ∀ k, (ms k : Measure (E n)) univ =
      (compactDomainVolume S hS : Measure (E n)) univ := by
    simpa only [compactDomainVolume, FiniteMeasure.toMeasure, Measure.restrict_apply_univ] using hmass
  obtain ⟨u, huc, hu, hub, husol⟩ := exists_dirichlet_limit_of_weakly_convergent_solutions
    hS hSn hv hvc hb hweak hmass' hsol
  refine ⟨u, huc, hu, hub, ?_⟩
  intro A hA hAS
  rw [husol A hA hAS]
  change (volume.restrict S) A = volume A
  rw [Measure.restrict_apply hA.measurableSet, inter_eq_left.mpr (hAS.trans interior_subset)]

end GaussianTilt.MomentMapRegularity
