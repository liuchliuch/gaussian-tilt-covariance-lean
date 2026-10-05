import GaussianTilt.MomentMapLinearDirichletHolderLaplace
import GaussianTilt.MomentMapHolderCompactExtension

/-! # Genuine Laplace existence for every datum in the Hölder Banach codomain

The forcing extension is constructed from the actual datum. Consequently
compact global forcing is not an extra hypothesis in the starting inverse.
Boundary C²,α regularity is deliberately not asserted here.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

/-- Every actual Hölder codomain element yields a genuine continuous
zero-boundary C²-interior solution. No global forcing extension or classical
solution is a premise. -/
theorem exists_classicalDirichletLaplaceSolution_holder_banach [NeZero n]
    {S Ω : Set (CoordinateSpace n)} (hSc : IsCompact S) (hΩ : IsOpen Ω)
    (hΩS : Ω ⊆ S)
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (f : Space S ℝ α)
    {w : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w) (hw0 : ∀ x ∈ Ω, w x ≤ 0)
    (hwb : ∀ x ∈ frontier Ω, w x = 0)
    {a : ℝ} (ha : 0 < a) (hwlap : ∀ x ∈ Ω, a ≤ euclideanLaplacian w x) :
    ∃ v : CoordinateSpace n → ℝ, Continuous v ∧ MemLp v 2 volume ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 v x) ∧
      (∀ x, ∀ hx : x ∈ Ω, euclideanLaplacian v x = -value S ℝ α f ⟨x, hΩS hx⟩) ∧
      (∀ x ∉ Ω, v x = 0) := by
  obtain ⟨g, hgc, hgs, hg, hgb, hgh⟩ := exists_compact_holder_extension hSc hα hα1.le f
  obtain ⟨v, hvc, hv2, hvlap, hvout, hvAE⟩ :=
    exists_classicalDirichletLaplaceSolution_holder_data hΩ (hSc.isBounded.subset hΩS)
      i hR hstrip g hgc hgs hα hα1 (by positivity : 0 ≤ 2 * ‖f‖)
      (fun x y => by simpa only [dist_eq_norm] using hgh x y)
      hw hw0 hwb ha (norm_nonneg f) hwlap (fun x _ => hgb x)
  refine ⟨v, hvc, ?_, hv2, ?_, hvout⟩
  · exact (memLp_congr_ae hvAE).mpr (Lp.memLp _)
  · intro x hx
    rw [hvlap x hx, hg ⟨x, hΩS hx⟩]

end GaussianTilt.MomentMapLinearDirichlet
