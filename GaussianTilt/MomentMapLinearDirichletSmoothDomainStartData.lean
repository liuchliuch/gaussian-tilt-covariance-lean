import GaussianTilt.MomentMapLinearDirichletSmoothDomainStartGeometry
import GaussianTilt.MomentMapHolderCompactExtension

/-! # Genuine signed weak/classical starting data on the actual smooth domain

The original H₀¹ value/gradient jet is retained together with the continuous
classical representative and its literal almost-everywhere identification.
No boundary derivative regularity is included in this starting package.
-/
noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ContDiff ENNReal BoundedContinuousFunction
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.HolderSpace
variable {n : ℕ}

structure SmoothDomainLaplaceStartData {S A : Set (E n)} (d : SmoothInnerDomain S A)
    (α : ℝ) (f : Space {y | d.coordinateDefining y ≤ 0} ℝ α) where
  forcing : CoordinateSpace n → ℝ
  forcing_continuous : Continuous forcing
  forcing_compact : HasCompactSupport forcing
  forcing_on_body : ∀ x : {y | d.coordinateDefining y ≤ 0},
    forcing x = -value {y | d.coordinateDefining y ≤ 0} ℝ α f x
  forcing_bound : ∀ x, |forcing x| ≤ ‖f‖
  forcing_holder : ∀ x y, |forcing x-forcing y| ≤ (2*‖f‖)*‖x-y‖^α
  source : Lp ℝ 2 (volume : Measure (CoordinateSpace n))
  source_ae : source =ᵐ[volume] forcing
  weakSolution : dirichletSobolev {y | d.coordinateDefining y<0}
  weak_equation : ∀ w : dirichletSobolev {y | d.coordinateDefining y<0},
    dirichletEnergy {y | d.coordinateDefining y<0} weakSolution w =
      inner ℝ source (dirichletValue {y | d.coordinateDefining y<0} w)
  representative : CoordinateSpace n → ℝ
  representative_continuous : Continuous representative
  representative_memLp : MemLp representative 2 volume
  representative_ae : representative =ᵐ[volume] weakSolution.1 0
  representative_interior : ∀ x, d.coordinateDefining x<0 → ContDiffAt ℝ 2 representative x
  representative_equation : ∀ x, d.coordinateDefining x<0 →
    euclideanLaplacian representative x = -forcing x
  representative_zero : ∀ x, ¬d.coordinateDefining x<0 → representative x=0

/-- Every raw Hölder datum constructs both the actual Sobolev solution and
its common continuous/classical representative, with the sign required by
the positive Laplacian Banach-space starting operator. -/
theorem exists_smoothDomain_laplace_start_data [NeZero n]
    {S A : Set (E n)} (d : SmoothInnerDomain S A)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (f : Space {y | d.coordinateDefining y ≤ 0} ℝ α) :
    Nonempty (SmoothDomainLaplaceStartData d α f) := by
  obtain ⟨i,R,a,hR,ha,hstrip,hbarrier,hzero⟩ := exists_smoothDomain_laplace_start_geometry d
  obtain ⟨g,hgc,hgs,hge,hgb,hgh⟩ := exists_compact_holder_extension d.coordinate_body_compact hα hα1.le (-f)
  have hgbody : ∀ x : {y | d.coordinateDefining y ≤ 0},
      g x = -value {y | d.coordinateDefining y ≤ 0} ℝ α f x := by
    intro x
    rw [hge x]
    simp only [map_neg,BoundedContinuousFunction.neg_apply]
  have hgB : ∀ x, |g x| ≤ ‖f‖ := by simpa only [norm_neg] using hgb
  have hgH : ∀ x y, |g x-g y| ≤ (2*‖f‖)*‖x-y‖^α := by
    simpa only [norm_neg,dist_eq_norm] using hgh
  have hgLp := hgc.memLp_of_hasCompactSupport hgs (p := 2) (μ := (volume : Measure (CoordinateSpace n)))
  let gL := hgLp.toLp g
  let u := weakDirichletLaplaceSolution i hR hstrip gL
  have hΩ : IsOpen {y | d.coordinateDefining y<0} := isOpen_lt d.coordinateDefining_smooth.continuous continuous_const
  have hΩb : Bornology.IsBounded {y | d.coordinateDefining y<0} :=
    d.coordinate_body_compact.isBounded.subset (fun x (hx : d.coordinateDefining x<0) => show d.coordinateDefining x≤0 from hx.le)
  obtain ⟨v,hvc,hvi,hve,hvzero,hvAE⟩ := exists_classicalDirichletLaplaceSolution_holder_data
    hΩ hΩb i hR hstrip g hgc hgs hα hα1 (by positivity : 0 ≤ 2*‖f‖) hgH
    d.coordinateDefining_smooth (fun x hx => hx.le) hzero ha (norm_nonneg f)
    (fun x _ => hbarrier x) (fun x _ => hgB x)
  have hvu : v =ᵐ[volume] u.1 0 := hvAE
  refine ⟨{
    forcing := g
    forcing_continuous := hgc
    forcing_compact := hgs
    forcing_on_body := hgbody
    forcing_bound := hgB
    forcing_holder := hgH
    source := gL
    source_ae := hgLp.coeFn_toLp
    weakSolution := u
    weak_equation := fun w => weakDirichletLaplaceSolution_equation i hR hstrip gL w
    representative := v
    representative_continuous := hvc
    representative_memLp := (memLp_congr_ae hvu).mpr (Lp.memLp (u.1 0))
    representative_ae := hvu
    representative_interior := hvi
    representative_equation := hve
    representative_zero := hvzero }⟩

namespace SmoothDomainLaplaceStartData
variable {S A : Set (E n)} {d : SmoothInnerDomain S A} {α : ℝ}
  {f : Space {y | d.coordinateDefining y ≤ 0} ℝ α}

lemma positive_datum_equation (data : SmoothDomainLaplaceStartData d α f)
    (x : CoordinateSpace n) (hx : d.coordinateDefining x<0) :
    euclideanLaplacian data.representative x = value {y | d.coordinateDefining y ≤ 0} ℝ α f ⟨x,hx.le⟩ := by
  rw [data.representative_equation x hx,data.forcing_on_body ⟨x,hx.le⟩,neg_neg]

lemma representative_zero_frontier (data : SmoothDomainLaplaceStartData d α f)
    (x : CoordinateSpace n) (hx : x ∈ frontier {y | d.coordinateDefining y≤0}) :
    data.representative x=0 := by
  apply data.representative_zero
  rw [d.coordinate_zero_boundary x hx]
  exact lt_irrefl 0

end SmoothDomainLaplaceStartData
end GaussianTilt.MomentMapLinearDirichlet
