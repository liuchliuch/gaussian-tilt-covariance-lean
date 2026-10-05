import GaussianTilt.MomentMapClassicalDirichletFixedHolderNorm
import GaussianTilt.MomentMapClassicalDirichletHomotopyJets
import GaussianTilt.MomentMapClassicalDirichletReferenceConversion

/-! # Actual nonlinear continuation reduced to the precise linear inverse

Every nonlinear estimate, initial solution, compactness and connectedness
step is proved. This theorem leaves only bijectivity of the literal Banach
derivative as the explicit linear Dirichlet input; it does not claim that
linear solvability has already been established.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

theorem exists_classical_unit_dirichlet_of_linearized_bijective [NeZero n]
    (hlinear : ∀ (α : ℝ), 0 < α → α < 1 → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      (∀ x ∈ {y | d.coordinateDefining y ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 x).PosDef) →
      (∀ x ∈ {y | d.coordinateDefining y ≤ 0},
        (intrinsicHessian d.coordinate_body_convex α j.1 x).det = dirichletContinuationDensity d.coordinateDefining t x) →
      Function.Bijective (fderiv ℝ (dirichletMongeAmpere d.coordinate_body_convex α 0) j)) :
    ∃ u : E n → ℝ, Continuous u ∧ ContDiffOn ℝ ∞ u (interior d.body) ∧
      ConvexOn ℝ d.body u ∧ (∀ x ∈ frontier d.body, u x=0) ∧
      (∀ x ∈ interior d.body, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef) ∧
      (∀ x ∈ interior d.body, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det=1) := by
  obtain ⟨α,B,hα,hα1,hB,hbound⟩ := d.intrinsic_dirichletContinuation_uniform_holder_jet_norm
  obtain ⟨j₀,F,hF,hvalue,hpd₀,hMA₀,hFvalue⟩ := d.exists_intrinsic_dirichlet_homotopy hα.le hα1.le
  have hpraw (j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α)
      (hp : ∀ x : {y | d.coordinateDefining y ≤ 0}, (hessianMatrix d.coordinate_body_convex α j.1 x).PosDef) :
      ∀ x ∈ {y | d.coordinateDefining y ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 x).PosDef := by
    intro x hx
    rw [intrinsicHessian_eq_stored d.coordinate_body_convex α j.1 ⟨x,hx⟩]
    exact hp ⟨x,hx⟩
  have hraw (t : ℝ) (j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α)
      (he : mongeAmpere d.coordinate_body_convex α j.1 = F t) :
      ∀ x ∈ {y | d.coordinateDefining y ≤ 0},
        (intrinsicHessian d.coordinate_body_convex α j.1 x).det = dirichletContinuationDensity d.coordinateDefining t x := by
    intro x hx
    have hh := congrArg (fun f : Space {y | d.coordinateDefining y ≤ 0} ℝ α =>
      value {y | d.coordinateDefining y ≤ 0} ℝ α f ⟨x,hx⟩) he
    dsimp only at hh
    rw [value_mongeAmpere,hFvalue] at hh
    rw [intrinsicHessian_eq_stored d.coordinate_body_convex α j.1 ⟨x,hx⟩]
    exact hh
  obtain ⟨j,hpd,hMA⟩ := holder_dirichlet_continuation d.coordinate_body_convex d.coordinate_body_compact
    d.coordinate_body_interior_nonempty hα hB F hF.continuous
    (fun t ht x => by rw [hFvalue]; exact dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef x))
    j₀ hpd₀ hMA₀
    (fun t ht j hp he => hlinear α hα hα1 t ht j (hpraw j hp) (hraw t j he))
    (fun t ht j hp he => hbound t ht j (hpraw j hp) (hraw t j he))
  apply d.classical_unit_dirichlet_of_positive_holder_jet hα hα1 j (hpraw j hpd)
  intro x hx
  simpa only [dirichletContinuationDensity,sub_self,zero_mul,add_zero,zero_add] using hraw 1 j hMA x hx

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
