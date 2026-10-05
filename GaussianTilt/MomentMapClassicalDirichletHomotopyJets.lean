import GaussianTilt.MomentMapClassicalDirichletContinuationOpen
import GaussianTilt.MomentMapClassicalDirichletIntrinsicInterior
import GaussianTilt.MomentMapHolderSmoothEmbedding

/-! # Constructed initial jet and actual Hölder forcing homotopy -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- The starting solution and every right-hand side are actual elements of
the constructed Hölder Banach spaces. The pointwise homotopy is unchanged. -/
theorem exists_intrinsic_dirichlet_homotopy {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ j₀ : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ∃ F : ℝ → Space {x | d.coordinateDefining x ≤ 0} ℝ α,
      ContDiff ℝ ∞ F ∧
      (∀ x : {x | d.coordinateDefining x ≤ 0},
        value {x | d.coordinateDefining x ≤ 0} ℝ α (jetValue (CoordinateSpace n) ℝ d.coordinate_body_convex α j₀.1) x = d.coordinateDefining x) ∧
      (∀ x : {x | d.coordinateDefining x ≤ 0}, (hessianMatrix d.coordinate_body_convex α j₀.1 x).PosDef) ∧
      mongeAmpere d.coordinate_body_convex α j₀.1 = F 0 ∧
      (∀ t : ℝ, ∀ x : {x | d.coordinateDefining x ≤ 0},
        value {x | d.coordinateDefining x ≤ 0} ℝ α (F t) x = dirichletContinuationDensity d.coordinateDefining t x) := by
  obtain ⟨j,hval,hD,hH⟩ := exists_jet_of_smooth d.coordinate_body_convex d.coordinate_body_compact
    hα hα1 d.coordinateDefining d.coordinateDefining_smooth
  have hzero : j ∈ zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α := by
    simp only [zeroBoundary,Submodule.mem_iInf,LinearMap.mem_ker]
    intro x
    change value {x | d.coordinateDefining x ≤ 0} ℝ α
      (jetValue (CoordinateSpace n) ℝ d.coordinate_body_convex α j) x.1 = 0
    rw [hval]
    exact d.coordinate_zero_boundary x.1 x.2
  have hmat (x : {x | d.coordinateDefining x ≤ 0}) :
      hessianMatrix d.coordinate_body_convex α j x = coordinateHessian d.coordinateDefining x := by
    ext i l
    rw [holder_hessianMatrix_apply,hH]
    rw [coordinateHessian_eq_secondFDerivAt (contDiff_infty.mp d.coordinateDefining_smooth 2).contDiffAt]
    rfl
  let F : ℝ → Space {x | d.coordinateDefining x ≤ 0} ℝ α := fun t =>
    (1-t) • mongeAmpere d.coordinate_body_convex α j + t • constant {x | d.coordinateDefining x ≤ 0} α 1
  have hF : ContDiff ℝ ∞ F :=
    ((contDiff_const.sub contDiff_id).smul contDiff_const).add (contDiff_id.smul contDiff_const)
  refine ⟨⟨j,hzero⟩,F,hF,hval,fun x => ?_,?_,?_⟩
  · rw [hmat]
    exact d.coordinateDefining_hessian_posDef x
  · simp [F]
  · intro t x
    simp only [F,map_add,map_smul,BoundedContinuousFunction.add_apply,BoundedContinuousFunction.smul_apply,
      value_mongeAmpere,hmat,value_constant,smul_eq_mul,mul_one]
    rfl

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
