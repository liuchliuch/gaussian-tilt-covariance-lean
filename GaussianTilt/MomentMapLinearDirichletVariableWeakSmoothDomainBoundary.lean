import GaussianTilt.MomentMapLinearDirichletVariableWeakCurvedBoundary
import GaussianTilt.MomentMapLinearDirichletBoundaryFieldPatchRealization
import GaussianTilt.MomentMapLinearDirichletSmoothDomainBoundaryChart

/-! # Unconditional physical boundary patches for the constructed Laplace start

Every analytic boundary input is derived from the genuine H₀¹ solution and
the actual original Hölder datum. The resulting physical field patch is the
concrete input to global jet gluing and true Laplace surjectivity.
-/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapElliptic GaussianTilt.HolderSpace
variable {n : ℕ}
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 1000

namespace SmoothDomainLaplaceStartData

/-- Every boundary point of the actual smooth convex domain has a genuine
C²,α physical first/second-field patch for the constructed signed weak
Laplace solution. No boundary regularity or solvability premise remains. -/
theorem boundary_secondFieldPatch [NeZero n]
    {S A:Set (E n)} {d:SmoothInnerDomain S A} {α:ℝ}
    (hα:0<α) (hα1:α<1) {f:Space {y|d.coordinateDefining y≤0} ℝ α}
    (data:SmoothDomainLaplaceStartData d α f)
    (a:E n) (ha:a∈frontier d.body) :
    Nonempty (SecondFieldPatch d.body α data.euclideanRepresentative a) := by
  have ha0 := smoothDomain_defining_eq_zero_of_frontier d ha
  obtain ⟨q,hq,s,hs,hInv⟩ := exists_smoothDomain_boundary_chart d a ha
  obtain ⟨ψ,hψ,he,r,hr,hrmax,Q,H,hC2,hQc,hHc,hHH,hDu,hDG⟩ :=
    exists_curved_weak_boundary_C2_holder d.smooth a q hq hs hInv
      (data.chartWeakSolution a ha0) data.source (data.chartWeakSolution_equation a ha0)
      hα hα1 data.forcing_boundedHolderOn (data.chart_source_ae a)
      data.representative_continuous (data.chart_representative_ae_on a ha0)
      (data.chartWeakSolution_representative_zero a ha0)
  exact boundary_secondFieldPatch_of_inverse_model_fields d hα hα1.le data a ha q hq hs hr
    (by linarith : r≤1) ψ he Q H hC2.continuousOn hQc hHc hDu hDG hHH

end SmoothDomainLaplaceStartData
end GaussianTilt.MomentMapLinearDirichlet
