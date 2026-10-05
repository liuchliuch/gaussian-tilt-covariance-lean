import GaussianTilt.MomentMapLinearDirichletVariableWeakSmoothDomainBoundary
import GaussianTilt.MomentMapLinearDirichletSmoothDomainStartClosure

/-! # Unconditional surjectivity of the genuine positive Dirichlet Laplacian

For every actual Hölder datum, the signed compact extension, H₀¹ solution,
continuous representative, true same-exponent interior and boundary fields,
closed jet, and coordinate/operator realization are all constructed.
-/
noncomputable section
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
open Set
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.HolderSpace GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

/-- The actual positive Laplace operator on the complete zero-boundary
C²,α jet space is surjective. There is no weak/classical solvability,
boundary regularity, inverse or estimate hypothesis. -/
theorem smoothDomain_laplace_surjective [NeZero n]
    {S A : Set (E n)} (d : SmoothInnerDomain S A)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Function.Surjective (ellipticDirichletOperator d.coordinate_body_convex α
      (identityFields {y | d.coordinateDefining y ≤ 0} α)) := by
  intro f
  obtain ⟨data⟩ := exists_smoothDomain_laplace_start_data d hα hα1 f
  exact raw_laplace_preimage_of_boundary_secondFieldPatches d hα hα1 f data
    (SmoothDomainLaplaceStartData.boundary_secondFieldPatch hα hα1 data)

end GaussianTilt.MomentMapLinearDirichlet
