import GaussianTilt.MomentMapLinearDirichletSmoothDomainStartData
import GaussianTilt.MomentMapLinearDirichletInteriorJetPatchWeak
import GaussianTilt.MomentMapLinearDirichletSecondFieldPatch

/-! # Actual same-exponent interior patches for the common starting solution -/
noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory Set Filter
open scoped Topology ContDiff BoundedContinuousFunction
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.HolderSpace GaussianTilt.MomentMapElliptic
variable {n : ℕ}
namespace SmoothDomainLaplaceStartData
variable {S A : Set (E n)} {d : SmoothInnerDomain S A} {α : ℝ}
  {f : Space {y | d.coordinateDefining y ≤ 0} ℝ α}

/-- The Euclidean representative is the same actual continuous weak
solution, composed with the literal coordinate equivalence. -/
def euclideanRepresentative (data : SmoothDomainLaplaceStartData d α f) : E n → ℝ :=
  data.representative ∘ coordinateEquiv n

lemma euclideanRepresentative_continuous (data : SmoothDomainLaplaceStartData d α f) :
    Continuous data.euclideanRepresentative := data.representative_continuous.comp (coordinateEquiv n).continuous

lemma euclideanRepresentative_zero_frontier (data : SmoothDomainLaplaceStartData d α f)
    (x : E n) (hx : x ∈ frontier d.body) : data.euclideanRepresentative x=0 := by
  have hxi : x ∉ d.domain := by simpa only [← d.interior_body] using hx.2
  apply data.representative_zero
  simpa only [SmoothInnerDomain.coordinateDefining,coordinatePullback,Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply] using hxi

lemma euclideanRepresentative_positive_equation (data : SmoothDomainLaplaceStartData d α f)
    (x : E n) (hx : x ∈ d.domain) : kernelLaplacian data.euclideanRepresentative x =
      value {y | d.coordinateDefining y ≤ 0} ℝ α f
        ⟨coordinateEquiv n x,by
          change d.defining ((coordinateEquiv n).symm (coordinateEquiv n x)) ≤ 0
          simpa only [ContinuousLinearEquiv.symm_apply_apply] using (show d.defining x<0 from hx).le⟩ := by
  have hcx : d.coordinateDefining (coordinateEquiv n x)<0 := by
    simpa only [SmoothInnerDomain.coordinateDefining,coordinatePullback,Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply] using hx
  change kernelLaplacian (data.representative ∘ dirichletCoordinateEquiv n) x = _
  rw [kernelLaplacian_ofLp_any]
  exact data.positive_datum_equation _ hcx

/-- These interior patches are constructed from the original H₀¹ energy
equation and AE representative. No local regularity premise remains. -/
theorem interior_secondFieldPatch [NeZero n]
    (data : SmoothDomainLaplaceStartData d α f) (hα : 0 < α) (hα1 : α < 1)
    (x : E n) (hx : x ∈ interior d.body) :
    Nonempty (SecondFieldPatch d.body α data.euclideanRepresentative x) := by
  have hΩ : IsOpen {y | d.coordinateDefining y<0} := isOpen_lt d.coordinateDefining_smooth.continuous continuous_const
  have hΩb : Bornology.IsBounded {y | d.coordinateDefining y<0} :=
    d.coordinate_body_compact.isBounded.subset
      (fun y (hy : d.coordinateDefining y<0) => show d.coordinateDefining y≤0 from hy.le)
  have he : (dirichletCoordinateEquiv n) ⁻¹' {y | d.coordinateDefining y<0}=d.domain := by
    ext y
    change d.defining ((coordinateEquiv n).symm (coordinateEquiv n y))<0 ↔ d.defining y<0
    rw [ContinuousLinearEquiv.symm_apply_apply]
  have hpatch := exists_interior_jet_patch_of_weakLaplace_representative hΩ hΩb
    data.weakSolution data.source data.weak_equation data.representative_continuous
    data.representative_ae data.forcing_continuous data.forcing_compact data.source_ae
    hα hα1 (by positivity : 0≤2*‖f‖) data.forcing_holder
  rw [he] at hpatch
  obtain ⟨U,hU,hxU,hUΩ,hD,hH,hDu,hDH,C,hC,hHolder⟩ := hpatch x (d.interior_body ▸ hx)
  have hfields : data.representative ∘ dirichletCoordinateEquiv n=data.euclideanRepresentative := rfl
  rw [hfields] at hD hH hDu hDH hHolder
  exact ⟨{
    patch := U
    isOpen_patch := hU
    mem_patch := hxU
    first := fderiv ℝ data.euclideanRepresentative
    second := fderiv ℝ (fderiv ℝ data.euclideanRepresentative)
    first_continuous := hD.mono inter_subset_right
    second_continuous := hH.mono inter_subset_right
    first_derivative := fun y hy => hDu y hy.2
    second_derivative := fun y hy => hDH y hy.2
    second_holder := ⟨C,hC,fun y hy z hz => hHolder y hy.2 z hz.2⟩ }⟩

end SmoothDomainLaplaceStartData
end GaussianTilt.MomentMapLinearDirichlet
