import GaussianTilt.MomentMapLinearDirichletSmoothDomainStartWeakChart
import GaussianTilt.MomentMapLinearDirichletFlatteningCoordinates

/-! # A genuine transverse scaled weak chart at every actual smooth-domain boundary point -/
noncomputable section
set_option maxHeartbeats 1500000
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapElliptic GaussianTilt.Letwin
variable {n : ℕ}

lemma smoothDomain_defining_eq_zero_of_frontier {S A : Set (E n)} (d : SmoothInnerDomain S A)
    {a : E n} (ha : a ∈ frontier d.body) : d.defining a=0 := by
  have hle : d.defining a≤0 := d.compact_sublevel.isClosed.frontier_subset ha
  have hn : ¬d.defining a<0 := by
    intro hh
    apply ha.2
    rw [d.interior_body]
    exact hh
  exact le_antisymm hle (le_of_not_gt hn)

/-- A real transverse coordinate and a positive chart scale are selected
from the defining function. The entire doubled closed chart ball lies in
the actual IFT target with a genuinely smooth inverse. -/
theorem exists_smoothDomain_boundary_chart {S A : Set (E n)} (d : SmoothInnerDomain S A)
    (a : E n) (ha : a ∈ frontier d.body) :
    ∃ q : Fin n, ∃ hq : fderiv ℝ d.defining a (EuclideanSpace.basisFun (Fin n) ℝ q)≠0,
      ∃ s : ℝ, 0 < s ∧ ∀ z ∈ Metric.closedBall (0 : E n) (2*s),
        z ∈ (regularLevelFlatteningChart d.smooth a q hq).target ∧
        ContDiffAt ℝ ∞ (regularLevelFlatteningChart d.smooth a q hq).symm z := by
  have ha0 := smoothDomain_defining_eq_zero_of_frontier d ha
  have hc : d.coordinateDefining (coordinateEquiv n a)=0 := by
    simpa only [SmoothInnerDomain.coordinateDefining,coordinatePullback,Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply] using ha0
  obtain ⟨q,hq⟩ := d.coordinate_transverse_index hc
  have hqa : fderiv ℝ d.defining a (EuclideanSpace.basisFun (Fin n) ℝ q)≠0 := by
    simpa only [SmoothInnerDomain.coordinateDefining,
      coordinateDerivative_pullback_at (d.smooth.differentiable (by simp) a)] using hq
  obtain ⟨r,hr,hInv⟩ := exists_regularLevelFlattening_inverse_ball d.smooth a q hqa
  refine ⟨q,hqa,r/4,by positivity,?_⟩
  intro z hz
  have hzr : z ∈ Metric.ball (0 : E n) r :=
    Metric.closedBall_subset_ball (by linarith) hz
  exact ⟨(hInv z hzr).1,(hInv z hzr).2.1⟩

end GaussianTilt.MomentMapLinearDirichlet
