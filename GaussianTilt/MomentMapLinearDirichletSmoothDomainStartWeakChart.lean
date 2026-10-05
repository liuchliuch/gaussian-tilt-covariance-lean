import GaussianTilt.MomentMapLinearDirichletSmoothDomainStartData
import GaussianTilt.MomentMapLinearDirichletVariableWeakPhysicalValue

/-! # Exact Sobolev/domain/sign interface of the genuine start with weak boundary charts -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.HolderSpace GaussianTilt.MomentMapRegularity GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}
namespace SmoothDomainLaplaceStartData
variable {S A : Set (E n)} {d : SmoothInnerDomain S A} {α : ℝ}
  {f : Space {y | d.coordinateDefining y ≤ 0} ℝ α}

lemma chartPhysicalDomain_eq (a : E n) (ha : d.defining a=0) :
    chartPhysicalDomain d.defining a={y | d.coordinateDefining y<0} := by
  simp only [chartPhysicalDomain,ha,SmoothInnerDomain.coordinateDefining]

/-- Only the definition of the same physical domain changes. The actual
L² value and every weak-gradient coordinate remain literally unchanged. -/
def chartWeakSolution (data : SmoothDomainLaplaceStartData d α f)
    (a : E n) (ha : d.defining a=0) : dirichletSobolev (chartPhysicalDomain d.defining a) :=
  ⟨data.weakSolution.1,by rw [chartPhysicalDomain_eq a ha]; exact data.weakSolution.2⟩

lemma chartWeakSolution_coe (data : SmoothDomainLaplaceStartData d α f)
    (a : E n) (ha : d.defining a=0) :
    (data.chartWeakSolution a ha).1=data.weakSolution.1 := rfl

lemma chartWeakSolution_equation (data : SmoothDomainLaplaceStartData d α f)
    (a : E n) (ha : d.defining a=0)
    (w : dirichletSobolev (chartPhysicalDomain d.defining a)) :
    dirichletEnergy (chartPhysicalDomain d.defining a) (data.chartWeakSolution a ha) w=
      inner ℝ data.source (dirichletValue (chartPhysicalDomain d.defining a) w) := by
  let v : dirichletSobolev {y | d.coordinateDefining y<0} :=
    ⟨w.1,by rw [← chartPhysicalDomain_eq a ha]; exact w.2⟩
  have he := data.weak_equation v
  rw [dirichletEnergy_apply] at he ⊢
  change (∑ i : Fin n,inner ℝ (data.weakSolution.1 i.succ) (w.1 i.succ))=
    inner ℝ data.source (w.1 0) at he ⊢
  exact he

lemma chartWeakSolution_representative_ae (data : SmoothDomainLaplaceStartData d α f)
    (a : E n) (ha : d.defining a=0) :
    data.representative =ᵐ[volume] (data.chartWeakSolution a ha).1 0 := data.representative_ae

lemma chartWeakSolution_representative_zero (data : SmoothDomainLaplaceStartData d α f)
    (a : E n) (ha : d.defining a=0) :
    ∀ x, x ∉ chartPhysicalDomain d.defining a → data.representative x=0 := by
  rw [chartPhysicalDomain_eq a ha]
  exact data.representative_zero

/-- The literal divergence-form source in the flattened weak equation is
the signed compact forcing, whose negative is the desired positive Laplace
datum. The actual Sobolev derivatives enter on the left. -/
lemma chartWeakSolution_compact_test (data : SmoothDomainLaplaceStartData d α f)
    (a : E n) (ha : d.defining a=0) (τ : smoothCompactCore n)
    (hτ : tsupport τ.1⊆chartPhysicalDomain d.defining a) :
    (∫ x, (fun i : Fin n => (data.chartWeakSolution a ha).1 i.succ x) ⬝ᵥ coordinateGradient τ.1 x)=
      ∫ x, data.forcing x*τ.1 x := by
  rw [dirichlet_weak_energy_compact_test (data.chartWeakSolution a ha) data.source
    (data.chartWeakSolution_equation a ha) τ hτ]
  apply integral_congr_ae
  filter_upwards [data.source_ae] with x hx
  rw [hx]

lemma forcing_boundedHolderOn (data : SmoothDomainLaplaceStartData d α f) :
    BoundedHolderOn α data.forcing univ := by
  refine ⟨2*‖f‖,by positivity,?_,?_⟩
  · intro x _
    exact (data.forcing_bound x).trans (by linarith [norm_nonneg f])
  · intro x _ y _
    exact data.forcing_holder x y

lemma chart_source_ae (data : SmoothDomainLaplaceStartData d α f) (a : E n) :
    ∀ᵐ x ∂volume, x ∈ chartPhysicalDomain d.defining a → data.source x=data.forcing x :=
  data.source_ae.mono (fun _ hx _ => hx)

lemma chart_representative_ae_on (data : SmoothDomainLaplaceStartData d α f)
    (a : E n) (ha : d.defining a=0) :
    ∀ᵐ x ∂volume, x ∈ chartPhysicalDomain d.defining a →
      data.representative x=(data.chartWeakSolution a ha).1 0 x :=
  (data.chartWeakSolution_representative_ae a ha).mono (fun _ hx _ => hx)

end SmoothDomainLaplaceStartData
end GaussianTilt.MomentMapLinearDirichlet
