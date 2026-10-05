import GaussianTilt.MomentMapLinearDirichletInteriorJetPatch
import GaussianTilt.MomentMapLinearDirichletEuclideanWeakGradient

/-! # Same-exponent interior patches of the actual Dirichlet weak solution -/
noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Every genuine H₀¹ solution of the actual energy equation solves the
literal compact-test distributional equation. -/
theorem weakLaplace_distribution_of_dirichlet_equation {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (hu : ∀ v : dirichletSobolev Ω,dirichletEnergy Ω u v=inner ℝ f (dirichletValue Ω v))
    {ψ : CoordinateSpace n→ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ⊆Ω) :
    (∫ x,dirichletValue Ω u x*euclideanLaplacian ψ x)= -(∫ x,f x*ψ x) := by
  let g : smoothCompactCore n := ⟨ψ,hψ,hψc⟩
  let v := dirichletCoreToSobolev Ω ⟨g,hψs⟩
  have he := hu v
  rw [dirichletEnergy_apply] at he
  change (∑ i : Fin n,inner ℝ (u.1 i.succ) (smoothCompactToL2 volume (smoothCompactDerivative i g)))=
    inner ℝ f (smoothCompactToL2 volume g) at he
  rw [dirichletSobolev_laplacian_pairing,inner_Lp_smoothCompactToL2] at he
  change -(∫ x,dirichletValue Ω u x*euclideanLaplacian ψ x)=(∫ x,f x*ψ x) at he
  linarith

/-- The continuous actual AE representative, rather than a new unrelated
function, has interior C²,α patches with the exact forcing exponent. -/
theorem exists_interior_jet_patch_of_weakLaplace_representative [NeZero n]
    {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (u : dirichletSobolev Ω) (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (hu : ∀ v : dirichletSobolev Ω,dirichletEnergy Ω u v=inner ℝ f (dirichletValue Ω v))
    {v f₀ : CoordinateSpace n→ℝ} (hv : Continuous v) (hvu : v=ᵐ[volume] dirichletValue Ω u)
    (hf : Continuous f₀) (hfc : HasCompactSupport f₀) (hff : f=ᵐ[volume] f₀)
    {α H : ℝ} (hα : 0<α) (hα1 : α<1) (hH : 0≤H)
    (hholder : ∀ x y,|f₀ x-f₀ y|≤H*‖x-y‖^α) :
    ∀ x∈(dirichletCoordinateEquiv n) ⁻¹' Ω,
      ∃ U : Set (KernelSpace n),IsOpen U ∧ x∈U ∧ U⊆(dirichletCoordinateEquiv n) ⁻¹' Ω ∧
        ContinuousOn (fderiv ℝ (v ∘ dirichletCoordinateEquiv n)) U ∧
        ContinuousOn (fderiv ℝ (fderiv ℝ (v ∘ dirichletCoordinateEquiv n))) U ∧
        (∀ y∈U,HasFDerivAt (v ∘ dirichletCoordinateEquiv n) (fderiv ℝ (v ∘ dirichletCoordinateEquiv n) y) y) ∧
        (∀ y∈U,HasFDerivAt (fderiv ℝ (v ∘ dirichletCoordinateEquiv n))
          (fderiv ℝ (fderiv ℝ (v ∘ dirichletCoordinateEquiv n)) y) y) ∧
        ∃ C : ℝ,0≤C ∧ ∀ y∈U,∀ z∈U,
          ‖fderiv ℝ (fderiv ℝ (v ∘ dirichletCoordinateEquiv n)) y-
            fderiv ℝ (fderiv ℝ (v ∘ dirichletCoordinateEquiv n)) z‖≤C*dist y z^α := by
  let e := dirichletCoordinateEquiv n
  have hdist : ∀ ψ : CoordinateSpace n→ℝ,ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ⊆Ω →
      (∫ y,v y*euclideanLaplacian ψ y)=∫ y,(-f₀ y)*ψ y := by
    intro ψ hψ hψc hψs
    calc
      _ = ∫ y,dirichletValue Ω u y*euclideanLaplacian ψ y := by
        apply integral_congr_ae
        filter_upwards [hvu] with y hy
        rw [hy]
      _ = -(∫ y,f y*ψ y) := weakLaplace_distribution_of_dirichlet_equation u f hu hψ hψc hψs
      _ = _ := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [hff] with y hy
        rw [hy]
        ring
  have hEb : Bornology.IsBounded (e ⁻¹' Ω) := by
    apply (hΩb.isCompact_closure.image e.symm.continuous).isBounded.subset
    intro x hx
    exact ⟨e x,subset_closure hx,e.symm_apply_apply x⟩
  apply exists_open_interior_jet_patch_of_continuous_weak_poisson
    (hΩ.preimage e.continuous) hEb (hv.comp e.continuous)
    ((hf.neg).comp e.continuous) (hfc.neg.comp_homeomorph e.toHomeomorph) hα hα1 hH
  · exact holder_comp_dirichletCoordinateEquiv (f := fun x : CoordinateSpace n=> -f₀ x) hH hα.le
      (fun x y=>by simpa only [neg_sub_neg,abs_sub_comm] using hholder x y)
  · exact distribution_poisson_ofLp hdist

end GaussianTilt.MomentMapLinearDirichlet
