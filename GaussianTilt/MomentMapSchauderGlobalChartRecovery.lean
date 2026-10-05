import GaussianTilt.MomentMapHolderChartComposition
import GaussianTilt.MomentMapLinearDirichletFlatteningChainRule

/-! # Actual recovery of closed-domain derivative fields through a chart -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.HolderSpace
variable {n : ℕ}

/-- Equality of continuous fields on interior points extends to every
point of a relatively open patch of a full-dimensional closed convex body. -/
lemma eqOn_convex_patch_of_eqOn_interior {F : Type*} [TopologicalSpace F] [T2Space F]
    {S U : Set (KernelSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S)
    (hint : (interior S).Nonempty) (hU : IsOpen U) {f g : KernelSpace n → F}
    (hf : ContinuousOn f (S ∩ U)) (hg : ContinuousOn g (S ∩ U))
    (he : EqOn f g (interior S ∩ U)) : EqOn f g (S ∩ U) := by
  have hcl : closure (interior S)=S := (hS.closure_interior_eq_closure_of_nonempty_interior hint).trans hSc.closure_eq
  apply he.of_subset_closure hf hg (inter_subset_inter_left U interior_subset)
  intro x hx
  exact hU.closure_inter ⟨by rw [hcl]; exact hx.1,hx.2⟩

/-- No boundary chain rule is assumed. True interior derivatives and
continuity recover the complete closed first/second fields under the
fixed smooth forward chart. -/
theorem jet_fields_recover_through_smooth_chart
    {S T U : Set (KernelSpace n)} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hSc : IsClosed S) (hint : (interior S).Nonempty) (hU : IsOpen U)
    {α : ℝ} (hα : 0 < α) (J : Jet (KernelSpace n) ℝ hS α) (j : Jet (KernelSpace n) ℝ hT α)
    (φ : KernelSpace n → KernelSpace n) (hφ : ContDiff ℝ ∞ φ)
    (hmapi : MapsTo φ (interior S ∩ U) (interior T))
    (hvalue : ∀ x ∈ S ∩ U,
      extendValue α (jetValue (KernelSpace n) ℝ hS α J) x=
        extendValue α (jetValue (KernelSpace n) ℝ hT α j) (φ x))
    (hfirstc : ContinuousOn (chartFirst (extendValue α (jetFirst (KernelSpace n) ℝ hT α j)) φ) (S ∩ U))
    (hsecondc : ContinuousOn (chartSecond (extendValue α (jetFirst (KernelSpace n) ℝ hT α j))
      (extendValue α (jetSecond (KernelSpace n) ℝ hT α j)) φ) (S ∩ U)) :
    EqOn (extendValue α (jetFirst (KernelSpace n) ℝ hS α J))
      (chartFirst (extendValue α (jetFirst (KernelSpace n) ℝ hT α j)) φ) (S ∩ U) ∧
    EqOn (extendValue α (jetSecond (KernelSpace n) ℝ hS α J))
      (chartSecond (extendValue α (jetFirst (KernelSpace n) ℝ hT α j))
        (extendValue α (jetSecond (KernelSpace n) ℝ hT α j)) φ) (S ∩ U) := by
  let u := extendValue α (jetValue (KernelSpace n) ℝ hS α J)
  let v := extendValue α (jetValue (KernelSpace n) ℝ hT α j)
  have heN : ∀ x ∈ interior S ∩ U, u =ᶠ[𝓝 x] (v ∘ φ) := by
    intro x hx
    filter_upwards [(isOpen_interior.inter hU).mem_nhds hx] with y hy
    exact hvalue y ⟨interior_subset hy.1,hy.2⟩
  constructor
  · apply eqOn_convex_patch_of_eqOn_interior hS hSc hint hU
      ((continuousOn_extendValue α _).mono inter_subset_left) hfirstc
    intro x hx
    rw [← (jet_hasFDerivAt hS hα J hx.1).fderiv,(heN x hx).fderiv_eq]
    have hv := jet_hasFDerivAt hT hα j (hmapi hx)
    have hc := hv.comp x ((hφ.differentiable (by simp) x).hasFDerivAt)
    exact hc.fderiv
  · apply eqOn_convex_patch_of_eqOn_interior hS hSc hint hU
      ((continuousOn_extendValue α _).mono inter_subset_left) hsecondc
    intro x hx
    rw [← jet_second_eq_fderiv_fderiv hS hα J hx.1,(heN x hx).fderiv.fderiv_eq]
    have hv : ContDiffAt ℝ 2 v (φ x) :=
      (jet_contDiffOn_two hT hα j).contDiffAt (isOpen_interior.mem_nhds (hmapi hx))
    have hvc := (jet_hasFDerivAt hT hα j (hmapi hx)).fderiv
    have hvB := jet_second_eq_fderiv_fderiv hT hα j (hmapi hx)
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    rw [secondFrechet_comp_at hv (contDiff_infty.mp hφ 2).contDiffAt a b,hvc,hvB]
    simp only [chartSecond,ContinuousLinearMap.add_apply,ContinuousLinearMap.bilinearComp_apply,postcomposeBilinear]
    rfl

end GaussianTilt.MomentMapSchauder
