import GaussianTilt.MomentMapLinearDirichletJetPatchGluing

/-! # A genuine global closed Hölder jet from local C²,α fields

The lower Hölder bounds, overlap compatibility and both segment FTC laws
are derived. Only the actual local second-order fields and their local
Hölder estimates enter as regularity data.
-/
noncomputable section
set_option maxHeartbeats 2500000
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma exists_holder_bound_of_continuous_interior_field {S : Set E}
    (hS : Convex ℝ S) (hSc : IsCompact S) (hint : (interior S).Nonempty)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : E → F} {D : E → E →L[ℝ] F}
    (hu : ContinuousOn u S) (hD : ContinuousOn D S)
    (hd : ∀ x ∈ interior S, HasFDerivAt u (D x) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ y ∈ S, ‖u x-u y‖ ≤ C*(dist x y)^α := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hSc
  let b : S →ᵇ F := BoundedContinuousFunction.mkOfCompact ⟨fun x => u x,
    continuousOn_iff_continuous_restrict.mp hu⟩
  obtain ⟨B,hB⟩ := hSc.exists_bound_of_continuousOn hD
  let L := max B 0
  have hL : 0 ≤ L := le_max_right _ _
  have hLip : ∀ x y : S, ‖b x-b y‖ ≤ L*dist x y := by
    intro x y
    have hh := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => hasFDerivWithinAt_of_continuous_interior_field hS hSc.isClosed hint hu hD hd hz)
      (fun z hz => (hB z hz).trans (le_max_left B 0)) y.2 x.2
    change ‖u x-u y‖ ≤ max B 0*dist (x:E) (y:E)
    simpa only [dist_eq_norm] using hh
  refine ⟨max L (2*‖b‖),hL.trans (le_max_left _ _),?_⟩
  intro x hx y hy
  exact holder_bound_of_bounded_lipschitz S b hα hα1 hL hLip ⟨x,hx⟩ ⟨y,hy⟩

/-- The constructed global Hölder jet agrees with every local derivative
field throughout the corresponding closed-domain patch. -/
theorem exists_jet_of_local_second_fields {ι : Type*} {S : Set E}
    (hS : Convex ℝ S) (hSc : IsCompact S) (hint : (interior S).Nonempty)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x ∈ S, ∃ i, x ∈ U i)
    (u : E → F) (hu : ContinuousOn u S)
    (D : ι → E → E →L[ℝ] F) (H : ι → E → E →L[ℝ] E →L[ℝ] F)
    (hD : ∀ i, ContinuousOn (D i) (S ∩ U i)) (hH : ∀ i, ContinuousOn (H i) (S ∩ U i))
    (hdu : ∀ i x, x ∈ interior S ∩ U i → HasFDerivAt u (D i x) x)
    (hdD : ∀ i x, x ∈ interior S ∩ U i → HasFDerivAt (D i) (H i x) x)
    (hHolder : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S ∩ U i, ∀ y ∈ S ∩ U i,
      ‖H i x-H i y‖ ≤ C*(dist x y)^α) :
    ∃ j : Jet E F hS α,
      (∀ x : S, value S F α (jetValue E F hS α j) x=u x) ∧
      (∀ i, ∀ x : S, (x:E) ∈ U i → value S (E →L[ℝ] F) α (jetFirst E F hS α j) x=D i x) ∧
      (∀ i, ∀ x : S, (x:E) ∈ U i → value S (E →L[ℝ] E →L[ℝ] F) α (jetSecond E F hS α j) x=H i x) := by
  obtain ⟨G,K,hG,hK,hGD,hKH,hduG,hdG⟩ := exists_global_derivative_fields_of_patches hS hSc.isClosed hint
    U hU hcover u D H hD hH hdu hdD
  obtain ⟨Cu,hCu,huh⟩ := exists_holder_bound_of_continuous_interior_field hS hSc hint hα.le hα1 hu hG hduG
  obtain ⟨CG,hCG,hGh⟩ := exists_holder_bound_of_continuous_interior_field hS hSc hint hα.le hα1 hG hK hdG
  obtain ⟨CK,hCK,hKh⟩ := exists_holder_bound_of_glued_patches hSc hα.le U hU hcover H K hK hKH hHolder
  obtain ⟨j,hju,hjG,hjK⟩ := exists_jet_of_continuous_holder_interior_fields hS hSc hint u G K
    hu hG hK huh hGh hKh hduG hdG
  refine ⟨j,hju,?_,?_⟩
  · intro i x hx
    exact (hjG x).trans (hGD i ⟨x.2,hx⟩)
  · intro i x hx
    exact (hjK x).trans (hKH i ⟨x.2,hx⟩)

/-- Literal zero boundary values put the constructed compatible jet in
the actual closed zero-boundary Banach subspace. -/
theorem exists_zeroBoundary_jet_of_local_second_fields {ι : Type*} {S : Set E}
    (hS : Convex ℝ S) (hSc : IsCompact S) (hint : (interior S).Nonempty)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x ∈ S, ∃ i, x ∈ U i)
    (u : E → F) (hu : ContinuousOn u S) (hzero : ∀ x ∈ frontier S, u x=0)
    (D : ι → E → E →L[ℝ] F) (H : ι → E → E →L[ℝ] E →L[ℝ] F)
    (hD : ∀ i, ContinuousOn (D i) (S ∩ U i)) (hH : ∀ i, ContinuousOn (H i) (S ∩ U i))
    (hdu : ∀ i x, x ∈ interior S ∩ U i → HasFDerivAt u (D i x) x)
    (hdD : ∀ i x, x ∈ interior S ∩ U i → HasFDerivAt (D i) (H i x) x)
    (hHolder : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S ∩ U i, ∀ y ∈ S ∩ U i,
      ‖H i x-H i y‖ ≤ C*(dist x y)^α) :
    ∃ j : zeroBoundary E F hS α,
      (∀ x : S, value S F α (jetValue E F hS α j.1) x=u x) ∧
      (∀ i, ∀ x : S, (x:E) ∈ U i → value S (E →L[ℝ] F) α (jetFirst E F hS α j.1) x=D i x) ∧
      (∀ i, ∀ x : S, (x:E) ∈ U i → value S (E →L[ℝ] E →L[ℝ] F) α (jetSecond E F hS α j.1) x=H i x) := by
  obtain ⟨j,hju,hjD,hjH⟩ := exists_jet_of_local_second_fields hS hSc hint hα hα1 U hU hcover u hu D H hD hH hdu hdD hHolder
  have hjzero : j ∈ zeroBoundary E F hS α := by
    simp only [zeroBoundary,Submodule.mem_iInf,LinearMap.mem_ker]
    intro x
    change value S F α (jetValue E F hS α j) x.1=0
    rw [hju]
    exact hzero x.1 x.2
  exact ⟨⟨j,hjzero⟩,hju,hjD,hjH⟩

end GaussianTilt.MomentMapLinearDirichlet
