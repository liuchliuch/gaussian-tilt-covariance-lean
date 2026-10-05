import GaussianTilt.MomentMapLinearDirichletJetPatchEmbedding

/-! # A concrete local field interface for the final weak Dirichlet gluing -/
noncomputable section
open Set
open scoped Topology
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual first and second fields on an open neighborhood of a closed-body
point. The derivative equations hold on the true interior and the fields
extend continuously, with the given Hölder exponent, to its closed patch. -/
structure SecondFieldPatch (S : Set E) (α : ℝ) (u : E → F) (x : E) where
  patch : Set E
  isOpen_patch : IsOpen patch
  mem_patch : x ∈ patch
  first : E → E →L[ℝ] F
  second : E → E →L[ℝ] E →L[ℝ] F
  first_continuous : ContinuousOn first (S ∩ patch)
  second_continuous : ContinuousOn second (S ∩ patch)
  first_derivative : ∀ y ∈ interior S ∩ patch, HasFDerivAt u (first y) y
  second_derivative : ∀ y ∈ interior S ∩ patch, HasFDerivAt first (second y) y
  second_holder : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ S ∩ patch, ∀ z ∈ S ∩ patch,
    ‖second y-second z‖ ≤ C*(dist y z)^α

/-- The open cover, overlap compatibility, global Hölder bound and closed
FTC jet laws are all constructed from the actual pointwise patch family. -/
theorem exists_zeroBoundary_jet_of_secondFieldPatches [CompleteSpace F]
    {S : Set E} (hS : Convex ℝ S) (hSc : IsCompact S) (hint : (interior S).Nonempty)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {u : E → F} (hu : ContinuousOn u S) (hzero : ∀ x ∈ frontier S, u x=0)
    (hpatch : ∀ x : S, Nonempty (SecondFieldPatch S α u x)) :
    ∃ J : zeroBoundary E F hS α,
      ∀ x : S, value S F α (jetValue E F hS α J.1) x=u x := by
  classical
  let p := fun x : S => Classical.choice (hpatch x)
  obtain ⟨J,hvalue,hfirst,hsecond⟩ := exists_zeroBoundary_jet_of_local_second_fields
    hS hSc hint hα hα1 (fun x : S => (p x).patch) (fun x => (p x).isOpen_patch)
    (fun x hx => ⟨⟨x,hx⟩,(p ⟨x,hx⟩).mem_patch⟩) u hu hzero
    (fun x => (p x).first) (fun x => (p x).second)
    (fun x => (p x).first_continuous) (fun x => (p x).second_continuous)
    (fun x y hy => (p x).first_derivative y hy)
    (fun x y hy => (p x).second_derivative y hy)
    (fun x => (p x).second_holder)
  exact ⟨J,hvalue⟩

end GaussianTilt.MomentMapLinearDirichlet
