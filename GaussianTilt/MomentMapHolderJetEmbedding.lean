import GaussianTilt.MomentMapHolderJetRegularity

/-! # Faithfulness and actual bounds of the Dirichlet Hölder Banach domain -/
noncomputable section
open Set
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma norm_jetValue_le {S : Set E} (hS : Convex ℝ S) (α : ℝ) (j : Jet E F hS α) :
    ‖jetValue E F hS α j‖ ≤ ‖j‖ := le_max_left _ _

lemma norm_jetFirst_le {S : Set E} (hS : Convex ℝ S) (α : ℝ) (j : Jet E F hS α) :
    ‖jetFirst E F hS α j‖ ≤ ‖j‖ := (le_max_left _ _).trans (le_max_right _ _)

lemma norm_jetSecond_le {S : Set E} (hS : Convex ℝ S) (α : ℝ) (j : Jet E F hS α) :
    ‖jetSecond E F hS α j‖ ≤ ‖j‖ := (le_max_right _ _).trans (le_max_right _ _)

/-- The complete jet space contains no spurious derivative fields on a
full-dimensional convex domain: the actual function uniquely determines it. -/
theorem jetValue_injective {S : Set E} (hS : Convex ℝ S) (hint : (interior S).Nonempty)
    {α : ℝ} (hα : 0 < α) : Function.Injective (jetValue E F hS α) := by
  intro j k he
  have hUD := uniqueDiffOn_convex hS hint
  have hD : jetFirst E F hS α j = jetFirst E F hS α k := by
    apply value_injective S (E →L[ℝ] F) α
    apply BoundedContinuousFunction.ext
    intro x
    have hf := jet_hasFDerivWithinAt hS hα j x.2
    have hg := jet_hasFDerivWithinAt hS hα k x.2
    have hfunc : extendValue α (jetValue E F hS α j) = extendValue α (jetValue E F hS α k) :=
      congrArg (extendValue α) he
    rw [hfunc] at hf
    have heder := (hUD x x.2).eq hf hg
    rw [extendValue_mem α _ x.2, extendValue_mem α _ x.2] at heder
    exact heder
  have hH : jetSecond E F hS α j = jetSecond E F hS α k := by
    apply value_injective S (E →L[ℝ] E →L[ℝ] F) α
    apply BoundedContinuousFunction.ext
    intro x
    have hf := jet_first_hasFDerivWithinAt hS hα j x.2
    have hg := jet_first_hasFDerivWithinAt hS hα k x.2
    have hfunc : extendValue α (jetFirst E F hS α j) = extendValue α (jetFirst E F hS α k) :=
      congrArg (extendValue α) hD
    rw [hfunc] at hf
    have heder := (hUD x x.2).eq hf hg
    rw [extendValue_mem α _ x.2, extendValue_mem α _ x.2] at heder
    exact heder
  apply Subtype.ext
  exact Prod.ext he (Prod.ext hD hH)

/-- Literal zero boundary values follow from the closed kernel definition. -/
theorem zeroBoundary_value {S : Set E} (hS : Convex ℝ S) (hSc : IsClosed S) (α : ℝ)
    (j : zeroBoundary E F hS α) {x : E} (hx : x ∈ frontier S) :
    extendValue α (jetValue E F hS α j.1) x = 0 := by
  have hxs : x ∈ S := by
    have hc := frontier_subset_closure hx
    rwa [hSc.closure_eq] at hc
  rw [extendValue_mem α _ hxs]
  have hj := j.2
  simp only [zeroBoundary, Submodule.mem_iInf, LinearMap.mem_ker] at hj
  exact hj ⟨⟨x, hxs⟩, hx⟩

end GaussianTilt.HolderSpace
