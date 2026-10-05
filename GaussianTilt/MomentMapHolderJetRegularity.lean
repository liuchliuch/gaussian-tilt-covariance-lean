import GaussianTilt.MomentMapHolderJets
import GaussianTilt.MomentMapHolderDerivatives

/-! # The complete FTC jet space consists of actual C² functions -/
noncomputable section
open Set Filter
open scoped Topology
namespace GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The first stored field is the actual Fréchet derivative at every
interior point, as a consequence of its proved FTC compatibility. -/
theorem jet_hasFDerivAt {S : Set E} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet E F hS α) {x : E} (hx : x ∈ interior S) :
    HasFDerivAt (extendValue α (jetValue E F hS α j))
      (extendValue α (jetFirst E F hS α j) x) x := by
  rw [extendValue_mem α _ (interior_subset hx)]
  exact hasFDerivAt_extendValue_of_ftc hS hα _ _
    (fun x y => (jet_ftc E F hS α j x y).1) ⟨x, interior_subset hx⟩ hx

/-- The second stored field is the actual derivative of the first. -/
theorem jet_first_hasFDerivAt {S : Set E} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet E F hS α) {x : E} (hx : x ∈ interior S) :
    HasFDerivAt (extendValue α (jetFirst E F hS α j))
      (extendValue α (jetSecond E F hS α j) x) x := by
  rw [extendValue_mem α _ (interior_subset hx)]
  exact hasFDerivAt_extendValue_of_ftc hS hα _ _
    (fun x y => (jet_ftc E F hS α j x y).2) ⟨x, interior_subset hx⟩ hx

/-- Actual C² regularity follows from closed linear FTC conditions plus
Hölder continuity of the fields, with no differentiability premise. -/
theorem jet_contDiffOn_two {S : Set E} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet E F hS α) :
    ContDiffOn ℝ 2 (extendValue α (jetValue E F hS α j)) (interior S) := by
  have hg : ContDiffOn ℝ 1 (extendValue α (jetFirst E F hS α j)) (interior S) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_interior]
    refine ⟨fun x hx => (jet_first_hasFDerivAt hS hα j hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · simp
    · rw [contDiffOn_zero]
      exact ((continuousOn_extendValue α (jetSecond E F hS α j)).mono interior_subset).congr
        (fun x hx => (jet_first_hasFDerivAt hS hα j hx).fderiv)
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_interior]
  refine ⟨fun x hx => (jet_hasFDerivAt hS hα j hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · simp
  · exact hg.congr (fun x hx => (jet_hasFDerivAt hS hα j hx).fderiv)

/-- The stored second jet is exactly the true iterated Fréchet derivative. -/
theorem jet_second_eq_fderiv_fderiv {S : Set E} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet E F hS α) {x : E} (hx : x ∈ interior S) :
    fderiv ℝ (fderiv ℝ (extendValue α (jetValue E F hS α j))) x =
      extendValue α (jetSecond E F hS α j) x := by
  have he : fderiv ℝ (extendValue α (jetValue E F hS α j)) =ᶠ[𝓝 x]
      extendValue α (jetFirst E F hS α j) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact (jet_hasFDerivAt hS hα j hy).fderiv
  rw [he.fderiv.self_of_nhds]
  exact (jet_first_hasFDerivAt hS hα j hx).fderiv

/-- Second-derivative symmetry is a derived analytic fact, not an
additional compatibility condition in the Banach-space definition. -/
theorem jet_second_symmetric {S : Set E} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet E F hS α) {x : E} (hx : x ∈ interior S) (v w : E) :
    extendValue α (jetSecond E F hS α j) x v w =
      extendValue α (jetSecond E F hS α j) x w v := by
  have hs := ((jet_contDiffOn_two hS hα j).contDiffAt (isOpen_interior.mem_nhds hx)).isSymmSndFDerivAt
    (by simp)
  rw [← jet_second_eq_fderiv_fderiv hS hα j hx]
  exact hs v w

theorem jet_hasFDerivWithinAt {S : Set E} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet E F hS α) {x : E} (hx : x ∈ S) :
    HasFDerivWithinAt (extendValue α (jetValue E F hS α j))
      (extendValue α (jetFirst E F hS α j) x) S x := by
  rw [extendValue_mem α _ hx]
  exact hasFDerivWithinAt_extendValue_of_ftc hS hα _ _
    (fun x y => (jet_ftc E F hS α j x y).1) ⟨x, hx⟩

theorem jet_first_hasFDerivWithinAt {S : Set E} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet E F hS α) {x : E} (hx : x ∈ S) :
    HasFDerivWithinAt (extendValue α (jetFirst E F hS α j))
      (extendValue α (jetSecond E F hS α j) x) S x := by
  rw [extendValue_mem α _ hx]
  exact hasFDerivWithinAt_extendValue_of_ftc hS hα _ _
    (fun x y => (jet_ftc E F hS α j x y).2) ⟨x, hx⟩

/-- On a full-dimensional convex closed domain the jets give actual C²
regularity all the way to the boundary, in the intrinsic within-domain
sense used by the Dirichlet Banach space. -/
theorem jet_contDiffOn_two_closed {S : Set E} (hS : Convex ℝ S)
    (hint : (interior S).Nonempty) {α : ℝ} (hα : 0 < α) (j : Jet E F hS α) :
    ContDiffOn ℝ 2 (extendValue α (jetValue E F hS α j)) S := by
  have hUD : UniqueDiffOn ℝ S := uniqueDiffOn_convex hS hint
  have hg : ContDiffOn ℝ 1 (extendValue α (jetFirst E F hS α j)) S := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderivWithin hUD]
    refine ⟨fun x hx => (jet_first_hasFDerivWithinAt hS hα j hx).differentiableWithinAt, ?_, ?_⟩
    · simp
    · rw [contDiffOn_zero]
      exact (continuousOn_extendValue α (jetSecond E F hS α j)).congr
        (fun x hx => (jet_first_hasFDerivWithinAt hS hα j hx).fderivWithin (hUD x hx))
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_fderivWithin hUD]
  refine ⟨fun x hx => (jet_hasFDerivWithinAt hS hα j hx).differentiableWithinAt, ?_, ?_⟩
  · simp
  · exact hg.congr (fun x hx => (jet_hasFDerivWithinAt hS hα j hx).fderivWithin (hUD x hx))

end GaussianTilt.HolderSpace
