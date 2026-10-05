import GaussianTilt.MomentMapClassicalDirichletIntrinsicJets
import GaussianTilt.MomentMapClassicalDirichletLocalExtension
import GaussianTilt.MomentMapClassicalDirichletGlobalHessian

/-!
# Actual interior calculus for intrinsic Hölder jets

Constructed compact cutoffs supply local smooth representatives only where
the source is genuinely smooth. The intrinsic fields agree with the true
interior derivatives and are continuous up to the actual boundary.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

def intrinsicDerivative {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) (i : Fin n) (x : CoordinateSpace n) : ℝ :=
  intrinsicFirst hS α j x (Pi.single i 1)

def intrinsicHessian {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) (x : CoordinateSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i l => intrinsicSecond hS α j x (Pi.single l 1) (Pi.single i 1)

lemma intrinsicHessian_eq_stored {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) (x : S) : intrinsicHessian hS α j x = hessianMatrix hS α j x := by
  ext i l
  simp only [intrinsicHessian,intrinsicSecond,extendValue_mem α _ x.2]
  rfl

lemma intrinsicDerivative_eq_actual {S : Set (CoordinateSpace n)} (hS : Convex ℝ S)
    {α : ℝ} (hα : 0 < α) (j : Jet (CoordinateSpace n) ℝ hS α)
    {x : CoordinateSpace n} (hx : x ∈ interior S) (i : Fin n) :
    intrinsicDerivative hS α j i x = coordinateDerivative i (intrinsicValue hS α j) x := by
  exact congrArg (fun D : CoordinateSpace n →L[ℝ] ℝ => D (Pi.single i 1))
    (jet_hasFDerivAt hS hα j hx).fderiv.symm

lemma intrinsicHessian_eq_actual {S : Set (CoordinateSpace n)} (hS : Convex ℝ S)
    {α : ℝ} (hα : 0 < α) (j : Jet (CoordinateSpace n) ℝ hS α)
    {x : CoordinateSpace n} (hx : x ∈ interior S) :
    intrinsicHessian hS α j x = coordinateHessian (intrinsicValue hS α j) x := by
  exact (intrinsicHessian_eq_stored hS α j ⟨x,interior_subset hx⟩).trans
    (hessianMatrix_eq_actual hS hα j ⟨x,interior_subset hx⟩ hx)

lemma continuousOn_intrinsicDerivative {S : Set (CoordinateSpace n)} (hS : Convex ℝ S)
    (α : ℝ) (j : Jet (CoordinateSpace n) ℝ hS α) (i : Fin n) :
    ContinuousOn (intrinsicDerivative hS α j i) S :=
  (continuousOn_extendValue α (jetFirst (CoordinateSpace n) ℝ hS α j)).clm_apply continuousOn_const

lemma continuousOn_intrinsicHessian_entry {S : Set (CoordinateSpace n)} (hS : Convex ℝ S)
    (α : ℝ) (j : Jet (CoordinateSpace n) ℝ hS α) (i l : Fin n) :
    ContinuousOn (fun x => intrinsicHessian hS α j x i l) S :=
  ((continuousOn_extendValue α (jetSecond (CoordinateSpace n) ℝ hS α j)).clm_apply continuousOn_const).clm_apply continuousOn_const

/-- A genuine local global representative for an intrinsically smooth
interior jet, including equality of its actual first and second fields. -/
theorem intrinsic_exists_smooth_representative_at
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S))
    {x : CoordinateSpace n} (hx : x ∈ interior S) :
    ∃ u : CoordinateSpace n → ℝ, ContDiff ℝ ∞ u ∧
      u =ᶠ[𝓝 x] intrinsicValue hS α j ∧
      (∀ i, intrinsicDerivative hS α j i =ᶠ[𝓝 x] coordinateDerivative i u) ∧
      intrinsicHessian hS α j =ᶠ[𝓝 x] coordinateHessian u := by
  obtain ⟨u,hu,he⟩ := exists_global_smooth_coordinate_eq_near_compact isOpen_interior hs
    (isCompact_singleton (x := x)) (singleton_subset_iff.mpr hx)
  have he' := he x (mem_singleton x)
  refine ⟨u,hu,he',?_,?_⟩
  · intro i
    filter_upwards [isOpen_interior.mem_nhds hx,he'.eventually_nhds] with y hy hey
    rw [intrinsicDerivative_eq_actual hS hα j hy]
    exact (coordinateDerivative_congr_nhds hey i).symm
  · filter_upwards [isOpen_interior.mem_nhds hx,he'.eventually_nhds] with y hy hey
    rw [intrinsicHessian_eq_actual hS hα j hy]
    exact (coordinateHessian_congr_nhds hey).symm

lemma contDiffAt_intrinsicDerivative {S : Set (CoordinateSpace n)} (hS : Convex ℝ S)
    {α : ℝ} (hα : 0 < α) (j : Jet (CoordinateSpace n) ℝ hS α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S))
    {x : CoordinateSpace n} (hx : x ∈ interior S) (i : Fin n) :
    ContDiffAt ℝ ∞ (intrinsicDerivative hS α j i) x := by
  obtain ⟨u,hu,he,hD,hH⟩ := intrinsic_exists_smooth_representative_at hS hα j hs hx
  exact (smooth_coordinateDerivative hu i).contDiffAt.congr_of_eventuallyEq (hD i)

lemma contDiffAt_intrinsicHessian_entry {S : Set (CoordinateSpace n)} (hS : Convex ℝ S)
    {α : ℝ} (hα : 0 < α) (j : Jet (CoordinateSpace n) ℝ hS α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S))
    {x : CoordinateSpace n} (hx : x ∈ interior S) (i l : Fin n) :
    ContDiffAt ℝ ∞ (fun x => intrinsicHessian hS α j x i l) x := by
  obtain ⟨u,hu,he,hD,hH⟩ := intrinsic_exists_smooth_representative_at hS hα j hs hx
  exact (smooth_coordinateHessian hu i l).contDiffAt.congr_of_eventuallyEq
    (hH.mono (fun y hy => congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i l) hy))

/-- The exact first-field PDE holds for intrinsic jets smooth only inside
the domain; no boundary smooth extension is a premise. -/
theorem intrinsic_linearized_first_identity
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S))
    {F : CoordinateSpace n → ℝ}
    (hMA : ∀ y ∈ interior S, (intrinsicHessian hS α j y).det = Real.exp (F y))
    {x : CoordinateSpace n} (hx : x ∈ interior S) (i : Fin n) :
    linearizedMA (intrinsicHessian hS α j x)⁻¹ (intrinsicDerivative hS α j i) x = coordinateDerivative i F x := by
  obtain ⟨u,hu,he,hD,hH⟩ := intrinsic_exists_smooth_representative_at hS hα j hs hx
  have hnear : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y) := by
    filter_upwards [isOpen_interior.mem_nhds hx,hH] with y hy hey
    rw [← hey]
    exact hMA y hy
  rw [hH.self_of_nhds]
  unfold linearizedMA
  rw [coordinateHessian_congr_nhds (hD i)]
  exact linearizedMA_coordinateDerivative_variable_density hu hnear i

/-- The true twice-differentiated diagonal inequality also localizes to the
intrinsic second field, whose boundary values remain the jet values. -/
theorem intrinsic_linearized_hessian_diagonal_lower
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S))
    {F : CoordinateSpace n → ℝ} (hF : ContDiff ℝ ∞ F)
    (hMA : ∀ y ∈ interior S, (intrinsicHessian hS α j y).det = Real.exp (F y))
    {x : CoordinateSpace n} (hx : x ∈ interior S) (hp : (intrinsicHessian hS α j x).PosDef) (i : Fin n) :
    coordinateHessian F x i i ≤ linearizedMA (intrinsicHessian hS α j x)⁻¹
      (fun y => intrinsicHessian hS α j y i i) x := by
  obtain ⟨u,hu,he,hD,hH⟩ := intrinsic_exists_smooth_representative_at hS hα j hs hx
  have hnear : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y) := by
    filter_upwards [isOpen_interior.mem_nhds hx,hH] with y hy hey
    rw [← hey]
    exact hMA y hy
  rw [hH.self_of_nhds] at hp ⊢
  unfold linearizedMA
  rw [coordinateHessian_congr_nhds (hH.mono (fun y hy => congrArg
    (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) hy))]
  exact linearizedMA_hessian_diagonal_lower hu hF hp hnear i

end GaussianTilt.MomentMapRegularity
