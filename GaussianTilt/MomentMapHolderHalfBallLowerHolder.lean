import GaussianTilt.MomentMapHolderHalfBallSmallInterpolation
import GaussianTilt.MomentMapHolderFixedExponentBounds

/-! # Lower Hölder terms are controlled by the value and a small highest norm -/
noncomputable section
set_option maxHeartbeats 1500000
open Set
open scoped Topology
namespace GaussianTilt.HolderSpace
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- Actual one-sided interpolation removes all lower-order terms from a
boundary Schauder estimate, with the radius/constant chosen before the jet. -/
theorem halfBall_jet_lower_holder_small_highest_norm
    (q : Fin n) {R α ε : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : Jet (KernelSpace n) ℝ (convex_flatClosedPatch q R) α)
      (U : ℝ), 0 ≤ U →
      (∀ y : flatClosedPatch q R,
        |value (flatClosedPatch q R) ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J) y| ≤ U) →
      let u := extendValue α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J)
      let D := extendValue α (jetFirst (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J)
      let H := extendValue α (jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J)
      let M := C*U+ε*‖jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J‖
      (∀ x ∈ flatClosedPatch q (R/2), ‖D x‖ ≤ M ∧ ‖H x‖ ≤ M) ∧
      (∀ x ∈ flatClosedPatch q (R/2), ∀ y ∈ flatClosedPatch q (R/2), |u x-u y| ≤ M*‖x-y‖^α) ∧
      (∀ x ∈ flatClosedPatch q (R/2), ∀ y ∈ flatClosedPatch q (R/2), ‖D x-D y‖ ≤ M*‖x-y‖^α) := by
  obtain ⟨L,hL,hest⟩ := halfBall_jet_derivatives_small_highest_norm q hR hα
    (show 0 < ε/4 by positivity)
  refine ⟨2*L+2, by positivity, ?_⟩
  intro J U hU hu
  dsimp only
  let S := flatClosedPatch q R
  let T := flatClosedPatch q (R/2)
  let u := extendValue α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J)
  let D := extendValue α (jetFirst (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J)
  let H := extendValue α (jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J)
  let N := ‖jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J‖
  let M := L*U+(ε/4)*N
  let B := (2*L+2)*U+ε*N
  have hN : 0 ≤ N := norm_nonneg _
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsub : T ⊆ S := by
    intro x hx
    exact ⟨Metric.closedBall_subset_closedBall (by linarith) hx.1, hx.2⟩
  have hfields (x : KernelSpace n) (hx : x ∈ T) : ‖D x‖ ≤ M ∧ ‖H x‖ ≤ M := by
    have hh := hest J U hU hu ⟨x,hsub hx⟩ (flat_patch_norm hx)
    simpa only [D,H,extendValue_mem α _ (hsub hx)] using hh
  have huv (x : T) : ‖u x‖ ≤ U := by
    rw [Real.norm_eq_abs]
    simpa only [u,extendValue_mem α _ (hsub x.2)] using hu ⟨x,hsub x.2⟩
  have huLip (x y : T) : ‖u x-u y‖ ≤ M*dist x y^(1:ℝ) := by
    have hh := (convex_flatClosedPatch q (R/2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (jet_hasFDerivWithinAt (convex_flatClosedPatch q R) hα J (hsub hz)).mono hsub)
      (fun z hz => (hfields z hz).1) y.2 x.2
    simpa only [u,D,Real.rpow_one,Subtype.dist_eq,dist_eq_norm] using hh
  have hDLip (x y : T) : ‖D x-D y‖ ≤ M*dist x y^(1:ℝ) := by
    have hh := (convex_flatClosedPatch q (R/2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (jet_first_hasFDerivWithinAt (convex_flatClosedPatch q R) hα J (hsub hz)).mono hsub)
      (fun z hz => (hfields z hz).2) y.2 x.2
    simpa only [u,D,Real.rpow_one,Subtype.dist_eq,dist_eq_norm] using hh
  have hMB : M ≤ B := by dsimp [M,B]; nlinarith
  have hUHB : max M (2*U) ≤ B := max_le hMB (by dsimp [B]; nlinarith)
  have hDHB : max M (2*M) ≤ B := max_le hMB (by dsimp [M,B]; nlinarith)
  refine ⟨fun x hx => ⟨((hfields x hx).1).trans hMB,((hfields x hx).2).trans hMB⟩, ?_, ?_⟩
  · intro x hx y hy
    have hh := holder_bound_of_bounded_and_higher_holder (fun z : T => u z) hα.le hα1 hU hM huv huLip ⟨x,hx⟩ ⟨y,hy⟩
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hUHB (Real.rpow_nonneg dist_nonneg α))
    simpa only [Real.norm_eq_abs,Subtype.dist_eq,dist_eq_norm] using hh'
  · intro x hx y hy
    have hh := holder_bound_of_bounded_and_higher_holder (fun z : T => D z) hα.le hα1 hM hM
      (fun z => (hfields z z.2).1) hDLip ⟨x,hx⟩ ⟨y,hy⟩
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hDHB (Real.rpow_nonneg dist_nonneg α))
    simpa only [Subtype.dist_eq,dist_eq_norm] using hh'

end GaussianTilt.HolderSpace
