import GaussianTilt.MomentMapSchauderInteriorJetInterpolation
import GaussianTilt.MomentMapHolderFixedExponentBounds

/-! # Interior lower Hölder norms with a tunably small highest norm -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 1800000
open Set
open scoped Topology
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.HolderSpace
variable {n : ℕ}

/-- All local lower-jet terms are controlled by the actual value bound
and any prescribed small multiple of the global highest jet norm. -/
theorem interior_jet_lower_holder_small_highest {R α ε : ℝ}
    (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Set (KernelSpace n)) (hS : Convex ℝ S) (hSc : IsClosed S)
      (hint : (interior S).Nonempty) (a : KernelSpace n), Metric.closedBall a R ⊆ S →
      ∀ (J : Jet (KernelSpace n) ℝ hS α) (U : ℝ), 0 ≤ U →
      (∀ y : S, |value S ℝ α (jetValue (KernelSpace n) ℝ hS α J) y| ≤ U) →
      let u := extendValue α (jetValue (KernelSpace n) ℝ hS α J)
      let D := extendValue α (jetFirst (KernelSpace n) ℝ hS α J)
      let B := extendValue α (jetSecond (KernelSpace n) ℝ hS α J)
      let M := C*U+ε*‖jetSecond (KernelSpace n) ℝ hS α J‖
      (∀ x ∈ Metric.closedBall a (R/2), ‖D x‖ ≤ M ∧ ‖B x‖ ≤ M) ∧
      (∀ x ∈ Metric.closedBall a (R/2), ∀ y ∈ Metric.closedBall a (R/2), |u x-u y| ≤ M*‖x-y‖^α) ∧
      (∀ x ∈ Metric.closedBall a (R/2), ∀ y ∈ Metric.closedBall a (R/2), ‖D x-D y‖ ≤ M*‖x-y‖^α) := by
  obtain ⟨L,hL,hest⟩ := interior_jet_derivatives_small_highest (n := n) hR hα (show 0 < ε/4 by positivity)
  refine ⟨2*L+2,by positivity,?_⟩
  intro S hS hSc hint a hball J U hU hu
  dsimp only
  let T := Metric.closedBall a (R/2)
  let u := extendValue α (jetValue (KernelSpace n) ℝ hS α J)
  let D := extendValue α (jetFirst (KernelSpace n) ℝ hS α J)
  let B := extendValue α (jetSecond (KernelSpace n) ℝ hS α J)
  let N := ‖jetSecond (KernelSpace n) ℝ hS α J‖
  let M := L*U+(ε/4)*N
  let Q := (2*L+2)*U+ε*N
  have hN : 0 ≤ N := norm_nonneg _
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hsub : T ⊆ S := (Metric.closedBall_subset_closedBall (by linarith : R/2 ≤ R)).trans hball
  have hfields (x : KernelSpace n) (hx : x ∈ T) : ‖D x‖ ≤ M ∧ ‖B x‖ ≤ M := by
    have hh := hest S hS hSc hint a hball J U hU hu ⟨x,hsub hx⟩
      (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
    simpa only [D,B,extendValue_mem α _ (hsub hx)] using hh
  have huv (x : T) : ‖u x‖ ≤ U := by
    rw [Real.norm_eq_abs]
    simpa only [u,extendValue_mem α _ (hsub x.2)] using hu ⟨x,hsub x.2⟩
  have huLip (x y : T) : ‖u x-u y‖ ≤ M*dist x y^(1:ℝ) := by
    have hh := (convex_closedBall a (R/2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (jet_hasFDerivWithinAt hS hα J (hsub hz)).mono hsub)
      (fun z hz => (hfields z hz).1) y.2 x.2
    simpa only [u,D,Real.rpow_one,Subtype.dist_eq,dist_eq_norm] using hh
  have hDLip (x y : T) : ‖D x-D y‖ ≤ M*dist x y^(1:ℝ) := by
    have hh := (convex_closedBall a (R/2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (jet_first_hasFDerivWithinAt hS hα J (hsub hz)).mono hsub)
      (fun z hz => (hfields z hz).2) y.2 x.2
    simpa only [D,B,Real.rpow_one,Subtype.dist_eq,dist_eq_norm] using hh
  have hMQ : M ≤ Q := by dsimp [M,Q]; nlinarith
  have hUHQ : max M (2*U) ≤ Q := max_le hMQ (by dsimp [Q]; nlinarith)
  have hDHQ : max M (2*M) ≤ Q := max_le hMQ (by dsimp [M,Q]; nlinarith)
  refine ⟨fun x hx => ⟨((hfields x hx).1).trans hMQ,((hfields x hx).2).trans hMQ⟩,?_,?_⟩
  · intro x hx y hy
    have hh := holder_bound_of_bounded_and_higher_holder (fun z : T => u z) hα.le hα1 hU hM huv huLip ⟨x,hx⟩ ⟨y,hy⟩
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hUHQ (Real.rpow_nonneg dist_nonneg α))
    simpa only [Real.norm_eq_abs,Subtype.dist_eq,dist_eq_norm] using hh'
  · intro x hx y hy
    have hh := holder_bound_of_bounded_and_higher_holder (fun z : T => D z) hα.le hα1 hM hM
      (fun z => (hfields z z.2).1) hDLip ⟨x,hx⟩ ⟨y,hy⟩
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hDHQ (Real.rpow_nonneg dist_nonneg α))
    simpa only [Subtype.dist_eq,dist_eq_norm] using hh'

end GaussianTilt.MomentMapSchauder
