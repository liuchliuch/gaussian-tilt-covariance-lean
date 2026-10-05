import GaussianTilt.MomentMapHolderTaylorRemainder
import GaussianTilt.MomentMapSchauderBoundaryPatchGeometry
import GaussianTilt.MomentMapCampanatoHalfBallJets

/-! # Genuine one-sided interpolation for closed half-ball Hölder jets -/
noncomputable section
set_option maxHeartbeats 1500000
open Set InnerProductSpace
open scoped Topology BigOperators
namespace GaussianTilt.HolderSpace
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma norm_continuousLinearMapOfBilin_real (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) :
    ‖continuousLinearMapOfBilin B‖ = ‖B‖ := by
  have he (v : KernelSpace n) : ‖continuousLinearMapOfBilin B v‖ = ‖B v‖ :=
    (toDual ℝ (KernelSpace n)).symm.norm_map _
  apply le_antisymm
  · apply (continuousLinearMapOfBilin B).opNorm_le_bound (norm_nonneg B)
    intro v
    rw [he]
    exact B.le_opNorm v
  · apply B.opNorm_le_bound (norm_nonneg _)
    intro v
    rw [← he]
    exact (continuousLinearMapOfBilin B).le_opNorm v

/-- No ambient boundary extension is used. The actual stored fields and
both FTC laws yield Taylor control on a genuine one-sided ball of increments,
then polynomial coefficient extraction gives the tunably small highest-norm term. -/
theorem halfBall_jet_derivative_interpolation
    (q : Fin n) {R α U r : ℝ} (hR : 0 < R) (hα : 0 < α) (hU : 0 ≤ U)
    (J : Jet (KernelSpace n) ℝ (convex_flatClosedPatch q R) α)
    (hu : ∀ y : flatClosedPatch q R,
      |value (flatClosedPatch q R) ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J) y| ≤ U)
    (hr : 0 < r) (hrR : r ≤ R/2)
    (x : flatClosedPatch q R) (hx : ‖(x : KernelSpace n)‖ ≤ R/2) :
    ‖value (flatClosedPatch q R) (KernelSpace n →L[ℝ] ℝ) α
      (jetFirst (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J) x‖ ≤
      36*U/r + 36*‖jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J‖*r^α*r ∧
    ‖value (flatClosedPatch q R) (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) α
      (jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J) x‖ ≤
      64*U/r^2 + 64*‖jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J‖*r^α := by
  let S := flatClosedPatch q R
  let a := value S ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J) x
  let D := value S (KernelSpace n →L[ℝ] ℝ) α (jetFirst (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J) x
  let B := value S (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) α
    (jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J) x
  let H := continuousLinearMapOfBilin B
  let p := (toDual ℝ (KernelSpace n)).symm D
  let T := ‖jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J‖
  have hT : 0 ≤ T := norm_nonneg _
  have hsym (v w : KernelSpace n) : inner ℝ (H v) w = inner ℝ v (H w) := by
    rw [real_inner_comm (H w) v]
    simp only [H, continuousLinearMapOfBilin_apply]
    exact jet_second_symmetric_closed (convex_flatClosedPatch q R) (isCompact_flatClosedPatch q R).isClosed
      (flatClosedPatch_nonempty_interior q hR) hα J x v w
  have hpoly (h : KernelSpace n) (hh : ‖h‖ ≤ r) (hq : 0 ≤ h q) :
      |quadraticJet a p 0 H h| ≤ U+T*r^α*r^2 := by
    have hyS : (x : KernelSpace n)+h ∈ S := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact (norm_add_le _ _).trans (by linarith)
      · change 0 ≤ (x : KernelSpace n) q+h q
        exact add_nonneg x.2.2 hq
    let y : S := ⟨(x : KernelSpace n)+h,hyS⟩
    let uy := value S ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J) y
    have hyx : (y : KernelSpace n)-x = h := by dsimp [y]; abel
    have ht := jet_quadratic_remainder_norm (convex_flatClosedPatch q R) hα.le J x y
    rw [hyx] at ht
    have hpD : inner ℝ p h = D h := toDual_symm_apply
    have hHB : inner ℝ (H h) h = B h h := continuousLinearMapOfBilin_apply _ _ _
    have ht' : |uy-quadraticJet a p 0 H h| ≤ T*‖h‖^α*‖h‖^2 := by
      simp only [quadraticJet,sub_zero,hpD,hHB]
      convert ht using 1 <;> dsimp only [a,D,B,T,uy] <;> congr 1 <;> ring
    have hpow := Real.rpow_le_rpow (norm_nonneg h) hh hα.le
    have hsq := (sq_le_sq₀ (norm_nonneg h) hr.le).mpr hh
    have htR : T*‖h‖^α*‖h‖^2 ≤ T*r^α*r^2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow hT) hsq (sq_nonneg _) (by positivity)
    have hv := abs_sub_le (quadraticJet a p 0 H h) uy 0
    simp only [sub_zero, abs_sub_comm (quadraticJet a p 0 H h) uy] at hv
    exact hv.trans (by linarith [ht'.trans htR, hu y])
  obtain ⟨_,hp,hH⟩ := quadraticJet_halfBall_coefficients q a p H hsym hr
    (show 0 ≤ U+T*r^α*r^2 by positivity) hpoly
  have hpn : ‖p‖=‖D‖ := (toDual ℝ (KernelSpace n)).symm.norm_map D
  have hHn : ‖H‖=‖B‖ := norm_continuousLinearMapOfBilin_real B
  rw [hpn] at hp
  rw [hHn] at hH
  constructor
  · exact hp.trans_eq (by dsimp only [T]; field_simp <;> ring)
  · exact hH.trans_eq (by dsimp only [T]; field_simp <;> ring)

end GaussianTilt.HolderSpace
