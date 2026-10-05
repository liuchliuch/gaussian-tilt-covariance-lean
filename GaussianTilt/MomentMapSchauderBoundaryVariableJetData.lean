import GaussianTilt.MomentMapSchauderBoundaryVariableFirstJet
import GaussianTilt.MomentMapHolderHalfBallLowerHolder

/-! # Actual zero-extension data furnished by a closed Hölder boundary jet -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000
open Set InnerProductSpace
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.HolderSpace
variable {n : ℕ}

/-- A true compatible jet with zero flat trace supplies the zero extension,
local C² regularity, true interior derivatives and linear boundary growth
needed by the derived variable-coefficient estimate. -/
theorem flat_zero_jet_classical_data (j : Fin n) {R α : ℝ} (hR : 0 < R) (hα : 0 < α)
    (J : Jet (KernelSpace n) ℝ (convex_flatClosedPatch j R) α)
    (hzero : ∀ x : flatClosedPatch j R, (x : KernelSpace n) j=0 →
      value (flatClosedPatch j R) ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J) x=0) :
    let u := extendValue α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J)
    let D := extendValue α (jetFirst (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J)
    let B := extendValue α (jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J)
    (∀ x, x j ≤ 0 → u x=0) ∧ ContDiffOn ℝ 2 u (flatUpperBall j R) ∧
    (∀ x ∈ flatUpperBall j R, D x=fderiv ℝ u x) ∧
    (∀ x ∈ flatUpperBall j R, B x=fderiv ℝ (fderiv ℝ u) x) ∧
    BoundedHolderOn α B (flatClosedPatch j R) ∧
    (∀ x ∈ Metric.ball (0 : KernelSpace n) (R/2), |u x| ≤
      ‖jetFirst (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J‖*|x j|) := by
  dsimp only
  let S := flatClosedPatch j R
  let u := extendValue α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J)
  let D := jetFirst (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J
  let B := jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J
  have hu0 : ∀ x, x j ≤ 0 → u x=0 := by
    intro x hx
    by_cases hxS : x ∈ S
    · rw [show u x=value S ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J) ⟨x,hxS⟩ from extendValue_mem α _ hxS]
      exact hzero ⟨x,hxS⟩ (le_antisymm hx hxS.2)
    · exact dif_neg hxS
  have hmap : flatUpperBall j R ⊆ interior S := by
    intro x hx
    exact flatClosedPatch_mem_interior (by simpa only [Metric.mem_ball,dist_zero_right] using hx.1) hx.2
  refine ⟨hu0,(jet_contDiffOn_two (convex_flatClosedPatch j R) hα J).mono hmap,
    fun x hx => (jet_hasFDerivAt (convex_flatClosedPatch j R) hα J (hmap hx)).fderiv.symm,
    fun x hx => (jet_second_eq_fderiv_fderiv (convex_flatClosedPatch j R) hα J (hmap hx)).symm,?_,?_⟩
  · refine ⟨‖B‖,norm_nonneg _,?_,?_⟩
    · intro x hx
      rw [extendValue_mem α B hx]
      exact norm_value_apply_le S _ α B ⟨x,hx⟩
    · intro x hx y hy
      rw [extendValue_mem α B hx,extendValue_mem α B hy]
      exact norm_value_sub_le S _ α B ⟨x,hx⟩ ⟨y,hy⟩
  · intro x hx
    change |u x| ≤ ‖D‖*|x j|
    by_cases hxj : x j ≤ 0
    · rw [hu0 x hxj,abs_zero]
      positivity
    · have hxpos : 0 < x j := lt_of_not_ge hxj
      have hn : ‖x‖ < R/2 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
      have hxS : x ∈ S := ⟨by rw [Metric.mem_closedBall,dist_zero_right]; linarith,hxpos.le⟩
      let z := flatProjection j x
      have hzS : z ∈ S := by
        refine ⟨?_,?_⟩
        · rw [Metric.mem_closedBall,dist_zero_right]
          have ht := norm_flatProjection_le j x
          dsimp [z]
          linarith
        · change 0 ≤ z j
          simp only [show z j=0 from flatProjection_plane j x,le_refl]
      have hzu : value S ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J) ⟨z,hzS⟩=0 :=
        hzero ⟨z,hzS⟩ (flatProjection_plane j x)
      have hftc := (jet_ftc (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J ⟨z,hzS⟩ ⟨x,hxS⟩).1
      rw [hzu,sub_zero] at hftc
      rw [show u x=value S ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J) ⟨x,hxS⟩ from extendValue_mem α _ hxS,hftc]
      have hb := segmentIntegralLinear_norm_bound (convex_flatClosedPatch j R) α ⟨z,hzS⟩ ⟨x,hxS⟩ D
      simpa only [Real.norm_eq_abs,z,norm_sub_flatProjection_eq,mul_comm] using hb

end GaussianTilt.MomentMapSchauder
