import GaussianTilt.MomentMapLinearDirichletCampanatoL2Representative
import GaussianTilt.MomentMapSchauderBoundaryGluing

/-! # The natural L² Campanato theorem with actual existential approximants -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma memLp_square_error_upperBall {F : Type*} [NormedAddCommGroup F]
    {G : KernelSpace n → F} (hG : MemLp G 2 volume) (q : F)
    (j : Fin n) (x : KernelSpace n) (r : ℝ) :
    IntegrableOn (fun z => ‖G z-q‖^2) (upperCampanatoBall j x r) := by
  haveI : Fact (volume (upperCampanatoBall j x r) < ∞) := ⟨(upperCampanatoBall_finite j x r).lt_top⟩
  have hq : MemLp (fun _ : KernelSpace n => q) 2 (volume.restrict (upperCampanatoBall j x r)) := memLp_const q
  exact ((hG.restrict _).sub hq).integrable_norm_pow (p := 2) (by norm_num)

/-- Literal local mean-square approximation constants are chosen, proved
coherent, and identified AE with a continuous Hölder field on the closed
half-space patch. No approximating sequence is an extra input. -/
theorem exists_holder_representative_of_l2_campanato [NeZero n] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (j : Fin n) (G : KernelSpace n → F) {S : Set (KernelSpace n)} {R C α : ℝ}
    (hG : MemLp G 2 volume) (hR : 0 < R) (hC : 0 ≤ C) (hα : 0 < α)
    (hS : ∀ x ∈ S, 0 ≤ x j)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ R/2)
    (hApprox : ∀ x ∈ S, ∀ k : ℕ, ∃ q : F,
      (∫ z in upperCampanatoBall j x (R*(1/2 : ℝ)^k), ‖G z-q‖^2) ≤
        C*(R*(1/2 : ℝ)^k)^((n:ℝ)+2*α)) :
    ∃ L : KernelSpace n → F, ContinuousOn L S ∧
      (∀ᵐ x ∂volume, x ∈ S → 0 < x j → L x = G x) ∧
      (∀ x ∈ S, ∀ y ∈ S, ‖L x-L y‖ ≤ campanatoL2HolderConstant n C α*‖x-y‖^α) := by
  classical
  have hex : ∀ x : S, ∀ k : ℕ, ∃ q : F,
      (∫ z in upperCampanatoBall j x (R*(1/2 : ℝ)^k), ‖G z-q‖^2) ≤
        C*(R*(1/2 : ℝ)^k)^((n:ℝ)+2*α) := fun x => hApprox x x.property
  choose q hq using hex
  let p := fun x : KernelSpace n => fun k : ℕ => if hx : x ∈ S then q ⟨x,hx⟩ k else 0
  have hE : ∀ x ∈ S, ∀ k : ℕ,
      (∫ z in upperCampanatoBall j x (R*(1/2 : ℝ)^k), ‖G z-p x k‖^2) ≤
        C*(R*(1/2 : ℝ)^k)^((n:ℝ)+2*α) := by
    intro x hx k
    simpa only [p,dif_pos hx] using hq ⟨x,hx⟩ k
  obtain ⟨L,hAE,hlim,hHolder⟩ := exists_l2_campanato_holder_representative j G p
    (hG.locallyIntegrable (by norm_num)) hR hC hα hS hdiam
    (fun x _ k => memLp_square_error_upperBall hG (p x k) j x _) hE
  exact ⟨L,continuousOn_of_norm_holder_bound hα hHolder,hAE,hHolder⟩

/-- The geometric closed half-ball version used by the actual boundary
energy iteration, with all center/radius containment conditions explicit. -/
theorem exists_holder_representative_on_closed_halfBall [NeZero n] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (j : Fin n) (G : KernelSpace n → F) {R C α : ℝ}
    (hG : MemLp G 2 volume) (hR : 0 < R) (hC : 0 ≤ C) (hα : 0 < α)
    (hApprox : ∀ x : KernelSpace n, ‖x‖ ≤ R/4 → 0 ≤ x j → ∀ k : ℕ, ∃ q : F,
      (∫ z in upperCampanatoBall j x (R*(1/2 : ℝ)^k), ‖G z-q‖^2) ≤
        C*(R*(1/2 : ℝ)^k)^((n:ℝ)+2*α)) :
    ∃ L : KernelSpace n → F,
      ContinuousOn L (Metric.closedBall 0 (R/4) ∩ {x | 0 ≤ x j}) ∧
      (∀ᵐ x ∂volume, ‖x‖ ≤ R/4 → 0 < x j → L x = G x) ∧
      (∀ x : KernelSpace n, ‖x‖ ≤ R/4 → 0 ≤ x j →
        ∀ y : KernelSpace n, ‖y‖ ≤ R/4 → 0 ≤ y j →
          ‖L x-L y‖ ≤ campanatoL2HolderConstant n C α*‖x-y‖^α) := by
  let S : Set (KernelSpace n) := Metric.closedBall 0 (R/4) ∩ {x | 0 ≤ x j}
  have hmem (x : KernelSpace n) : x ∈ S ↔ ‖x‖ ≤ R/4 ∧ 0 ≤ x j := by
    simp only [S,mem_inter_iff,Metric.mem_closedBall,dist_zero_right,mem_setOf_eq]
  obtain ⟨L,hLc,hAE,hHolder⟩ := exists_holder_representative_of_l2_campanato j G hG hR hC hα
    (S := S) (fun x hx => ((hmem x).mp hx).2) (by
      intro x hx y hy
      have hx' := ((hmem x).mp hx).1
      have hy' := ((hmem y).mp hy).1
      have ht := norm_sub_le x y
      linarith)
    (fun x hx => hApprox x ((hmem x).mp hx).1 ((hmem x).mp hx).2)
  refine ⟨L,hLc,?_,?_⟩
  · filter_upwards [hAE] with x hx
    intro hxn hxj
    exact hx ((hmem x).mpr ⟨hxn,hxj.le⟩) hxj
  · intro x hxn hxj y hyn hyj
    exact hHolder x ((hmem x).mpr ⟨hxn,hxj⟩) y ((hmem y).mpr ⟨hyn,hyj⟩)

end GaussianTilt.MomentMapLinearDirichlet
