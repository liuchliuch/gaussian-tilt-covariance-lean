import GaussianTilt.MomentMapLinearDirichletCampanatoL2Endpoint

/-! # Local L² data suffice for the actual boundary Campanato reconstruction -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma upperCampanatoBall_subset_large_halfBall (j : Fin n) {R : ℝ} (hR : 0 < R)
    {x : KernelSpace n} (hx : ‖x‖ ≤ R/4) (k : ℕ) :
    upperCampanatoBall j x (R*(1/2 : ℝ)^k) ⊆ upperCampanatoBall j 0 (2*R) := by
  intro z hz
  refine ⟨?_,hz.2⟩
  have hzk : ‖z-x‖ < R*(1/2 : ℝ)^k := by simpa only [Metric.mem_ball,dist_eq_norm] using hz.1
  have hk : R*(1/2 : ℝ)^k ≤ R := by
    have hh := pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1) (n := k)
    nlinarith
  have hn : ‖z‖ ≤ ‖z-x‖+‖x‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z-x) x
  rw [Metric.mem_ball,dist_zero_right]
  linarith

/-- Local square integrability on the containing half-ball and literal
mean-square approximation estimates construct an actual Hölder representative
on the closed smaller half-ball, with no global extension input. -/
theorem exists_holder_representative_of_local_l2_campanato [NeZero n] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (j : Fin n) (G : KernelSpace n → F) {R C α : ℝ}
    (hG : MemLp G 2 (volume.restrict (upperCampanatoBall j 0 (2*R))))
    (hR : 0 < R) (hC : 0 ≤ C) (hα : 0 < α)
    (hApprox : ∀ x : KernelSpace n, ‖x‖ ≤ R/4 → 0 ≤ x j → ∀ k : ℕ, ∃ q : F,
      (∫ z in upperCampanatoBall j x (R*(1/2 : ℝ)^k), ‖G z-q‖^2) ≤
        C*(R*(1/2 : ℝ)^k)^((n:ℝ)+2*α)) :
    ∃ L : KernelSpace n → F,
      ContinuousOn L (Metric.closedBall 0 (R/4) ∩ {x | 0 ≤ x j}) ∧
      (∀ᵐ x ∂volume, ‖x‖ ≤ R/4 → 0 < x j → L x = G x) ∧
      (∀ x : KernelSpace n, ‖x‖ ≤ R/4 → 0 ≤ x j →
        ∀ y : KernelSpace n, ‖y‖ ≤ R/4 → 0 ≤ y j →
          ‖L x-L y‖ ≤ campanatoL2HolderConstant n C α*‖x-y‖^α) := by
  let U := upperCampanatoBall j (0 : KernelSpace n) (2*R)
  let G₀ := U.indicator G
  have hU : MeasurableSet U := (isOpen_upperCampanatoBall j 0 (2*R)).measurableSet
  have hG₀ : MemLp G₀ 2 volume := (memLp_indicator_iff_restrict hU).mpr hG
  have hApp₀ : ∀ x : KernelSpace n, ‖x‖ ≤ R/4 → 0 ≤ x j → ∀ k : ℕ, ∃ q : F,
      (∫ z in upperCampanatoBall j x (R*(1/2 : ℝ)^k), ‖G₀ z-q‖^2) ≤
        C*(R*(1/2 : ℝ)^k)^((n:ℝ)+2*α) := by
    intro x hx hxj k
    obtain ⟨q,hq⟩ := hApprox x hx hxj k
    refine ⟨q,?_⟩
    have he : (∫ z in upperCampanatoBall j x (R*(1/2 : ℝ)^k), ‖G₀ z-q‖^2) =
        ∫ z in upperCampanatoBall j x (R*(1/2 : ℝ)^k), ‖G z-q‖^2 := by
      apply setIntegral_congr_fun (isOpen_upperCampanatoBall j x _).measurableSet
      intro z hz
      dsimp only
      have hzU := upperCampanatoBall_subset_large_halfBall j hR hx k hz
      rw [show G₀ z = G z from indicator_of_mem hzU G]
    rwa [he]
  obtain ⟨L,hLc,hAE,hHolder⟩ := exists_holder_representative_on_closed_halfBall j G₀ hG₀ hR hC hα hApp₀
  refine ⟨L,hLc,?_,hHolder⟩
  filter_upwards [hAE] with x hx
  intro hxn hxj
  have hxU : x ∈ U := by
    refine ⟨?_,hxj⟩
    rw [Metric.mem_ball,dist_zero_right]
    linarith
  rw [hx hxn hxj]
  exact indicator_of_mem hxU G

end GaussianTilt.MomentMapLinearDirichlet
