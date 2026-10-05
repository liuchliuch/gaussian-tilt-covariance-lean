import GaussianTilt.MomentMapLinearDirichletCampanatoL2Local

/-! # Actual radius interpolation of mean-square boundary estimates -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma upperCampanatoBall_subset_large_halfBall_of_radius (j : Fin n) {R r : ℝ}
    (hR : 0 < R) (hrR : r ≤ R) {x : KernelSpace n} (hx : ‖x‖ ≤ R/4) :
    upperCampanatoBall j x r ⊆ upperCampanatoBall j 0 (2*R) := by
  intro z hz
  refine ⟨?_,hz.2⟩
  have hzk : ‖z-x‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hz.1
  have hn : ‖z‖ ≤ ‖z-x‖+‖x‖ := by simpa only [sub_add_cancel] using norm_add_le (z-x) x
  rw [Metric.mem_ball,dist_zero_right]
  linarith

lemma local_memLp_square_error_halfBall {F : Type*} [NormedAddCommGroup F]
    (j : Fin n) {G : KernelSpace n → F} {R r : ℝ}
    (hG : MemLp G 2 (volume.restrict (upperCampanatoBall j 0 (2*R))))
    (hR : 0 < R) (hrR : r ≤ R) {x : KernelSpace n} (hx : ‖x‖ ≤ R/4) (q : F) :
    IntegrableOn (fun z => ‖G z-q‖^2) (upperCampanatoBall j x r) := by
  have hsub := upperCampanatoBall_subset_large_halfBall_of_radius j hR hrR hx
  have hGL : MemLp G 2 (volume.restrict (upperCampanatoBall j x r)) :=
    hG.mono_measure (Measure.restrict_mono_set volume hsub)
  haveI : Fact (volume (upperCampanatoBall j x r) < ∞) := ⟨(upperCampanatoBall_finite j x r).lt_top⟩
  exact (hGL.sub (memLp_const q)).integrable_norm_pow (p := 2) (by norm_num)

/-- Geometric mean-square bounds at any true contraction ratio interpolate
to every smaller radius, with the actual dimensional/exponent loss. -/
theorem l2_campanato_geometric_to_all_radii {F : Type*} [NormedAddCommGroup F]
    (j : Fin n) (G : KernelSpace n → F) {R ρ C α : ℝ}
    (hG : MemLp G 2 (volume.restrict (upperCampanatoBall j 0 (2*R))))
    (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (x : KernelSpace n) (hx : ‖x‖ ≤ R/4)
    (hApprox : ∀ k : ℕ, ∃ q : F,
      (∫ z in upperCampanatoBall j x (R*ρ^k), ‖G z-q‖^2) ≤ C*(R*ρ^k)^((n:ℝ)+2*α)) :
    ∀ r : ℝ, 0 < r → r ≤ R → ∃ q : F,
      (∫ z in upperCampanatoBall j x r, ‖G z-q‖^2) ≤
        (C*ρ^(-((n:ℝ)+2*α)))*r^((n:ℝ)+2*α) := by
  intro r hr hrR
  obtain ⟨k,hkl,hku⟩ := exists_nat_pow_near_of_lt_one (div_pos hr hR)
    ((div_le_one hR).mpr hrR) hρ hρ1
  obtain ⟨q,hq⟩ := hApprox k
  have hRk : 0 < R*ρ^k := mul_pos hR (pow_pos hρ _)
  have hkR : R*ρ^k ≤ R := by
    have hh := pow_le_one₀ hρ.le hρ1.le (n := k)
    nlinarith
  have hrk : r ≤ R*ρ^k := by have hh := (div_le_iff₀ hR).mp hku; nlinarith
  have hkr : R*ρ^k ≤ r/ρ := by
    have hh := (lt_div_iff₀ hR).mp hkl
    rw [pow_succ] at hh
    apply (le_div_iff₀ hρ).mpr
    nlinarith
  have hs : upperCampanatoBall j x r ⊆ upperCampanatoBall j x (R*ρ^k) :=
    upperCampanatoBall_mono (by simpa only [dist_self,zero_add] using hrk)
  have hI := local_memLp_square_error_halfBall j hG hR hkR hx q
  refine ⟨q,?_⟩
  have hm := setIntegral_mono_set hI (ae_of_all _ (fun z => sq_nonneg ‖G z-q‖))
    (ae_of_all _ (fun _ hz => hs hz))
  apply (hm.trans hq).trans
  have hp := Real.rpow_le_rpow hRk.le hkr (by positivity : 0 ≤ (n:ℝ)+2*α)
  have hb := mul_le_mul_of_nonneg_left hp hC
  rw [Real.div_rpow hr.le hρ.le] at hb
  convert hb using 1
  rw [Real.rpow_neg hρ.le]
  ring

/-- The natural local L² reconstruction accepts any geometric decay scale,
not only a preselected dyadic one. -/
theorem exists_holder_representative_of_geometric_l2_campanato [NeZero n] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (j : Fin n) (G : KernelSpace n → F) {R ρ C α : ℝ}
    (hG : MemLp G 2 (volume.restrict (upperCampanatoBall j 0 (2*R))))
    (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C) (hα : 0 < α)
    (hApprox : ∀ x : KernelSpace n, ‖x‖ ≤ R/4 → 0 ≤ x j → ∀ k : ℕ, ∃ q : F,
      (∫ z in upperCampanatoBall j x (R*ρ^k), ‖G z-q‖^2) ≤ C*(R*ρ^k)^((n:ℝ)+2*α)) :
    ∃ L : KernelSpace n → F,
      ContinuousOn L (Metric.closedBall 0 (R/4) ∩ {x | 0 ≤ x j}) ∧
      (∀ᵐ x ∂volume, ‖x‖ ≤ R/4 → 0 < x j → L x = G x) ∧
      (∀ x : KernelSpace n, ‖x‖ ≤ R/4 → 0 ≤ x j →
        ∀ y : KernelSpace n, ‖y‖ ≤ R/4 → 0 ≤ y j →
          ‖L x-L y‖ ≤ campanatoL2HolderConstant n (C*ρ^(-((n:ℝ)+2*α))) α*‖x-y‖^α) := by
  apply exists_holder_representative_of_local_l2_campanato j G hG hR (by positivity) hα
  intro x hx hxj k
  apply l2_campanato_geometric_to_all_radii j G hG hR hρ hρ1 hC hα.le x hx (hApprox x hx hxj)
    (R*(1/2 : ℝ)^k) (by positivity)
  have hp := pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1) (n := k)
  nlinarith

end GaussianTilt.MomentMapLinearDirichlet
