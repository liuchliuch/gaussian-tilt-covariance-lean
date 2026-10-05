import GaussianTilt.MomentMapLinearDirichletCampanatoL2Limits

/-! # Hölder compatibility of actual mean-square Campanato limits -/
noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def campanatoL2StepConstant (n : ℕ) (C : ℝ) : ℝ :=
  2*Real.sqrt (C/(campanatoHalfBallVolume n*(1/2 : ℝ)^n))

def campanatoL2HolderConstant (n : ℕ) (C α : ℝ) : ℝ :=
  (2*(campanatoL2StepConstant n C/(1-(1/2 : ℝ)^α))+campanatoL2StepConstant n C)*4^α

/-- Actual L² approximants at two centers have Hölder-close limits.
The common comparison set is a genuine half-radius truncated ball. -/
theorem l2_campanato_limits_holder [NeZero n] {F : Type*}
    [NormedAddCommGroup F] [CompleteSpace F]
    (j : Fin n) (G : KernelSpace n → F) (x y : KernelSpace n)
    (hx : 0 ≤ x j) (hy : 0 ≤ y j) (px py : ℕ → F) (gx gy : F)
    {R C α : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hα : 0 < α)
    (hd : ‖x-y‖ ≤ R/2) (hdpos : 0 < ‖x-y‖)
    (hIx : ∀ k, IntegrableOn (fun z => ‖G z-px k‖^2) (upperCampanatoBall j x (R*(1/2 : ℝ)^k)))
    (hIy : ∀ k, IntegrableOn (fun z => ‖G z-py k‖^2) (upperCampanatoBall j y (R*(1/2 : ℝ)^k)))
    (hEx : ∀ k, (∫ z in upperCampanatoBall j x (R*(1/2 : ℝ)^k), ‖G z-px k‖^2) ≤
      C*(R*(1/2 : ℝ)^k)^((n:ℝ)+2*α))
    (hEy : ∀ k, (∫ z in upperCampanatoBall j y (R*(1/2 : ℝ)^k), ‖G z-py k‖^2) ≤
      C*(R*(1/2 : ℝ)^k)^((n:ℝ)+2*α))
    (hpx : Tendsto px atTop (𝓝 gx)) (hpy : Tendsto py atTop (𝓝 gy)) :
    ‖gx-gy‖ ≤ campanatoL2HolderConstant n C α*‖x-y‖^α := by
  obtain ⟨gx',hpx',htx⟩ := exists_l2_campanato_geometric_limit j x hx G px hR
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1) hC hα hIx hEx
  obtain ⟨gy',hpy',hty⟩ := exists_l2_campanato_geometric_limit j y hy G py hR
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1) hC hα hIy hEy
  have hex := tendsto_nhds_unique hpx' hpx
  have hey := tendsto_nhds_unique hpy' hpy
  subst gx'; subst gy'
  let d := ‖x-y‖
  have hd0 : 0 < d := hdpos
  have hRatio : 0 < 2*d/R := div_pos (by positivity) hR
  have hRatio1 : 2*d/R ≤ 1 := (div_le_one hR).mpr (by dsimp [d]; linarith)
  obtain ⟨k,hkl,hku⟩ := exists_nat_pow_near_of_lt_one hRatio hRatio1
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  let r := R*(1/2 : ℝ)^k
  have hr : 0 < r := mul_pos hR (pow_pos (by norm_num) _)
  have hdr : 2*d ≤ r := by
    have hh := (div_le_iff₀ hR).mp hku
    dsimp [r]; nlinarith
  have hrd : r ≤ 4*d := by
    have hh := (lt_div_iff₀ hR).mp hkl
    rw [pow_succ] at hh
    dsimp [r]; nlinarith
  have hSx : upperCampanatoBall j x ((1/2)*r) ⊆ upperCampanatoBall j x r := by
    apply upperCampanatoBall_mono
    simp only [dist_self,zero_add]
    linarith
  have hSy : upperCampanatoBall j x ((1/2)*r) ⊆ upperCampanatoBall j y r := by
    apply upperCampanatoBall_mono
    rw [dist_eq_norm]
    change d+1/2*r ≤ r
    linarith
  have hxy := l2_campanato_coherence_at_scale j x hx G (px k) (py k) hr
    (by norm_num : (0:ℝ)<1/2) hC hSx hSy (hIx k) (hIy k) (hEx k) (hEy k)
  let K := campanatoL2StepConstant n C
  have hK : 0 ≤ K := by dsimp [K,campanatoL2StepConstant]; positivity
  have hq : (1/2 : ℝ)^α < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have htpos : 0 ≤ K/(1-(1/2 : ℝ)^α) := div_nonneg hK (by linarith)
  have hxB : ‖gx-px k‖ ≤ (K/(1-(1/2 : ℝ)^α))*r^α := by
    rw [norm_sub_rev]
    convert htx k using 1 <;> dsimp [K,campanatoL2StepConstant,r] <;> ring
  have hyB : ‖py k-gy‖ ≤ (K/(1-(1/2 : ℝ)^α))*r^α := by
    convert hty k using 1 <;> dsimp [K,campanatoL2StepConstant,r] <;> ring
  have hnorm : ‖gx-gy‖ ≤ (2*(K/(1-(1/2 : ℝ)^α))+K)*r^α := by
    have ht : ‖gx-gy‖ ≤ ‖gx-px k‖+‖px k-py k‖+‖py k-gy‖ := by
      have he : gx-gy = (gx-px k)+(px k-py k)+(py k-gy) := by abel
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    change ‖px k-py k‖ ≤ K*r^α at hxy
    linarith
  have hp := Real.rpow_le_rpow hr.le hrd hα.le
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) hd0.le] at hp
  apply hnorm.trans
  have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2*(K/(1-(1/2 : ℝ)^α))+K)
  convert hh using 1 <;> dsimp [campanatoL2HolderConstant,K] <;> ring

end GaussianTilt.MomentMapLinearDirichlet
