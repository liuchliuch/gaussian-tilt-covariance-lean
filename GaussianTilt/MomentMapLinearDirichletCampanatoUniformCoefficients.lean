import GaussianTilt.MomentMapLinearDirichletCampanatoL2Limits

/-! # Uniform coefficients at every radius from actual mean-square decay -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Square-integral approximation with a positive excess exponent controls
all coefficients, including radii between the geometric scales. -/
theorem exists_uniform_campanato_coefficient_bound [NeZero n]
    {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    {R C α B : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hα : 0 < α) (hB : 0 ≤ B) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (j : Fin n) (x : KernelSpace n), 0 ≤ x j →
      ∀ (G : KernelSpace n → F) (p : ℝ → F), ‖p R‖ ≤ B →
      (∀ r, 0 < r → r ≤ R → IntegrableOn (fun y => ‖G y-p r‖^2) (upperCampanatoBall j x r)) →
      (∀ r, 0 < r → r ≤ R → (∫ y in upperCampanatoBall j x r, ‖G y-p r‖^2) ≤
        C*r^((n:ℝ)+2*α)) → ∀ r, 0 < r → r ≤ R → ‖p r‖ ≤ L := by
  let ρ : ℝ := 1/2
  have hρ : 0 < ρ := by norm_num [ρ]
  have hρ1 : ρ < 1 := by norm_num [ρ]
  let K := 2*Real.sqrt (C/(campanatoHalfBallVolume n*ρ^n))
  let A := K*R^α
  let T := A/(1-ρ^α)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := mul_nonneg hK (Real.rpow_nonneg hR.le _)
  have hden : 0 < 1-ρ^α := sub_pos.mpr (Real.rpow_lt_one hρ.le hρ1 hα)
  have hT : 0 ≤ T := div_nonneg hA hden.le
  refine ⟨B+2*T+A,by positivity,?_⟩
  intro j x hx G p hpR hI hE
  have hscale (k : ℕ) : 0 < R*ρ^k ∧ R*ρ^k ≤ R :=
    ⟨mul_pos hR (pow_pos hρ _), by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hρ.le hρ1.le) hR.le⟩
  obtain ⟨p₀,hp₀,htail⟩ := exists_l2_campanato_geometric_limit j x hx G (fun k => p (R*ρ^k))
    hR hρ hρ1 hC hα (fun k => hI _ (hscale k).1 (hscale k).2)
    (fun k => hE _ (hscale k).1 (hscale k).2)
  have htailB (k : ℕ) : ‖p (R*ρ^k)-p₀‖ ≤ T := by
    apply (htail k).trans
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hscale k).1.le (hscale k).2 hα.le) hK
  have hpzero : ‖p₀‖ ≤ B+T := by
    have hh := norm_add_le (p R) (p₀-p R)
    have h0 : ‖p₀-p R‖ ≤ T := by
      rw [norm_sub_rev]
      simpa only [pow_zero,mul_one] using htailB 0
    have he : p R+(p₀-p R)=p₀ := by abel
    rw [he] at hh
    linarith
  intro r hr hrR
  obtain ⟨k,hkl,hku⟩ := exists_nat_pow_near_of_lt_one (div_pos hr hR) ((div_le_one hR).mpr hrR) hρ hρ1
  have hrk : r ≤ R*ρ^k := by
    have hh := (div_le_iff₀ hR).mp hku
    simpa only [mul_comm] using hh
  have hkr : ρ*(R*ρ^k) ≤ r := by
    have hh := (lt_div_iff₀ hR).mp hkl
    rw [pow_succ] at hh
    nlinarith
  have hsmall : upperCampanatoBall j x (ρ*(R*ρ^k)) ⊆ upperCampanatoBall j x r :=
    upperCampanatoBall_mono (by simpa only [dist_self,zero_add] using hkr)
  have hlarge : upperCampanatoBall j x (ρ*(R*ρ^k)) ⊆ upperCampanatoBall j x (R*ρ^k) :=
    upperCampanatoBall_mono (by simp only [dist_self,zero_add]; nlinarith [(hscale k).1])
  have heR : (∫ y in upperCampanatoBall j x r, ‖G y-p r‖^2) ≤ C*(R*ρ^k)^((n:ℝ)+2*α) :=
    (hE r hr hrR).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hr.le hrk (by positivity)) hC)
  have hcoh := l2_campanato_coherence_at_scale j x hx G (p r) (p (R*ρ^k))
    (hscale k).1 hρ hC hsmall hlarge (hI r hr hrR)
    (hI _ (hscale k).1 (hscale k).2) heR (hE _ (hscale k).1 (hscale k).2)
  have hcohA : ‖p r-p (R*ρ^k)‖ ≤ A := hcoh.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hscale k).1.le (hscale k).2 hα.le) hK)
  have hn := norm_add_le (p r-p (R*ρ^k)) (p (R*ρ^k)-p₀)
  have hn2 := norm_add_le (p r-p₀) p₀
  have he1 : (p r-p (R*ρ^k))+(p (R*ρ^k)-p₀)=p r-p₀ := by abel
  rw [he1] at hn
  simp only [sub_add_cancel] at hn2
  linarith [htailB k]

end GaussianTilt.MomentMapLinearDirichlet
