import GaussianTilt.MomentMapLinearDirichletCampanatoL2MeanError

/-!
# The constructed Hölder field is the actual weak-field representative

Lebesgue differentiation of the original locally integrable field and
vanishing mean error identify the geometric Campanato limit almost
everywhere. Boundary values are then supplied by the proved Hölder field.
-/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Any actual geometric Campanato limit equals the original field almost
everywhere inside the half-space. No AE representative premise is used. -/
theorem ae_l2_campanato_limit_eq [NeZero n] {F : Type*}
    [NormedAddCommGroup F] [CompleteSpace F]
    (j : Fin n) (G : KernelSpace n → F) (p : KernelSpace n → ℕ → F)
    (L : KernelSpace n → F) {S : Set (KernelSpace n)} {R C α : ℝ}
    (hG : LocallyIntegrable G volume) (hR : 0 < R) (hC : 0 ≤ C) (hα : 0 < α)
    (hI : ∀ x ∈ S, ∀ k, IntegrableOn (fun z => ‖G z-p x k‖^2)
      (upperCampanatoBall j x (R*(1/2 : ℝ)^k)))
    (hE : ∀ x ∈ S, ∀ k, (∫ z in upperCampanatoBall j x (R*(1/2 : ℝ)^k), ‖G z-p x k‖^2) ≤
      C*(R*(1/2 : ℝ)^k)^((n:ℝ)+2*α))
    (hlim : ∀ x ∈ S, Tendsto (p x) atTop (𝓝 (L x))) :
    ∀ᵐ x ∂volume, x ∈ S → 0 < x j → L x = G x := by
  let r := fun k : ℕ => R*(1/2 : ℝ)^k
  have hr : ∀ k, 0 < r k := fun k => mul_pos hR (pow_pos (by norm_num) _)
  have ht : Tendsto r atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1))
  have hpow : Tendsto (fun k => (r k)^α) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hα.ne'] using (Real.continuous_rpow_const hα.le).continuousAt.tendsto.comp ht
  filter_upwards [ae_tendsto_openBall_average_norm_sub hG hR] with x hx
  intro hxS hxj
  have hupper : ∀ᶠ k in atTop, upperCampanatoBall j x (r k) = Metric.ball x (r k) := by
    filter_upwards [(tendsto_order.mp ht).2 (x j) hxj] with k hk
    exact upperCampanatoBall_eq_ball j x hk.le
  have hbound : ∀ᶠ k in atTop, ‖p x k-G x‖ ≤
      (1+C/campanatoHalfBallVolume n)*(r k)^α+
        (⨍ z in Metric.ball x (r k), ‖G z-G x‖) := by
    filter_upwards [hupper] with k hk
    have hvol := upperCampanatoBall_volume_lower j x hxj.le (hr k)
    have hmass : 0 < volume.real (upperCampanatoBall j x (r k)) :=
      (mul_pos campanatoHalfBallVolume_pos (pow_pos (hr k) _)).trans_le hvol
    have hc := norm_constant_sub_le_mean_errors (upperCampanatoBall_finite j x (r k)) hmass
      G (p x k) (G x) (locallyIntegrable_norm_sub_upperBall hG (p x k) j x (r k))
      (locallyIntegrable_norm_sub_upperBall hG (G x) j x (r k))
    have he := l2_campanato_mean_error j x hxj.le hG (p x k) (hr k) hC (hI x hxS k) (hE x hxS k)
    rw [hk] at hc he
    exact hc.trans (add_le_add_right he _)
  have hnorm : Tendsto (fun k => ‖p x k-G x‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) hbound
    simpa only [mul_zero,zero_add] using (tendsto_const_nhds.mul hpow).add hx
  have hpG : Tendsto (p x) atTop (𝓝 (G x)) := (tendsto_iff_norm_sub_tendsto_zero).mpr hnorm
  exact tendsto_nhds_unique (hlim x hxS) hpG

/-- The genuine L² Campanato reconstruction endpoint, including the AE
identity with the original field and a uniform Hölder bound up to the plane. -/
theorem exists_l2_campanato_holder_representative [NeZero n] {F : Type*}
    [NormedAddCommGroup F] [CompleteSpace F]
    (j : Fin n) (G : KernelSpace n → F) (p : KernelSpace n → ℕ → F)
    {S : Set (KernelSpace n)} {R C α : ℝ}
    (hG : LocallyIntegrable G volume) (hR : 0 < R) (hC : 0 ≤ C) (hα : 0 < α)
    (hS : ∀ x ∈ S, 0 ≤ x j)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ R/2)
    (hI : ∀ x ∈ S, ∀ k, IntegrableOn (fun z => ‖G z-p x k‖^2)
      (upperCampanatoBall j x (R*(1/2 : ℝ)^k)))
    (hE : ∀ x ∈ S, ∀ k, (∫ z in upperCampanatoBall j x (R*(1/2 : ℝ)^k), ‖G z-p x k‖^2) ≤
      C*(R*(1/2 : ℝ)^k)^((n:ℝ)+2*α)) :
    ∃ L : KernelSpace n → F,
      (∀ᵐ x ∂volume, x ∈ S → 0 < x j → L x = G x) ∧
      (∀ x ∈ S, Tendsto (p x) atTop (𝓝 (L x))) ∧
      (∀ x ∈ S, ∀ y ∈ S, ‖L x-L y‖ ≤ campanatoL2HolderConstant n C α*‖x-y‖^α) := by
  obtain ⟨L,hlim,htail,hholder⟩ := exists_l2_campanato_holder_limit j G p hR hC hα hS hdiam hI hE
  exact ⟨L,ae_l2_campanato_limit_eq j G p L hG hR hC hα hI hE hlim,hlim,hholder⟩

end GaussianTilt.MomentMapLinearDirichlet
