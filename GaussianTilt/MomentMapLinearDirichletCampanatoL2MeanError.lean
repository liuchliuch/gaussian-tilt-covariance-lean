import GaussianTilt.MomentMapLinearDirichletCampanatoL2Average

/-! # Vanishing actual mean error of L² approximating constants -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma locallyIntegrable_norm_sub_upperBall {F : Type*} [NormedAddCommGroup F]
    {G : KernelSpace n → F} (hG : LocallyIntegrable G volume) (p : F)
    (j : Fin n) (x : KernelSpace n) (r : ℝ) :
    IntegrableOn (fun z => ‖G z-p‖) (upperCampanatoBall j x r) := by
  have hGI : IntegrableOn G (upperCampanatoBall j x r) :=
    (hG.integrableOn_isCompact (isCompact_closedBall x r)).mono_set
      (inter_subset_left.trans Metric.ball_subset_closedBall)
  have hpI : IntegrableOn (fun _ : KernelSpace n => p) (upperCampanatoBall j x r) :=
    integrableOn_const (upperCampanatoBall_finite j x r)
  exact (hGI.sub hpI).norm

lemma l2_campanato_mean_error [NeZero n] {F : Type*} [NormedAddCommGroup F]
    (j : Fin n) (x : KernelSpace n) (hx : 0 ≤ x j) {G : KernelSpace n → F}
    (hG : LocallyIntegrable G volume) (p : F) {r C α : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hI : IntegrableOn (fun z => ‖G z-p‖^2) (upperCampanatoBall j x r))
    (hE : (∫ z in upperCampanatoBall j x r, ‖G z-p‖^2) ≤ C*r^((n:ℝ)+2*α)) :
    (⨍ z in upperCampanatoBall j x r, ‖G z-p‖) ≤
      (1+C/campanatoHalfBallVolume n)*r^α := by
  let v := campanatoHalfBallVolume n
  have hv : 0 < v := campanatoHalfBallVolume_pos
  have hm := upperCampanatoBall_volume_lower j x hx hr
  have hb := mean_norm_error_le_of_square (upperCampanatoBall_finite j x r)
    (mul_pos hv (pow_pos hr _)) hm (mul_nonneg hC (Real.rpow_nonneg hr.le _))
    (Real.rpow_pos_of_pos hr α) G p (locallyIntegrable_norm_sub_upperBall hG p j x r) hI hE
  convert hb using 1
  change (1+C/v)*r^α = r^α+C*r^((n:ℝ)+2*α)/(r^α*(v*r^n))
  rw [campanato_energy_power hr]
  field_simp

lemma upperCampanatoBall_eq_ball (j : Fin n) (x : KernelSpace n) {r : ℝ} (hrx : r ≤ x j) :
    upperCampanatoBall j x r = Metric.ball x r := by
  apply inter_eq_left.mpr
  intro z hz
  change 0 < z j
  have hn : ‖z-x‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
  have hc : |(z-x) j| ≤ ‖z-x‖ := PiLp.norm_apply_le (z-x) j
  simp only [PiLp.sub_apply] at hc
  linarith [neg_abs_le (z j-x j)]

lemma norm_constant_sub_le_mean_errors {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    {μ : Measure X} {S : Set X} (hS : μ S ≠ ∞) (hpos : 0 < μ.real S)
    (G : X → F) (p q : F) (hIp : IntegrableOn (fun z => ‖G z-p‖) S μ)
    (hIq : IntegrableOn (fun z => ‖G z-q‖) S μ) :
    ‖p-q‖ ≤ (⨍ z in S, ‖G z-p‖ ∂μ)+(⨍ z in S, ‖G z-q‖ ∂μ) := by
  have hconst : IntegrableOn (fun _ : X => ‖p-q‖) S μ := integrableOn_const hS
  have hb := integral_mono hconst (hIp.add hIq) (fun z => show ‖p-q‖ ≤ ‖G z-p‖+‖G z-q‖ from by
    have he : p-q = (p-G z)+(G z-q) := by abel
    rw [he]
    exact (norm_add_le _ _).trans_eq (by rw [norm_sub_rev p (G z)]))
  simp only [Pi.add_apply,integral_add hIp hIq,integral_const,Measure.restrict_apply_univ,measureReal_restrict_apply_univ,
    smul_eq_mul,← measureReal_def] at hb
  have hv : ‖p-q‖ ≤ ((∫ z in S, ‖G z-p‖ ∂μ)+(∫ z in S, ‖G z-q‖ ∂μ))/μ.real S :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hb)
  simpa only [setAverage_eq,smul_eq_mul,div_eq_mul_inv,add_mul,mul_add,mul_comm] using hv

end GaussianTilt.MomentMapLinearDirichlet
