import GaussianTilt.MomentMapLinearDirichletNaturalData
import GaussianTilt.MomentMapLinearDirichletInteriorEnergyFields

/-! # Actual volume-order energy bounds from a bounded weak-gradient representative -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ} [NeZero n]

lemma weakGradient_energy_le_bound_volume (u : VolumeJet n) (j : Fin n)
    {R B : ℝ} (hB : 0≤B)
    (hbound : ∀ᵐx∂volume,‖x‖<R → 0<x j → ‖euclideanWeakGradient u x‖≤B)
    {S : Set (KernelSpace n)} (hS : MeasurableSet S)
    (hSU : S⊆upperCampanatoBall j 0 R)
    {a : KernelSpace n} {r : ℝ} (hr : 0≤r) (hSB : S⊆Metric.ball a r) :
    (∫x in S,‖euclideanWeakGradient u x‖^2)≤
      (B^2*volume.real (Metric.ball (0:KernelSpace n) 1))*r^n := by
  have hfin : volume S≠∞ := (measure_mono hSB).trans_lt measure_ball_lt_top |>.ne
  have hI := ((euclideanWeakGradient_memLp u).restrict S).integrable_norm_pow (p:=2) (by norm_num)
  have hc : IntegrableOn (fun _ : KernelSpace n=>B^2) S := integrableOn_const hfin
  have hp : ∀ᵐx∂volume.restrict S,‖euclideanWeakGradient u x‖^2≤B^2 := by
    filter_upwards [ae_restrict_of_ae hbound,ae_restrict_mem hS] with x hx hxs
    have hxU:=hSU hxs
    have hxn : ‖x‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using hxU.1
    exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (hx hxn hxU.2)
  have hh:=integral_mono_ae hI hc hp
  simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ] at hh
  have hvol:=measureReal_mono (μ:=(volume:Measure (KernelSpace n))) hSB measure_ball_lt_top.ne
  rw [real_volume_euclidean_ball a hr] at hvol
  nlinarith [mul_le_mul_of_nonneg_right hvol (sq_nonneg B)]

lemma upperBall_subset_origin_upper (j : Fin n) (a : KernelSpace n) {r R : ℝ}
    (har : ‖a‖+r≤R) : upperCampanatoBall j a r⊆upperCampanatoBall j 0 R := by
  intro x hx
  refine ⟨?_,hx.2⟩
  have hxa : ‖x-a‖<r := by simpa only [Metric.mem_ball,dist_eq_norm] using hx.1
  have ht : ‖x‖≤‖x-a‖+‖a‖ := by simpa only [sub_add_cancel] using norm_add_le (x-a) a
  rw [Metric.mem_ball,dist_zero_right]
  linarith

lemma bounded_weakGradient_upperBall_energy (u : VolumeJet n) (j : Fin n)
    {R B : ℝ} (hB : 0≤B)
    (hbound : ∀ᵐx∂volume,‖x‖<R → 0<x j → ‖euclideanWeakGradient u x‖≤B)
    (a : KernelSpace n) {r : ℝ} (hr : 0≤r) (har : ‖a‖+r≤R) :
    (∫x in upperCampanatoBall j a r,‖euclideanWeakGradient u x‖^2)≤
      (B^2*volume.real (Metric.ball (0:KernelSpace n) 1))*r^n :=
  weakGradient_energy_le_bound_volume u j hB hbound (isOpen_upperCampanatoBall j a r).measurableSet
    (upperBall_subset_origin_upper j a har) hr inter_subset_left

lemma bounded_weakGradient_ball_energy (u : VolumeJet n) (j : Fin n)
    {R B : ℝ} (hB : 0≤B)
    (hbound : ∀ᵐx∂volume,‖x‖<R → 0<x j → ‖euclideanWeakGradient u x‖≤B)
    (a : KernelSpace n) {r : ℝ} (hr : 0≤r)
    (hBall : Metric.ball a r⊆upperCampanatoBall j 0 R) :
    ballGradientEnergy u a r≤(B^2*volume.real (Metric.ball (0:KernelSpace n) 1))*r^n :=
  weakGradient_energy_le_bound_volume u j hB hbound Metric.isOpen_ball.measurableSet hBall hr (Subset.refl _)

end GaussianTilt.MomentMapLinearDirichlet
