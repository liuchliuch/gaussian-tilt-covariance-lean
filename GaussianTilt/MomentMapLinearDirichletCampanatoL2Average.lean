import GaussianTilt.MomentMapLinearDirichletCampanatoL2Selection
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-! # Actual mean-error estimates and differentiation on Euclidean balls -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma mean_norm_error_le_of_square {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    {μ : Measure X} {S : Set X} (hS : μ S ≠ ∞) {m E δ : ℝ}
    (hm : 0 < m) (hmS : m ≤ μ.real S) (hE : 0 ≤ E) (hδ : 0 < δ)
    (G : X → F) (p : F) (hI : IntegrableOn (fun x => ‖G x-p‖) S μ)
    (hI2 : IntegrableOn (fun x => ‖G x-p‖^2) S μ)
    (hbound : (∫ x in S, ‖G x-p‖^2 ∂μ) ≤ E) :
    (⨍ x in S, ‖G x-p‖ ∂μ) ≤ δ+E/(δ*m) := by
  have hmass : 0 < μ.real S := hm.trans_le hmS
  have hpt (x : X) : ‖G x-p‖ ≤ δ+‖G x-p‖^2/δ := by
    have ht : δ*‖G x-p‖ ≤ δ^2+‖G x-p‖^2 := by nlinarith [sq_nonneg (δ-‖G x-p‖)]
    apply (mul_le_mul_left hδ).mp
    have he : δ*(δ+‖G x-p‖^2/δ) = δ^2+‖G x-p‖^2 := by field_simp
    rw [he]
    exact ht
  have hconst : IntegrableOn (fun _ : X => δ) S μ := integrableOn_const hS
  have hb := integral_mono hI (hconst.add (hI2.div_const δ)) hpt
  have hmean : (⨍ x in S, ‖G x-p‖ ∂μ) ≤ δ+E/(δ*μ.real S) := by
    rw [setAverage_eq,smul_eq_mul,← div_eq_inv_mul]
    apply (div_le_iff₀ hmass).mpr
    have hbid : (∫ x in S, ‖G x-p‖ ∂μ) ≤ μ.real S*δ+E/δ := by
      simp only [Pi.add_apply,integral_add hconst (hI2.div_const δ),
        integral_const,Measure.restrict_apply_univ,measureReal_restrict_apply_univ,smul_eq_mul,integral_div,← measureReal_def] at hb
      exact hb.trans (add_le_add_left (div_le_div_of_nonneg_right hbound hδ.le) _)
    convert hbid using 1 <;> field_simp <;> ring
  apply hmean.trans
  exact add_le_add_left (div_le_div_of_nonneg_left hE (mul_pos hδ hm)
    (mul_le_mul_of_nonneg_left hmS hδ.le)) δ

lemma euclidean_ball_ae_eq_closedBall [NeZero n] (x : KernelSpace n) {r : ℝ} (hr : 0 < r) :
    Metric.ball x r =ᵐ[volume] Metric.closedBall x r := by
  apply ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall _
    Metric.isOpen_ball.measurableSet.nullMeasurableSet measure_closedBall_lt_top.ne
  rw [volume.addHaar_closedBall x hr.le,volume.addHaar_ball x hr.le]

/-- The ordinary Euclidean open-ball differentiation statement is derived
from the actual Vitali differentiation theorem and zero-volume spheres. -/
theorem ae_tendsto_openBall_average_norm_sub [NeZero n] {F : Type*} [NormedAddCommGroup F]
    {G : KernelSpace n → F} (hG : LocallyIntegrable G volume) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ x ∂volume, Tendsto (fun k : ℕ =>
      ⨍ z in Metric.ball x (R*(1/2 : ℝ)^k), ‖G z-G x‖) atTop (𝓝 0) := by
  have ht : Tendsto (fun k : ℕ => R*(1/2 : ℝ)^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1))
  have htpos : Tendsto (fun k : ℕ => R*(1/2 : ℝ)^k) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall (fun k => mul_pos hR (pow_pos (by norm_num) _))⟩
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hG 1] with x hx
  have hd := hx (fun _ : ℕ => x) (fun k => R*(1/2 : ℝ)^k) htpos
    (Eventually.of_forall (fun k => by
      rw [Metric.mem_closedBall,dist_self,one_mul]
      positivity))
  apply hd.congr
  intro k
  exact (setAverage_congr (euclidean_ball_ae_eq_closedBall x (mul_pos hR (pow_pos (by norm_num) _)))).symm

end GaussianTilt.MomentMapLinearDirichlet
