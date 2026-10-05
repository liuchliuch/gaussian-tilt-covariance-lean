import GaussianTilt.MomentMapLinearDirichletHarmonicL2Oscillation
import GaussianTilt.MomentMapSchauderBoundaryRescale
import GaussianTilt.MomentMapLinearDirichletFlatRescaling
import GaussianTilt.MomentMapLinearDirichletCampanatoL2Geometry

/-! # Exact ball rescaling of the genuine harmonic L² excess estimate -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal Pointwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma integral_ball_dilate_translate (f : KernelSpace n → ℝ) (a : KernelSpace n)
    {r : ℝ} (hr : 0 < r) :
    (∫ y in Metric.ball (0:KernelSpace n) 2, f (r • y+a))=
      (r^n)⁻¹*(∫ z in Metric.ball a (2*r), f z) := by
  have hm (y : KernelSpace n) : r • y+a ∈ Metric.ball a (2*r) ↔ y ∈ Metric.ball (0:KernelSpace n) 2 := by
    simp only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_right,norm_smul,Real.norm_of_nonneg hr.le,sub_zero]
    constructor <;> intro h <;> nlinarith
  rw [← integral_indicator Metric.isOpen_ball.measurableSet]
  have he : (fun y => (Metric.ball (0:KernelSpace n) 2).indicator (fun y => f (r • y+a)) y)=
      (fun y => (Metric.ball a (2*r)).indicator f (r • y+a)) := by
    funext y
    by_cases hy : y ∈ Metric.ball (0:KernelSpace n) 2
    · rw [indicator_of_mem hy,indicator_of_mem ((hm y).mpr hy)]
    · rw [indicator_of_notMem hy,indicator_of_notMem (fun hh => hy ((hm y).mp hh))]
  rw [he]
  have hh := Measure.integral_comp_smul_of_nonneg (volume : Measure (KernelSpace n))
    (fun z => (Metric.ball a (2*r)).indicator f (z+a)) r (hR := hr.le)
  simp only [KernelSpace,finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul] at hh
  rw [hh,integral_add_right_eq_self,integral_indicator Metric.isOpen_ball.measurableSet]

lemma memLp_dilate_translate {h : KernelSpace n → ℝ} (hh : MemLp h 2 volume)
    (a : KernelSpace n) {r : ℝ} (hr : r ≠ 0) : MemLp (fun y => h (r • y+a)) 2 volume :=
  memLp_comp_smul_dirichlet (hh.comp_measurePreserving (measurePreserving_add_right volume a)) hr

/-- Dimension-only local Lipschitz-square control at every center and
scale, with any constant removed from the true local L² energy. -/
theorem exists_harmonic_L2_oscillation_bound_scaled [NeZero n] :
    ∃ K : ℝ, 0 < K ∧ ∀ h : KernelSpace n → ℝ, MemLp h 2 volume →
      ∀ a : KernelSpace n, ∀ R : ℝ, 0 < R →
      (∀ x ∈ Metric.ball a R, ContDiffAt ℝ ∞ h x) →
      (∀ x ∈ Metric.ball a R, kernelLaplacian h x=0) →
      ∀ q : ℝ, ∀ x ∈ Metric.ball a (R/2), ∀ y ∈ Metric.ball a (R/2),
        (h x-h y)^2 ≤ K*(R^(n+2))⁻¹*(∫ z in Metric.ball a R, (h z-q)^2)*‖x-y‖^2 := by
  obtain ⟨K,hK,hbase⟩ := exists_local_harmonic_L2_oscillation_bound (n := n)
  refine ⟨K*2^(n+2),by positivity,?_⟩
  intro h hLp a R hR hs hhar q x hx y hy
  let r := R/2
  have hr : 0 < r := half_pos hR
  let H := fun z => h (r • z+a)
  have hHLp : MemLp H 2 volume := memLp_dilate_translate hLp a hr.ne'
  have hmaps (z : KernelSpace n) (hz : z ∈ Metric.ball (0:KernelSpace n) 2) : r • z+a ∈ Metric.ball a R := by
    have hh := dilate_translate_mem_ball a z hr hz
    have hrR : r*2=R := by dsimp [r]; ring
    simpa only [hrR] using hh
  have hHs (z : KernelSpace n) (hz : z ∈ Metric.ball (0:KernelSpace n) 2) : ContDiffAt ℝ ∞ H z :=
    (hs _ (hmaps z hz)).comp z ((contDiff_const.smul contDiff_id).add contDiff_const).contDiffAt
  have hHhar (z : KernelSpace n) (hz : z ∈ Metric.ball (0:KernelSpace n) 2) : kernelLaplacian H z=0 := by
    rw [kernelLaplacian_comp_dilate_translate_at a z r (contDiffAt_infty.mp (hs _ (hmaps z hz)) 2),hhar _ (hmaps z hz),mul_zero]
  letI : Fact (volume (Metric.ball (0:KernelSpace n) 2) < (⊤:ℝ≥0∞)) := ⟨measure_ball_lt_top⟩
  have hHI : IntegrableOn (fun z => (H z-q)^2) (Metric.ball (0:KernelSpace n) 2) volume := by
    have hconst : MemLp (fun _ : KernelSpace n => q) 2 (volume.restrict (Metric.ball (0:KernelSpace n) 2)) := memLp_const q
    exact ((hHLp.mono_measure Measure.restrict_le_self).sub hconst).integrable_sq
  let x' := r⁻¹ • (x-a)
  let y' := r⁻¹ • (y-a)
  have hx' : x' ∈ Metric.ball (0:KernelSpace n) 1 := by
    change ‖r⁻¹ • (x-a)-0‖ < 1
    rw [sub_zero,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    have hhx : ‖x-a‖ < r := hx
    exact (inv_mul_lt_iff₀ hr).mpr (by simpa using hhx)
  have hy' : y' ∈ Metric.ball (0:KernelSpace n) 1 := by
    change ‖r⁻¹ • (y-a)-0‖ < 1
    rw [sub_zero,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    have hhy : ‖y-a‖ < r := hy
    exact (inv_mul_lt_iff₀ hr).mpr (by simpa using hhy)
  have hHx : H x'=h x := by simp [H,x',smul_smul,mul_inv_cancel₀ hr.ne']
  have hHy : H y'=h y := by simp [H,y',smul_smul,mul_inv_cancel₀ hr.ne']
  have hdist : ‖x'-y'‖ = r⁻¹*‖x-y‖ := by
    rw [show x'-y'=r⁻¹ • (x-y) by dsimp [x',y']; module]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have hi : (∫ z in Metric.ball (0:KernelSpace n) 2, (H z-q)^2)=
      (r^n)⁻¹*(∫ z in Metric.ball a R, (h z-q)^2) := by
    have hh := integral_ball_dilate_translate (fun z => (h z-q)^2) a hr
    have hrR : 2*r=R := by dsimp [r]; ring
    simpa only [hrR,H] using hh
  have hb := hbase H hHs hHhar q hHI x' hx' y' hy'
  rw [hHx,hHy,hi,hdist] at hb
  convert hb using 1
  dsimp [r]
  simp only [div_pow,pow_add,inv_mul_eq_div,inv_div,pow_two]
  field_simp
  <;> ring

end GaussianTilt.MomentMapLinearDirichlet
