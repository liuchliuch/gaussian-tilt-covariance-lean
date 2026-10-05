import GaussianTilt.MomentMapSchauderBoundaryRescale

/-! # Radius-uniform actual Poisson jet bounds -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2000000
open Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- Exact scale-weighted interior estimates. The initial derivative norms
are absent, and the constant is independent of center and radius. -/
theorem exists_scaled_poisson_jet_bound [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u f : KernelSpace n → ℝ) (a : KernelSpace n) (r : ℝ), 0 < r →
      ContDiffOn ℝ 2 u (Metric.ball a (r*2)) → Continuous f →
      (∀ x ∈ Metric.ball a (r*2), kernelLaplacian u x=f x) →
      ∀ U F H : ℝ, 0 ≤ U → 0 ≤ F → 0 ≤ H →
      (∀ x ∈ Metric.ball a (r*2), |u x| ≤ U) →
      (∀ x ∈ Metric.ball a (r*4), |f x| ≤ F) →
      (∀ x ∈ Metric.ball a (r*4), ∀ y ∈ Metric.ball a (r*4), |f x-f y| ≤ H*‖x-y‖^α) →
      r*‖fderiv ℝ u a‖ ≤ C*(U+r^2*F+r^2*H*r^α) ∧
      r^2*‖fderiv ℝ (fderiv ℝ u) a‖ ≤ C*(U+r^2*F+r^2*H*r^α) ∧
      (∀ x ∈ Metric.ball a (r/8), ∀ y ∈ Metric.ball a (r/8),
        r^2*‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤
          C*(U+r^2*F+r^2*H*r^α)*(r⁻¹*‖x-y‖)^α) := by
  obtain ⟨C,hC,hunit⟩ := exists_local_unit_poisson_jet_bound (n := n) hα hα1
  refine ⟨C,hC,?_⟩
  intro u f a r hr hu hf heq U F H hU hF hH huB hfB hfH
  let v := fun x : KernelSpace n => u (r • x+a)
  let g := fun x : KernelSpace n => r^2*f (r • x+a)
  have hmap2 : MapsTo (fun x : KernelSpace n => r • x+a) (Metric.ball 0 2) (Metric.ball a (r*2)) :=
    fun x hx => dilate_translate_mem_ball a x hr hx
  have hmap4 : MapsTo (fun x : KernelSpace n => r • x+a) (Metric.ball 0 4) (Metric.ball a (r*4)) :=
    fun x hx => dilate_translate_mem_ball a x hr hx
  have hv : ContDiffOn ℝ 2 v (Metric.ball 0 2) :=
    hu.comp ((contDiff_const.smul contDiff_id).add contDiff_const).contDiffOn hmap2
  have hg : Continuous g := continuous_const.mul (hf.comp ((continuous_const.smul continuous_id).add continuous_const))
  have hveq : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, kernelLaplacian v x=g x := by
    intro x hx
    rw [kernelLaplacian_comp_dilate_translate_at a x r
      (hu.contDiffAt (Metric.isOpen_ball.mem_nhds (hmap2 hx))),heq _ (hmap2 hx)]
  have hvB : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |v x| ≤ U := fun x hx => huB _ (hmap2 hx)
  have hgB : ∀ x ∈ Metric.ball (0 : KernelSpace n) 4, |g x| ≤ r^2*F := by
    intro x hx
    rw [show g x=r^2*f (r • x+a) from rfl,abs_mul,abs_of_nonneg (sq_nonneg r)]
    exact mul_le_mul_of_nonneg_left (hfB _ (hmap4 hx)) (sq_nonneg r)
  have hgH : ∀ x ∈ Metric.ball (0 : KernelSpace n) 4, ∀ y ∈ Metric.ball (0 : KernelSpace n) 4,
      |g x-g y| ≤ (r^2*H*r^α)*‖x-y‖^α := by
    intro x hx y hy
    change |r^2*f (r • x+a)-r^2*f (r • y+a)| ≤ _
    rw [← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg r)]
    have hh := hfH _ (hmap4 hx) _ (hmap4 hy)
    rw [add_sub_add_right_eq_sub,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hr,
      Real.mul_rpow hr.le (norm_nonneg _)] at hh
    exact (mul_le_mul_of_nonneg_left hh (sq_nonneg r)).trans_eq (by ring)
  obtain ⟨hD,hQ,hHH⟩ := hunit v g hv hg hveq U (r^2*F) (r^2*H*r^α)
    hU (by positivity) (by positivity) hvB hgB hgH
  have huc : ContDiffAt ℝ 2 u a := hu.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by positivity)))
  have huc0 : ContDiffAt ℝ 2 u (r • (0 : KernelSpace n)+a) := by simpa only [smul_zero,zero_add] using huc
  have hDscale := fderiv_comp_dilate_translate_at a 0 r huc0
  have hQscale := secondFrechet_comp_dilate_translate_at a 0 r huc0
  simp only [smul_zero,zero_add] at hDscale hQscale
  change ‖fderiv ℝ (fun x => u (r • x+a)) 0‖ ≤ _ at hD
  change ‖fderiv ℝ (fderiv ℝ (fun x => u (r • x+a))) 0‖ ≤ _ at hQ
  rw [hDscale,norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hD
  rw [hQscale,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] at hQ
  refine ⟨hD,hQ,?_⟩
  intro x hx y hy
  let X := r⁻¹ • (x-a)
  let Y := r⁻¹ • (y-a)
  have hX : X ∈ Metric.ball (0 : KernelSpace n) (1/8) := by
    rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    have hx' : ‖x-a‖ < r/8 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    have hh := mul_lt_mul_of_pos_left hx' (inv_pos.mpr hr)
    have he : r⁻¹*(r/8)=(1:ℝ)/8 := by field_simp
    rwa [he] at hh
  have hY : Y ∈ Metric.ball (0 : KernelSpace n) (1/8) := by
    rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    have hy' : ‖y-a‖ < r/8 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
    have hh := mul_lt_mul_of_pos_left hy' (inv_pos.mpr hr)
    have he : r⁻¹*(r/8)=(1:ℝ)/8 := by field_simp
    rwa [he] at hh
  have hXe : r • X+a=x := by dsimp [X]; rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,sub_add_cancel]
  have hYe : r • Y+a=y := by dsimp [Y]; rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,sub_add_cancel]
  have hh := hHH X hX Y hY
  have hx2 : x ∈ Metric.ball a (r*2) := Metric.ball_subset_ball (by linarith) hx
  have hy2 : y ∈ Metric.ball a (r*2) := Metric.ball_subset_ball (by linarith) hy
  have hux : ContDiffAt ℝ 2 u (r • X+a) := by rw [hXe]; exact hu.contDiffAt (Metric.isOpen_ball.mem_nhds hx2)
  have huy : ContDiffAt ℝ 2 u (r • Y+a) := by rw [hYe]; exact hu.contDiffAt (Metric.isOpen_ball.mem_nhds hy2)
  change ‖fderiv ℝ (fderiv ℝ (fun z => u (r • z+a))) X-fderiv ℝ (fderiv ℝ (fun z => u (r • z+a))) Y‖ ≤ _ at hh
  rw [secondFrechet_comp_dilate_translate_at a X r hux,secondFrechet_comp_dilate_translate_at a Y r huy,
    hXe,hYe,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] at hh
  have hXY : ‖X-Y‖=r⁻¹*‖x-y‖ := by
    dsimp [X,Y]
    rw [← smul_sub,sub_sub_sub_cancel_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  rwa [hXY] at hh

end GaussianTilt.MomentMapSchauder
