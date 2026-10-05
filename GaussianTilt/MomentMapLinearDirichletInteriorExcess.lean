import GaussianTilt.MomentMapLinearDirichletBoundaryExcessComparison

/-! # Actual unrestricted least-square gradient excess on interior balls -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet

lemma constant_error_integral_eq {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {μ : Measure X} [IsFiniteMeasure μ] {G : X → F} (hG : MemLp G 2 μ) (p : F) :
    (∫ x, ‖G x-p‖^2 ∂μ) = (∫ x, ‖G x‖^2 ∂μ)-2*inner ℝ p (∫ x,G x ∂μ)+‖p‖^2*μ.real univ := by
  have hI : Integrable (fun x => ‖G x‖^2) μ := hG.integrable_norm_pow (p := 2) (by norm_num)
  have hi : Integrable (fun x => inner ℝ p (G x)) μ :=
    ((innerSL ℝ p).comp_memLp' hG).integrable (by norm_num)
  have hI1 : Integrable (fun x => ‖G x‖^2-2*inner ℝ p (G x)) μ := hI.sub (hi.const_mul 2)
  have hI2 : Integrable (fun _ : X => ‖p‖^2) μ := integrable_const _
  have he (x : X) : ‖G x-p‖^2 = ‖G x‖^2-2*inner ℝ p (G x)+‖p‖^2 := by
    rw [norm_sub_sq_real,real_inner_comm (G x) p]
  simp_rw [he]
  rw [integral_add hI1 hI2,integral_sub hI (hi.const_mul 2),integral_const_mul,
    integral_inner (hG.integrable (by norm_num)),integral_const]
  simp only [smul_eq_mul]
  ring

/-- The genuine Bochner mean minimizes the true mean-square error, with
its exact variance defect. -/
theorem average_error_variance {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {μ : Measure X} [IsFiniteMeasure μ] {G : X → F} (hG : MemLp G 2 μ) (p : F) :
    (∫ x, ‖G x-p‖^2 ∂μ) = (∫ x, ‖G x-(⨍ y,G y ∂μ)‖^2 ∂μ)+
      μ.real univ*‖p-(⨍ y,G y ∂μ)‖^2 := by
  rw [constant_error_integral_eq hG p,constant_error_integral_eq hG,
    ← measure_smul_average μ G,real_inner_smul_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,norm_sub_sq_real]
  ring

theorem average_minimizes_error {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {μ : Measure X} [IsFiniteMeasure μ] {G : X → F} (hG : MemLp G 2 μ) (p : F) :
    (∫ x, ‖G x-(⨍ y,G y ∂μ)‖^2 ∂μ) ≤ ∫ x, ‖G x-p‖^2 ∂μ := by
  rw [average_error_variance hG p]
  exact le_add_of_nonneg_right (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))

/-- The corresponding true interior energy/excess inequalities, now with
arbitrary constant vectors rather than boundary-normal affine functions. -/
theorem interior_energy_excess_comparison {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hνμ : ν ≤ μ) {G H W : X → F}
    (hG : MemLp G 2 μ) (hH : MemLp H 2 μ) (hW : MemLp W 2 μ)
    (he : ∀ᵐ x ∂μ, G x=H x+W x) {de dx : ℝ} (hde : 0 ≤ de) (hdx : 0 ≤ dx)
    (hEnergy : (∫ x, ‖H x‖^2 ∂ν) ≤ de*(∫ x, ‖H x‖^2 ∂μ))
    (hExcess : ∃ p : F, (∫ x, ‖H x-p‖^2 ∂ν) ≤ dx*(∫ x, ‖H x-(⨍ y,G y ∂μ)‖^2 ∂μ)) :
    ((∫ x, ‖G x‖^2 ∂ν) ≤ 4*de*(∫ x, ‖G x‖^2 ∂μ)+(4*de+2)*(∫ x, ‖W x‖^2 ∂μ)) ∧
    ((∫ x, ‖G x-(⨍ y,G y ∂ν)‖^2 ∂ν) ≤
      4*dx*(∫ x, ‖G x-(⨍ y,G y ∂μ)‖^2 ∂μ)+(4*dx+2)*(∫ x, ‖W x‖^2 ∂μ)) := by
  have hGν := hG.mono_measure hνμ
  have hHν := hH.mono_measure hνμ
  have hWν := hW.mono_measure hνμ
  have heν : ∀ᵐ x ∂ν, G x=H x+W x := he.filter_mono (ae_mono hνμ)
  have hrev : ∀ᵐ x ∂μ, H x=G x+(-W x) := by filter_upwards [he] with x hx; rw [hx]; abel
  have hWmono : (∫ x, ‖W x‖^2 ∂ν) ≤ ∫ x, ‖W x‖^2 ∂μ :=
    integral_mono_measure hνμ (ae_of_all _ (fun x => sq_nonneg ‖W x‖)) (hW.integrable_norm_pow (p := 2) (by norm_num))
  constructor
  · have hsmall := integral_sq_norm_decomposition hGν hHν hWν heν
    have hlarge := integral_sq_norm_decomposition hH hG hW.neg hrev
    simp only [Pi.neg_apply,norm_neg] at hlarge
    have hm := mul_le_mul_of_nonneg_left hlarge hde
    nlinarith
  · obtain ⟨p,hp⟩ := hExcess
    have hmin := average_minimizes_error hGν p
    have hsmall := integral_sq_error_decomposition hGν hHν hWν heν p
    have hlarge := integral_sq_error_decomposition hH hG hW.neg hrev (⨍ y,G y ∂μ)
    simp only [Pi.neg_apply,norm_neg] at hlarge
    have hm := mul_le_mul_of_nonneg_left hlarge hdx
    nlinarith

end GaussianTilt.MomentMapLinearDirichlet
