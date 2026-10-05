import GaussianTilt.MomentMapLinearDirichletBoundaryExcess

/-! # Actual integral energy/excess comparison for harmonic replacements -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma integral_sq_norm_decomposition {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    {μ : Measure X} {G H W : X → F} (hG : MemLp G 2 μ) (hH : MemLp H 2 μ) (hW : MemLp W 2 μ)
    (he : ∀ᵐ x ∂μ, G x=H x+W x) :
    (∫ x, ‖G x‖^2 ∂μ) ≤ 2*(∫ x, ‖H x‖^2 ∂μ)+2*(∫ x, ‖W x‖^2 ∂μ) := by
  have hGI := hG.integrable_norm_pow (p := 2) (by norm_num)
  have hHI := hH.integrable_norm_pow (p := 2) (by norm_num)
  have hWI := hW.integrable_norm_pow (p := 2) (by norm_num)
  have hb := integral_mono_ae hGI ((hHI.const_mul 2).add (hWI.const_mul 2)) (by
    filter_upwards [he] with x hx
    simp only [Pi.add_apply]
    rw [hx]
    have hn := norm_add_le (H x) (W x)
    nlinarith [norm_nonneg (H x+W x),norm_nonneg (H x),norm_nonneg (W x),sq_nonneg (‖H x‖-‖W x‖)])
  simpa only [Pi.add_apply,integral_add (hHI.const_mul 2) (hWI.const_mul 2),integral_const_mul] using hb

lemma integral_sq_error_decomposition {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    {μ : Measure X} [IsFiniteMeasure μ] {G H W : X → F}
    (hG : MemLp G 2 μ) (hH : MemLp H 2 μ) (hW : MemLp W 2 μ)
    (he : ∀ᵐ x ∂μ, G x=H x+W x) (p : F) :
    (∫ x, ‖G x-p‖^2 ∂μ) ≤ 2*(∫ x, ‖H x-p‖^2 ∂μ)+2*(∫ x, ‖W x‖^2 ∂μ) := by
  apply integral_sq_norm_decomposition (hG.sub (memLp_const p)) (hH.sub (memLp_const p)) hW
  filter_upwards [he] with x hx
  simp only [Pi.sub_apply]
  rw [hx]
  abel

/-- Actual integral inequalities for one frozen harmonic replacement.
The comparison constants are derived by genuine L² triangles and the
normal-mean minimizing property, with no pointwise gradient bound. -/
theorem boundary_energy_excess_comparison {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NeZero μ] [NeZero ν]
    (hνμ : ν ≤ μ) (j : Fin n) {G H W : X → KernelSpace n}
    (hG : MemLp G 2 μ) (hH : MemLp H 2 μ) (hW : MemLp W 2 μ)
    (he : ∀ᵐ x ∂μ, G x=H x+W x) {de dx : ℝ} (hde : 0 ≤ de) (hdx : 0 ≤ dx)
    (hEnergy : (∫ x, ‖H x‖^2 ∂ν) ≤ de*(∫ x, ‖H x‖^2 ∂μ))
    (hExcess : ∃ t : ℝ,
      (∫ x, ‖H x-t • EuclideanSpace.basisFun (Fin n) ℝ j‖^2 ∂ν) ≤
        dx*(∫ x, ‖H x-normalMean μ j G • EuclideanSpace.basisFun (Fin n) ℝ j‖^2 ∂μ)) :
    ((∫ x, ‖G x‖^2 ∂ν) ≤ 4*de*(∫ x, ‖G x‖^2 ∂μ)+(4*de+2)*(∫ x, ‖W x‖^2 ∂μ)) ∧
    ((∫ x, ‖G x-normalMean ν j G • EuclideanSpace.basisFun (Fin n) ℝ j‖^2 ∂ν) ≤
      4*dx*(∫ x, ‖G x-normalMean μ j G • EuclideanSpace.basisFun (Fin n) ℝ j‖^2 ∂μ)+
        (4*dx+2)*(∫ x, ‖W x‖^2 ∂μ)) := by
  have hGν := hG.mono_measure hνμ
  have hHν := hH.mono_measure hνμ
  have hWν := hW.mono_measure hνμ
  have heν : ∀ᵐ x ∂ν, G x=H x+W x := he.filter_mono (ae_mono hνμ)
  have hrev : ∀ᵐ x ∂μ, H x=G x+(-W x) := by filter_upwards [he] with x hx; rw [hx]; abel
  have hWnorm : (∫ x, ‖-W x‖^2 ∂μ) = ∫ x, ‖W x‖^2 ∂μ := by simp only [norm_neg]
  have hWmono : (∫ x, ‖W x‖^2 ∂ν) ≤ ∫ x, ‖W x‖^2 ∂μ :=
    integral_mono_measure hνμ (ae_of_all _ (fun x => sq_nonneg ‖W x‖)) (hW.integrable_norm_pow (p := 2) (by norm_num))
  constructor
  · have hsmall := integral_sq_norm_decomposition hGν hHν hWν heν
    have hlarge := integral_sq_norm_decomposition hH hG hW.neg hrev
    simp only [Pi.neg_apply,norm_neg] at hlarge
    have hm := mul_le_mul_of_nonneg_left hlarge hde
    nlinarith
  · obtain ⟨t,ht⟩ := hExcess
    have hmin := normalMean_minimizes_error j hGν t
    have hsmall := integral_sq_error_decomposition hGν hHν hWν heν
      (t • EuclideanSpace.basisFun (Fin n) ℝ j)
    have hlarge := integral_sq_error_decomposition hH hG hW.neg hrev
      (normalMean μ j G • EuclideanSpace.basisFun (Fin n) ℝ j)
    simp only [Pi.neg_apply,norm_neg] at hlarge
    have hm := mul_le_mul_of_nonneg_left hlarge hdx
    nlinarith

end GaussianTilt.MomentMapLinearDirichlet
