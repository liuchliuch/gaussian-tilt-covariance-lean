import GaussianTilt.MomentMapLinearDirichletFlatPoissonStep
import GaussianTilt.MomentMapSchauderRescaling

/-!
# Actual dilation of the flat weak Poisson equation

The true second-derivative scaling and Haar change of variables transfer
the literal distributional equation. L² membership is preserved by the
actual pushforward measure formula, so rescaled residuals remain valid
inputs to the constructed half-ball correction.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Module
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma kernelLaplacian_comp_smul_C2 {ψ : KernelSpace n → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (r : ℝ) (x : KernelSpace n) :
    kernelLaplacian (fun y => ψ (r • y)) x = r^2 * kernelLaplacian ψ (r • x) := by
  have hc : ContDiff ℝ 2 (fun y : KernelSpace n => ψ (r • y)) := hψ.comp (contDiff_const.smul contDiff_id)
  have hs : fderiv ℝ (fderiv ℝ (fun y => ψ (r • y))) x = r^2 • fderiv ℝ (fderiv ℝ ψ) (r • x) := by
    have he : centeredRescale ψ 0 r = (fun y => ψ (r • y)) := by
      funext y
      simp [centeredRescale]
    have hh := secondFrechet_centeredRescale hψ 0 x r
    rw [he] at hh
    simpa only [sub_zero] using hh
  rw [kernelLaplacian_eq_trace hc, kernelLaplacian_eq_trace hψ, hs]
  simp only [kernelHessianTrace, ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma memLp_comp_smul_dirichlet {u : KernelSpace n → ℝ} (hu : MemLp u 2 volume)
    {r : ℝ} (hr : r ≠ 0) : MemLp (fun x => u (r • x)) 2 volume := by
  have hm : MemLp u 2 (Measure.map (fun x : KernelSpace n => r • x) volume) := by
    rw [Measure.map_addHaar_smul volume hr]
    exact hu.smul_measure ENNReal.ofReal_ne_top
  exact (Homeomorph.smulOfNeZero r hr).toMeasurableEquiv.memLp_map_measure_iff.mp hm

lemma tsupport_comp_inv_smul {ψ : KernelSpace n → ℝ} {r : ℝ} (hr : r ≠ 0) :
    tsupport (fun y => ψ (r⁻¹ • y)) ⊆ (fun y : KernelSpace n => r⁻¹ • y) ⁻¹' tsupport ψ := by
  apply closure_minimal _ ((isClosed_tsupport ψ).preimage (continuous_const.smul continuous_id))
  intro y hy
  exact subset_tsupport ψ hy

/-- Dilation preserves the actual local weak Poisson identity, including
the correct second-order forcing factor and arbitrary amplitude scaling. -/
theorem distribution_poisson_smul {Ω : Set (KernelSpace n)} {u f : KernelSpace n → ℝ}
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y * kernelLaplacian ψ y) = -(∫ y, f y * ψ y))
    {r : ℝ} (hr : 0 < r) (s : ℝ) :
    ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (fun y : KernelSpace n => r • y) ⁻¹' Ω →
      (∫ y, (s * u (r • y)) * kernelLaplacian ψ y) =
        -(∫ y, (s*r^2*f (r • y)) * ψ y) := by
  intro ψ hψ hψc hψs
  let φ := fun y => ψ (r⁻¹ • y)
  have hφ : ContDiff ℝ ∞ φ := hψ.comp (contDiff_const.smul contDiff_id)
  have hφc : HasCompactSupport φ := hψc.comp_homeomorph (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have hφs : tsupport φ ⊆ Ω := by
    intro y hy
    have hh := hψs (tsupport_comp_inv_smul hr.ne' hy)
    simpa only [mem_preimage, smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using hh
  have ht := heq φ hφ hφc hφs
  have hchange : (∫ y, u (r • y) * kernelLaplacian φ (r • y)) =
      -(∫ y, f (r • y) * φ (r • y)) := by
    have hleft := Measure.integral_comp_smul (volume : Measure (KernelSpace n))
      (fun y => u y * kernelLaplacian φ y) r
    have hright := Measure.integral_comp_smul (volume : Measure (KernelSpace n))
      (fun y => f y * φ y) r
    rw [hleft, hright, ht]
    simp only [smul_eq_mul, mul_neg]
  have hφlap (y : KernelSpace n) : kernelLaplacian φ (r • y) = r⁻¹^2 * kernelLaplacian ψ y := by
    rw [kernelLaplacian_comp_smul_C2 (contDiff_infty.mp hψ 2), smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hφval (y : KernelSpace n) : φ (r • y) = ψ y := by
    simp only [φ, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  simp_rw [hφlap, hφval] at hchange
  have hbase : (∫ y, u (r • y) * kernelLaplacian ψ y) = -(r^2 * ∫ y, f (r • y) * ψ y) := by
    have he : r⁻¹^2 * (∫ y, u (r • y) * kernelLaplacian ψ y) = -(∫ y, f (r • y) * ψ y) := by
      rw [← integral_const_mul]
      convert hchange using 1 <;> congr 1 <;> funext y <;> ring
    have hc : r^2 * r⁻¹^2 = 1 := by field_simp
    calc
      _ = r^2 * (r⁻¹^2 * ∫ y, u (r • y) * kernelLaplacian ψ y) := by rw [← mul_assoc, hc, one_mul]
      _ = _ := by rw [he]; ring
  have hleft : (fun y => (s*u (r • y))*kernelLaplacian ψ y) =
      (fun y => s*(u (r • y)*kernelLaplacian ψ y)) := by funext y; ring
  have hright : (fun y => (s*r^2*f (r • y))*ψ y) =
      (fun y => (s*r^2)*(f (r • y)*ψ y)) := by funext y; ring
  rw [hleft, hright, integral_const_mul, integral_const_mul, hbase]
  ring

end GaussianTilt.MomentMapLinearDirichlet
