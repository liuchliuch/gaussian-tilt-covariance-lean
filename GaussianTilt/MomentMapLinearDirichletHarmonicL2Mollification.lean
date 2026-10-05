import GaussianTilt.MomentMapLinearDirichletCoordinates
import GaussianTilt.NegativeSobolevMollifierFamily

/-! # Actual L² approximation by the Euclidean harmonic mollifiers -/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma harmonicConvolution_coordinate_transport (ρ f : KernelSpace n → ℝ) (x : KernelSpace n) :
    scalarConvolution (ρ ∘ (dirichletCoordinateEquiv n).symm)
      (f ∘ (dirichletCoordinateEquiv n).symm) (dirichletCoordinateEquiv n x)=harmonicConvolution ρ f x := by
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  unfold scalarConvolution harmonicConvolution
  change (∫ y, ρ ((dirichletCoordinateEquiv n).symm y)*
    f ((dirichletCoordinateEquiv n).symm (dirichletCoordinateEquiv n x-y)))=∫ y, ρ y*f (x-y)
  rw [← hμ.integral_comp (dirichletCoordinateEquiv n).toHomeomorph.measurableEmbedding]
  simp only [map_sub,ContinuousLinearEquiv.symm_apply_apply]

lemma dirichletCoordinateEquiv_norm_le (x : KernelSpace n) : ‖dirichletCoordinateEquiv n x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  exact PiLp.norm_apply_le x i

lemma harmonic_raw_mollifier_support (k : ℕ) :
    Function.support ((harmonicMollifierBump n k).normed volume ∘ (dirichletCoordinateEquiv n).symm) ⊆
      Function.support (canonicalMollifier n k) := by
  intro x hx
  have hx' : (dirichletCoordinateEquiv n).symm x ∈ Function.support ((harmonicMollifierBump n k).normed volume) := hx
  rw [ContDiffBump.support_normed_eq] at hx'
  rw [canonicalMollifier_support]
  have hn := dirichletCoordinateEquiv_norm_le ((dirichletCoordinateEquiv n).symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hn
  change ‖(dirichletCoordinateEquiv n).symm x-0‖ < ((k:ℝ)+1)⁻¹ at hx'
  change ‖x-0‖ < ((k:ℝ)+1)⁻¹
  simpa only [sub_zero] using hn.trans_lt (by simpa only [sub_zero] using hx')

lemma harmonicMollify_memLp {f : KernelSpace n → ℝ} (hf : MemLp f 2 volume) (k : ℕ) :
    MemLp (harmonicMollify k f) 2 volume := by
  let e := dirichletCoordinateEquiv n
  let ρ := (harmonicMollifierBump n k).normed (volume : Measure (KernelSpace n))
  have hμ : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have hμs : MeasurePreserving e.symm volume volume := PiLp.volume_preserving_toLp (Fin n)
  have hρ1 : (∫ x, (ρ ∘ e.symm) x)=1 := by
    change (∫ x, ρ (e.symm x))=1
    rw [hμs.integral_comp e.symm.toHomeomorph.measurableEmbedding]
    exact (harmonicMollifierBump n k).integral_normed
  have hraw := scalarConvolution_memLp
    ((harmonicMollifierBump n k).continuous_normed.comp e.symm.continuous)
    ((harmonicMollifierBump n k).hasCompactSupport_normed.comp_homeomorph e.symm.toHomeomorph)
    (fun x => (harmonicMollifierBump n k).nonneg_normed _) hρ1 (hf.comp_measurePreserving hμs)
  have hh := hraw.comp_measurePreserving hμ
  change MemLp (fun x => scalarConvolution (ρ ∘ e.symm) (f ∘ e.symm) (e x)) 2 volume at hh
  have he : (fun x => scalarConvolution (ρ ∘ e.symm) (f ∘ e.symm) (e x))=harmonicMollify k f :=
    funext (harmonicConvolution_coordinate_transport ρ f)
  rwa [he] at hh

/-- Strong L² convergence is obtained by the proved coordinate mollifier
contraction and density argument, transported with the actual unit Jacobian. -/
theorem integral_harmonicMollify_sub_sq_tendsto {f : KernelSpace n → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun k => ∫ x, (harmonicMollify k f x-f x)^2) atTop (𝓝 0) := by
  let e := dirichletCoordinateEquiv n
  let ρ := fun k => (harmonicMollifierBump n k).normed (volume : Measure (KernelSpace n)) ∘ e.symm
  have hμ : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have hμs : MeasurePreserving e.symm volume volume := PiLp.volume_preserving_toLp (Fin n)
  have hρ1 (k : ℕ) : (∫ x, ρ k x)=1 := by
    change (∫ x, (harmonicMollifierBump n k).normed volume (e.symm x))=1
    rw [hμs.integral_comp e.symm.toHomeomorph.measurableEmbedding]
    exact (harmonicMollifierBump n k).integral_normed
  have hρlim : Tendsto (fun k => Function.support (ρ k)) atTop (𝓝 0).smallSets := by
    apply tendsto_smallSets_iff.mpr
    intro U hU
    filter_upwards [(tendsto_smallSets_iff.mp (canonicalMollifier_support_tendsto n)) U hU] with k hk
    exact (harmonic_raw_mollifier_support k).trans hk
  have hh := integral_mollifier_sub_sq_tendsto
    (fun k => (harmonicMollifierBump n k).continuous_normed.comp e.symm.continuous)
    (fun k => (harmonicMollifierBump n k).hasCompactSupport_normed.comp_homeomorph e.symm.toHomeomorph)
    (fun k x => (harmonicMollifierBump n k).nonneg_normed _) hρ1
    (fun k => (harmonic_raw_mollifier_support k).trans (canonicalMollifier_support_le_one n k)) hρlim
    (hf.comp_measurePreserving hμs)
  have he (k : ℕ) : (∫ x, (scalarConvolution (ρ k) (f ∘ e.symm) x-(f ∘ e.symm) x)^2)=
      ∫ x, (harmonicMollify k f x-f x)^2 := by
    rw [← hμ.integral_comp e.toHomeomorph.measurableEmbedding]
    simp only [ρ,e,harmonicConvolution_coordinate_transport,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply]
    rfl
  change Tendsto (fun k => ∫ x, (scalarConvolution (ρ k) (f ∘ e.symm) x-(f ∘ e.symm) x)^2) atTop (𝓝 0) at hh
  simp_rw [he] at hh
  exact hh

end GaussianTilt.MomentMapLinearDirichlet
