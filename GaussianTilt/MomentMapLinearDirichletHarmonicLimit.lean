import GaussianTilt.MomentMapLinearDirichletHarmonicKernel
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Harmonic smoothing survives genuine bounded almost-everywhere limits

The explicitly constructed compact smoothing kernel is infinitely smooth.
Dominated convergence passes its exact reproduction identity to bounded
almost-everywhere limits of actual harmonic approximations, producing a
smooth representative rather than assuming one.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Convolution
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def harmonicSmoothing (χ f : KernelSpace n → ℝ) (x : KernelSpace n) : ℝ :=
  ∫ y, harmonicSmoothingKernel χ y * f (y + x)

lemma harmonicSmoothing_eq_convolution (χ f : KernelSpace n → ℝ) :
    harmonicSmoothing χ f = convolution (fun y => harmonicSmoothingKernel χ (-y)) f
      (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  symm
  change (∫ y, harmonicSmoothingKernel χ (-y) * f (x - y)) = _
  convert integral_neg_eq_self (fun y => harmonicSmoothingKernel χ y * f (y + x)) volume using 1
  congr 1
  funext y
  rw [sub_eq_add_neg, add_comm x]

lemma contDiff_harmonicSmoothing {χ f : KernelSpace n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 0] (fun _ => 1)) (hf : LocallyIntegrable f volume) :
    ContDiff ℝ ∞ (harmonicSmoothing χ f) := by
  rw [harmonicSmoothing_eq_convolution]
  exact ((hasCompactSupport_harmonicSmoothingKernel hχc hχ0).comp_homeomorph (Homeomorph.neg _)).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    ((contDiff_harmonicSmoothingKernel hχ hχ0).comp contDiff_id.neg) hf

/-- The smooth kernel pairing genuinely converges at every center under
bounded almost-everywhere convergence. -/
theorem tendsto_harmonicSmoothing {χ f : KernelSpace n → ℝ}
    {h : ℕ → KernelSpace n → ℝ} {B : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 0] (fun _ => 1))
    (hh : ∀ k, Continuous (h k)) (hb : ∀ k y, |h k y| ≤ B)
    (hlim : ∀ᵐ y ∂volume, Tendsto (fun k => h k y) atTop (𝓝 (f y))) (x : KernelSpace n) :
    Tendsto (fun k => harmonicSmoothing χ (h k) x) atTop (𝓝 (harmonicSmoothing χ f x)) := by
  have hg := (contDiff_harmonicSmoothingKernel hχ hχ0).continuous
  have hgc := hasCompactSupport_harmonicSmoothingKernel hχc hχ0
  apply tendsto_integral_of_dominated_convergence (fun y => |harmonicSmoothingKernel χ y| * B)
  · intro k
    exact (hg.mul ((hh k).comp (continuous_id.add continuous_const))).aestronglyMeasurable
  · exact (hg.norm.integrable_of_hasCompactSupport (hgc.comp_left norm_zero)).mul_const B
  · intro k
    exact ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hb k (y + x)) (abs_nonneg _))
  · filter_upwards [(measurePreserving_add_right (volume : Measure (KernelSpace n)) x).quasiMeasurePreserving.ae hlim]
      with y hy
    exact tendsto_const_nhds.mul hy

/-- A genuine smooth representative follows from actual locally harmonic
approximations and their bounded AE limit. The smoothing kernel and all
regularity of the resulting representative are conclusions. -/
theorem exists_smooth_rep_of_harmonic_approximation [NeZero n]
    {χ f : KernelSpace n → ℝ} {h : ℕ → KernelSpace n → ℝ}
    {U : Set (KernelSpace n)} {B : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 0] (fun _ => 1)) (hf : LocallyIntegrable f volume)
    (hh : ∀ k, ContDiff ℝ 2 (h k)) (hhc : ∀ k, HasCompactSupport (h k))
    (hb : ∀ k y, |h k y| ≤ B)
    (hlim : ∀ᵐ y ∂volume, Tendsto (fun k => h k y) atTop (𝓝 (f y)))
    (hharm : ∀ x ∈ U, ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ tsupport χ, kernelLaplacian (h k) (y + x) = 0) :
    ∃ v : KernelSpace n → ℝ, ContDiff ℝ ∞ v ∧
      ∀ᵐ x ∂volume, x ∈ U → v x = f x := by
  let C := 2 * (n : ℝ) * fundamentalApproxMass n
  have hC : C ≠ 0 := by
    have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    exact (mul_pos (mul_pos (by norm_num) hn) (fundamentalApproxMass_pos n)).ne'
  let v := fun x => C⁻¹ * harmonicSmoothing χ f x
  refine ⟨v, contDiff_const.mul (contDiff_harmonicSmoothing hχ hχc hχ0 hf), ?_⟩
  filter_upwards [hlim] with x hx hxU
  have hl := tendsto_harmonicSmoothing hχ hχc hχ0 (fun k => (hh k).continuous) hb hlim x
  have hr : Tendsto (fun k => C * h k x) atTop (𝓝 (C * f x)) := tendsto_const_nhds.mul hx
  have heq : (fun k => C * h k x) =ᶠ[atTop] (fun k => harmonicSmoothing χ (h k) x) := by
    filter_upwards [hharm x hxU] with k hk
    exact harmonicSmoothingKernel_reproduces_at hχ hχ0 (hh k) (hhc k) x hk
  have he : C * f x = harmonicSmoothing χ f x := tendsto_nhds_unique (hr.congr' heq) hl
  dsimp [v]
  rw [← he, inv_mul_cancel_left₀ hC]

end GaussianTilt.MomentMapLinearDirichlet
