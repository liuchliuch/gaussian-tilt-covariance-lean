import GaussianTilt.MomentMapLinearDirichletPoissonInterior

/-!
# The genuine pointwise equation of the regular representative

The local distributional fundamental lemma and actual Green integration
by parts upgrade the literal weak equation to the pointwise Laplacian.
Almost-everywhere local representatives patch by canonical mollifier
limits, so both regularity and the classical equation are conclusions.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- A genuinely C² function satisfying the literal local distributional
Poisson equation satisfies the ordinary equation at every interior point. -/
theorem kernelLaplacian_eq_of_distribution {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω)
    {q f : KernelSpace n → ℝ} (hq : ContDiff ℝ 2 q) (hf : Continuous f)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, q y * kernelLaplacian ψ y) = ∫ y, f y * ψ y) :
    ∀ x ∈ Ω, kernelLaplacian q x = f x := by
  have hc : Continuous (fun x => kernelLaplacian q x - f x) :=
    (continuous_kernelLaplacian hq).sub hf
  have hae : ∀ᵐ x ∂volume, x ∈ Ω → kernelLaplacian q x - f x = 0 :=
    hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hc.continuousOn.locallyIntegrableOn hΩ.measurableSet) (by
        intro ψ hψ hψc hψΩ
        have hg := integral_mul_kernelLaplacian_swap (contDiff_infty.mp hψ 2) hq hψc
        have hu := heq ψ hψ hψc hψΩ
        have hright : (∫ y, kernelLaplacian ψ y * q y) = ∫ y, q y * kernelLaplacian ψ y := by
          apply integral_congr_ae; exact ae_of_all _ (fun y => mul_comm _ _)
        have hforce : (∫ y, ψ y * f y) = ∫ y, f y * ψ y := by
          apply integral_congr_ae; exact ae_of_all _ (fun y => mul_comm _ _)
        simp only [smul_eq_mul, mul_sub]
        rw [integral_sub (integrable_compact_mul hψ.continuous hψc (continuous_kernelLaplacian hq))
          (integrable_compact_mul hψ.continuous hψc hf), hg, hright, hu, hforce, sub_self])
  have he := Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hΩ.measurableSet).mpr hae)
    hΩ hc.continuousOn continuousOn_const
  intro x hx
  exact sub_eq_zero.mp (he hx)

/-- Local AE agreement with a C² function transfers the weak equation
on the actual open neighborhood. -/
theorem kernelLaplacian_eq_of_local_representative {Ω V : Set (KernelSpace n)}
    (hV : IsOpen V) (hVΩ : V ⊆ Ω) {u q f : KernelSpace n → ℝ}
    (hq : ContDiff ℝ 2 q) (hf : Continuous f)
    (huq : ∀ᵐ y ∂volume, y ∈ V → q y = u y)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y * kernelLaplacian ψ y) = ∫ y, f y * ψ y) :
    ∀ x ∈ V, kernelLaplacian q x = f x := by
  apply kernelLaplacian_eq_of_distribution hV hq hf
  intro ψ hψ hψc hψV
  rw [← heq ψ hψ hψc (hψV.trans hVΩ)]
  apply integral_congr_ae
  filter_upwards [huq] with y hy
  by_cases hyV : y ∈ V
  · rw [hy hyV]
  · rw [kernelLaplacian_zero_off_tsupport ψ (fun hh => hyV (hψV hh)), mul_zero, mul_zero]

/-- Proved local C² representatives of a distributional solution yield
the actual pointwise PDE for their one canonical representative. -/
theorem harmonicRepresentative_laplacian_of_local_representatives
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) {u f : KernelSpace n → ℝ} (hf : Continuous f)
    (hlocal : ∀ x ∈ Ω, ∃ r : ℝ, 0 < r ∧ ∃ v : KernelSpace n → ℝ,
      ContDiff ℝ 2 v ∧ ∀ᵐ y ∂volume, y ∈ Metric.ball x r → v y = u y)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y * kernelLaplacian ψ y) = ∫ y, f y * ψ y) :
    ∀ x ∈ Ω, kernelLaplacian (harmonicRepresentative u) x = f x := by
  intro x hx
  obtain ⟨r, hr, v, hv, hvu⟩ := hlocal x hx
  let V := Metric.ball x r ∩ Ω
  have hVo : IsOpen V := Metric.isOpen_ball.inter hΩ
  have hxV : x ∈ V := ⟨Metric.mem_ball_self hr, hx⟩
  have hvuV : ∀ᵐ y ∂volume, y ∈ V → v y = u y := by
    filter_upwards [hvu] with y hy hym
    exact hy hym.1
  have hvPDE := kernelLaplacian_eq_of_local_representative hVo inter_subset_right hv hf hvuV heq x hxV
  have he := harmonicRepresentative_eqOn_of_local_ae_eq hVo hv.continuous (by
    filter_upwards [hvuV] with y hy hym
    exact (hy hym).symm)
  rw [kernelLaplacian_congr_nhds (eventually_of_mem (hVo.mem_nhds hxV) he)]
  exact hvPDE

/-- The genuine smooth-data interior weak-to-classical endpoint includes
both C² regularity and the literal pointwise Poisson equation. -/
theorem harmonicRepresentative_classical_of_smooth_distribution_poisson [NeZero n]
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {u f : KernelSpace n → ℝ} (hu : LocallyIntegrable u volume)
    {B : ℝ} (huB : ∀ x ∈ Ω, |u x| ≤ B)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y * kernelLaplacian ψ y) = ∫ y, f y * ψ y) :
    (∀ x ∈ Ω, ContDiffAt ℝ 2 (harmonicRepresentative u) x) ∧
      (∀ x ∈ Ω, kernelLaplacian (harmonicRepresentative u) x = f x) := by
  let C := 2 * (n : ℝ) * fundamentalApproxMass n
  have hC : C ≠ 0 := by
    have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    exact (mul_pos (mul_pos (by norm_num) hn) (fundamentalApproxMass_pos n)).ne'
  let q := fun x => C⁻¹ * newtonianPotential f x
  have hq : ContDiff ℝ 2 q := contDiff_const.mul (contDiff_infty.mp (smooth_newtonianPotential hf hfc) 2)
  have hqlap (x : KernelSpace n) : kernelLaplacian q x = f x := by
    rw [kernelLaplacian_const_mul_smooth _ (smooth_newtonianPotential hf hfc), newtonianPotential_laplacian hf hfc]
    exact inv_mul_cancel_left₀ hC _
  have hlocal := fun x hx => exists_local_C2_rep_of_distribution_poisson_particular hΩ hΩb hu huB hq
    (fun y _ => hqlap y) heq (x₀ := x) hx
  exact ⟨contDiffAt_harmonicRepresentative_of_local_representatives hlocal,
    harmonicRepresentative_laplacian_of_local_representatives hΩ hf.continuous hlocal heq⟩

end GaussianTilt.MomentMapLinearDirichlet
