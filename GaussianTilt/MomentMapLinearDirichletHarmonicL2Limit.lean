import GaussianTilt.MomentMapLinearDirichletHarmonicL2Mollification

/-! # Compact harmonic smoothing survives actual L² limits

Hilbert pairing continuity replaces the bounded-data dominated-convergence
hypothesis. No pointwise bound on the harmonic data is required.
-/
noncomputable section
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma harmonicSmoothing_eq_translated_pairing (χ f : KernelSpace n → ℝ) (x : KernelSpace n) :
    harmonicSmoothing χ f x=∫ z, harmonicSmoothingKernel χ (z-x)*f z := by
  have hh := (measurePreserving_add_right (volume : Measure (KernelSpace n)) x).integral_comp
    (Homeomorph.addRight x).measurableEmbedding (fun z => harmonicSmoothingKernel χ (z-x)*f z)
  simpa only [add_sub_cancel_right] using hh

lemma inner_toLp_eq_integral_mul {f g : KernelSpace n → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℝ (hf.toLp f) (hg.toLp g)=∫ x, f x*g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  simp only [hx,hy,RCLike.inner_apply,conj_trivial]
  ring

/-- Strong L² convergence gives convergence of the actual compact harmonic
smoothing at every point, with no uniform pointwise bound. -/
theorem tendsto_harmonicSmoothing_of_L2 {χ f : KernelSpace n → ℝ}
    {h : ℕ → KernelSpace n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 0] (fun _ => 1))
    (hf : MemLp f 2 volume) (hh : ∀ k, MemLp (h k) 2 volume)
    (hlim : Tendsto (fun k => ∫ x, (h k x-f x)^2) atTop (𝓝 0)) (x : KernelSpace n) :
    Tendsto (fun k => harmonicSmoothing χ (h k) x) atTop (𝓝 (harmonicSmoothing χ f x)) := by
  let H := fun k => (hh k).toLp (h k)
  let F := hf.toLp f
  have hnorm (k : ℕ) : ‖H k-F‖^2=∫ x, (h k x-f x)^2 := norm_toLp_sq_eq_integral ((hh k).sub hf)
  have hsqrt := hlim.sqrt
  simp_rw [← hnorm,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hsqrt
  have hHF : Tendsto H atTop (𝓝 F) := tendsto_iff_norm_sub_tendsto_zero.mpr hsqrt
  let g := fun z => harmonicSmoothingKernel χ (z-x)
  have hgc : HasCompactSupport g :=
    (hasCompactSupport_harmonicSmoothingKernel hχc hχ0).comp_homeomorph (Homeomorph.addRight (-x))
  have hgcont : Continuous g :=
    (contDiff_harmonicSmoothingKernel hχ hχ0).continuous.comp (continuous_id.sub continuous_const)
  have hg : MemLp g 2 volume := hgcont.memLp_of_hasCompactSupport hgc
  have hi : Tendsto (fun k => inner ℝ (hg.toLp g) (H k)) atTop (𝓝 (inner ℝ (hg.toLp g) F)) :=
    tendsto_const_nhds.inner hHF
  have hid (k : ℕ) : inner ℝ (hg.toLp g) (H k)=harmonicSmoothing χ (h k) x := by
    rw [inner_toLp_eq_integral_mul hg (hh k),harmonicSmoothing_eq_translated_pairing]
  have hiF : inner ℝ (hg.toLp g) F=harmonicSmoothing χ f x := by
    rw [inner_toLp_eq_integral_mul hg hf,harmonicSmoothing_eq_translated_pairing]
  simpa only [hid,hiF] using hi

/-- A genuine smooth representative is extracted from L² harmonic
approximations using the exact compact smoothing identity. -/
theorem exists_smooth_rep_of_L2_harmonic_approximation [NeZero n]
    {χ f : KernelSpace n → ℝ} {h : ℕ → KernelSpace n → ℝ} {U : Set (KernelSpace n)}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 0] (fun _ => 1)) (hf : MemLp f 2 volume)
    (hh : ∀ k, ContDiff ℝ 2 (h k)) (hhc : ∀ k, HasCompactSupport (h k))
    (hhLp : ∀ k, MemLp (h k) 2 volume)
    (hlim : Tendsto (fun k => ∫ x, (h k x-f x)^2) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume, Tendsto (fun k => h k x) atTop (𝓝 (f x)))
    (hharm : ∀ x ∈ U, ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ tsupport χ, kernelLaplacian (h k) (y+x)=0) :
    ∃ v : KernelSpace n → ℝ, ContDiff ℝ ∞ v ∧ ∀ᵐ x ∂volume, x ∈ U → v x=f x := by
  let C := 2*(n:ℝ)*fundamentalApproxMass n
  have hC : C ≠ 0 := by
    have hn : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    exact (mul_pos (mul_pos (by norm_num) hn) (fundamentalApproxMass_pos n)).ne'
  let v := fun x => C⁻¹*harmonicSmoothing χ f x
  refine ⟨v,contDiff_const.mul (contDiff_harmonicSmoothing hχ hχc hχ0 (hf.locallyIntegrable (by norm_num))),?_⟩
  filter_upwards [hae] with x hx hxU
  have hl := tendsto_harmonicSmoothing_of_L2 hχ hχc hχ0 hf hhLp hlim x
  have hr : Tendsto (fun k => C*h k x) atTop (𝓝 (C*f x)) := tendsto_const_nhds.mul hx
  have he : (fun k => C*h k x) =ᶠ[atTop] (fun k => harmonicSmoothing χ (h k) x) := by
    filter_upwards [hharm x hxU] with k hk
    exact harmonicSmoothingKernel_reproduces_at hχ hχ0 (hh k) (hhc k) x hk
  have hid : C*f x=harmonicSmoothing χ f x := tendsto_nhds_unique hr (hl.congr' he.symm)
  change C⁻¹*harmonicSmoothing χ f x=f x
  rw [← hid,inv_mul_cancel_left₀ hC]

end GaussianTilt.MomentMapLinearDirichlet
