import GaussianTilt.MomentMapSchauderBoundaryVariableForcing

/-! # Honest compact localization across a zero flat boundary -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

lemma continuousOn_zero_upper_of_growth (j : Fin n) {u : KernelSpace n → ℝ} {R L : ℝ}
    (hu0 : ∀ x, x j ≤ 0 → u x=0)
    (hug : ∀ x ∈ Metric.ball (0 : KernelSpace n) R, |u x| ≤ L*|x j|)
    (hu : ContinuousOn u (flatUpperBall j R)) : ContinuousOn u (Metric.ball 0 R) := by
  apply Metric.isOpen_ball.continuousOn_iff.mpr
  intro x hx
  by_cases hp : 0 < x j
  · exact hu.continuousAt ((isOpen_flatUpperBall j R).mem_nhds ⟨hx,hp⟩)
  · by_cases hn : x j < 0
    · apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [(isOpen_lt (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous continuous_const).mem_nhds hn] with y hy
      exact hu0 y hy.le
    · have hx0 : x j=0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      rw [hu0 x hx0.le]
      simp only [sub_zero,Real.norm_eq_abs]
      apply squeeze_zero' (Eventually.of_forall (fun y => abs_nonneg (u y)))
        (eventually_of_mem (Metric.isOpen_ball.mem_nhds hx) (fun y hy => hug y hy))
      have hcoord : Continuous (fun y : KernelSpace n => y j) := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous
      simpa only [hx0,abs_zero,mul_zero] using
        (tendsto_const_nhds.mul hcoord.continuousAt.tendsto.abs :
          Tendsto (fun y : KernelSpace n => L*|y j|) (𝓝 x) (𝓝 (L*|x j|)))

lemma continuous_cutoff_mul_of_continuousOn {u χ : KernelSpace n → ℝ} {U : Set (KernelSpace n)}
    (hU : IsOpen U) (hu : ContinuousOn u U) (hχ : Continuous χ) (hs : tsupport χ ⊆ U) :
    Continuous (fun x => χ x*u x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hχ.continuousAt.mul (hu.continuousAt (hU.mem_nhds hx))
  · have hn : x ∉ tsupport χ := fun hh => hx (hs hh)
    have he : (fun y => χ y*u y) =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      change χ y=0 at hy
      rw [hy,zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq he

/-- The localized zero extension is an actual L² function. Its C²
regularity is asserted only on the upper side, where it is proved. -/
theorem boundary_cutoff_classical_data (j : Fin n) {u χ : KernelSpace n → ℝ}
    (hu0 : ∀ x, x j ≤ 0 → u x=0) (hu : ContDiffOn ℝ 2 u (flatUpperBall j 2))
    {L : ℝ} (hL : 0 ≤ L) (hug : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ L*|x j|)
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hs : tsupport χ ⊆ Metric.ball 0 2)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) :
    MemLp (fun x => χ x*u x) 2 volume ∧ (∀ x, x j ≤ 0 → χ x*u x=0) ∧
      ContDiffOn ℝ 2 (fun x => χ x*u x) (flatUpperBall j 2) ∧
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |χ x*u x| ≤ L*|x j|) := by
  have hc := continuous_cutoff_mul_of_continuousOn Metric.isOpen_ball
    (continuousOn_zero_upper_of_growth j hu0 hug hu.continuousOn) hχ.continuous hs
  refine ⟨hc.memLp_of_hasCompactSupport (hχs.mul_right),fun x hx => by rw [hu0 x hx,mul_zero],
    (contDiff_infty.mp hχ 2).contDiffOn.mul hu,?_⟩
  intro x hx
  rw [abs_mul,abs_of_nonneg (hχ0 x)]
  exact (mul_le_mul_of_nonneg_right (hχ1 x) (abs_nonneg _)).trans (by simpa only [one_mul] using hug x hx)

/-- On the smaller ball the true cutoff field agrees with the original
closure Hessian, including points on the flat boundary. -/
lemma boundaryCutoffSecond_eq_of_one_neighborhood {u χ : KernelSpace n → ℝ}
    (D : KernelSpace n → KernelSpace n →L[ℝ] ℝ)
    (B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ)
    {x : KernelSpace n} (hχ : χ =ᶠ[𝓝 x] (fun _ => 1)) :
    boundaryCutoffSecond χ u D B x=B x := by
  have h0 := hχ.self_of_nhds
  have h1 : fderiv ℝ χ x=0 := by rw [hχ.fderiv_eq]; simp
  have h2 : fderiv ℝ (fderiv ℝ χ) x=0 := by rw [hχ.fderiv.fderiv_eq]; simp
  simp only [boundaryCutoffSecond,h0,h1,h2,one_smul,smul_zero,add_zero]
  ext v w
  simp

end GaussianTilt.MomentMapSchauder
