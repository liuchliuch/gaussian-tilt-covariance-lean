import GaussianTilt.MomentMapLinearDirichletHarmonicTaylor

/-!
# Pointwise classical reflection across the zero flat boundary

The linear height estimate makes the genuine odd extension continuous on
the full ball. Its proved smooth AE representative is therefore equal to
it everywhere there. Smoothness across the plane and exact upper-half
agreement are conclusions, with no classical reflection theorem assumed.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma isOpen_flatUpperBall (j : Fin n) (R : ℝ) :
    IsOpen (Metric.ball (0 : KernelSpace n) R ∩ {x | 0 < x j}) :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_const (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous)

lemma flatOddExtension_height_bound (j : Fin n) {u : KernelSpace n → ℝ} {R C : ℝ}
    (hug : ∀ x ∈ Metric.ball (0 : KernelSpace n) R, |u x| ≤ C * |x j|)
    {x : KernelSpace n} (hx : x ∈ Metric.ball 0 R) :
    |flatOddExtension j u x| ≤ 2*C*|x j| := by
  have hxT : flatReflection j x ∈ Metric.ball (0 : KernelSpace n) R := by
    simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
  have h1 := hug x hx
  have h2 := hug (flatReflection j x) hxT
  have ht : |flatReflection j x j| = |x j| := by simp [flatReflection_apply]
  rw [ht] at h2
  exact (abs_sub _ _).trans (by linarith)

lemma flatOddExtension_continuousOn (j : Fin n) {u : KernelSpace n → ℝ} {R C : ℝ}
    (hu0 : ∀ x, x j ≤ 0 → u x = 0)
    (hug : ∀ x ∈ Metric.ball (0 : KernelSpace n) R, |u x| ≤ C * |x j|)
    (hu : ContinuousOn u (Metric.ball 0 R ∩ {x | 0 < x j})) :
    ContinuousOn (flatOddExtension j u) (Metric.ball 0 R) := by
  apply Metric.isOpen_ball.continuousOn_iff.mpr
  intro x hx
  by_cases hp : 0 < x j
  · have huat : ContinuousAt u x := hu.continuousAt ((isOpen_flatUpperBall j R).mem_nhds ⟨hx, hp⟩)
    apply huat.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous).mem_nhds hp]
      with y hy
    exact flatOddExtension_eq_upper j hu0 hy.le
  · by_cases hn : x j < 0
    · have hxT : flatReflection j x ∈ Metric.ball (0 : KernelSpace n) R := by
        simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
      have hxTj : 0 < flatReflection j x j := by simpa [flatReflection_apply] using neg_pos.mpr hn
      have hat : ContinuousAt u (flatReflection j x) :=
        hu.continuousAt ((isOpen_flatUpperBall j R).mem_nhds ⟨hxT, hxTj⟩)
      have hc : ContinuousAt (fun y => -u (flatReflection j y)) x :=
        (hat.comp (flatReflection j).continuous.continuousAt).neg
      apply hc.congr_of_eventuallyEq
      filter_upwards [(isOpen_lt (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous continuous_const).mem_nhds hn]
        with y hy
      rw [flatOddExtension, hu0 y hy.le, zero_sub]
    · have hx0 : x j = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      have hux : flatOddExtension j u x = 0 := by
        rw [flatOddExtension, flatReflection_fixed j hx0, sub_self]
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      simp only [hux, sub_zero, Real.norm_eq_abs]
      apply squeeze_zero' (Eventually.of_forall (fun y => abs_nonneg (flatOddExtension j u y)))
        (eventually_of_mem (Metric.isOpen_ball.mem_nhds hx) (fun y hy => flatOddExtension_height_bound j hug hy))
      have hcoord : Continuous (fun y : KernelSpace n => y j) := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous
      simpa only [hx0, abs_zero, mul_zero] using
        (tendsto_const_nhds.mul hcoord.continuousAt.tendsto.abs :
          Tendsto (fun y : KernelSpace n => 2*C*|y j|) (𝓝 x) (𝓝 (2*C*|x j|)))

/-- The reflected smooth representative agrees pointwise with the true
odd extension throughout the ball, including the flat boundary. -/
theorem flatOddExtension_smooth_rep_eqOn [NeZero n] (j : Fin n) {u : KernelSpace n → ℝ}
    (hu : MemLp u 2 volume) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hu0 : ∀ x, x j ≤ 0 → u x = 0)
    (hug : ∀ x ∈ Metric.ball (0 : KernelSpace n) R, |u x| ≤ C * |x j|)
    (huc : ContinuousOn u (Metric.ball 0 R ∩ {x | 0 < x j}))
    (heq : ∀ φ : KernelSpace n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball 0 R ∩ {x | 0 < x j} → (∫ x, u x * kernelLaplacian φ x) = 0) :
    EqOn (harmonicRepresentative (flatOddExtension j u)) (flatOddExtension j u) (Metric.ball 0 R) ∧
      (∀ x ∈ Metric.ball 0 R, ContDiffAt ℝ ∞ (flatOddExtension j u) x) := by
  obtain ⟨hAE, hreg⟩ := flatOddExtension_smooth_representative j hu hR hC hu0 hug heq
  have hc : ContinuousOn (harmonicRepresentative (flatOddExtension j u)) (Metric.ball 0 R) :=
    Metric.isOpen_ball.continuousOn_iff.mpr (fun _ hx => (hreg _ hx).continuousAt)
  have he := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hAE) Metric.isOpen_ball hc
    (flatOddExtension_continuousOn j hu0 hug huc)
  refine ⟨he, ?_⟩
  intro x hx
  exact (hreg x hx).congr_of_eventuallyEq
    (eventually_of_mem (Metric.isOpen_ball.mem_nhds hx) (fun y hy => (he hy).symm))

/-- The actual odd extension, not just an AE class, satisfies the ordinary
harmonic equation throughout the full ball. -/
theorem flatOddExtension_harmonic_on_ball [NeZero n] (j : Fin n) {u : KernelSpace n → ℝ}
    (hu : MemLp u 2 volume) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hu0 : ∀ x, x j ≤ 0 → u x = 0)
    (hug : ∀ x ∈ Metric.ball (0 : KernelSpace n) R, |u x| ≤ C * |x j|)
    (huc : ContinuousOn u (Metric.ball 0 R ∩ {x | 0 < x j}))
    (heq : ∀ φ : KernelSpace n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball 0 R ∩ {x | 0 < x j} → (∫ x, u x * kernelLaplacian φ x) = 0) :
    ∀ x ∈ Metric.ball 0 R, kernelLaplacian (flatOddExtension j u) x = 0 := by
  have hi := (flatOddExtension_memLp j hu).locallyIntegrable (by norm_num)
  have hd := flatOddExtension_distribution_harmonic j hu hR hC hu0 hug heq
  have hb : ∀ x ∈ Metric.ball (0 : KernelSpace n) R, |flatOddExtension j u x| ≤ 2*C*R := by
    intro x hx
    have hc : |x j| ≤ R := (show |x j| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j).trans
      (show ‖x‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
    exact (flatOddExtension_height_bound j hug hx).trans (mul_le_mul_of_nonneg_left hc (by positivity))
  have hlocal : ∀ x ∈ Metric.ball (0 : KernelSpace n) R, ∃ r : ℝ, 0 < r ∧
      ∃ v : KernelSpace n → ℝ, ContDiff ℝ 2 v ∧
        ∀ᵐ y ∂volume, y ∈ Metric.ball x r → v y = flatOddExtension j u y := by
    intro x hx
    obtain ⟨r, hr, v, hv, he⟩ := exists_local_smooth_rep_of_bounded_distribution_harmonic
      Metric.isOpen_ball hi hb hd hx
    exact ⟨r, hr, v, contDiff_infty.mp hv 2, he⟩
  have hP := harmonicRepresentative_laplacian_of_local_representatives Metric.isOpen_ball
    (continuous_const (y := (0 : ℝ))) hlocal (by
      intro ψ hψ hψc hψs
      simpa only [zero_mul, integral_zero] using hd ψ hψ hψc hψs)
  have he := (flatOddExtension_smooth_rep_eqOn j hu hR hC hu0 hug huc heq).1
  intro x hx
  rw [kernelLaplacian_congr_nhds (eventually_of_mem (Metric.isOpen_ball.mem_nhds hx)
    (fun y hy => (he hy).symm))]
  exact hP x hx

end GaussianTilt.MomentMapLinearDirichlet
