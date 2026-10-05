import GaussianTilt.MomentMapLinearDirichletFlatTaylorJets

/-!
# Genuine flat zero-boundary harmonic quadratic approximation

Actual weak odd reflection gives a smooth harmonic function across the
plane. The derived uniform harmonic Taylor estimate then produces a
literal quadratic polynomial, zero on the plane and harmonic everywhere,
with a cubic error controlled only by the solution's supremum.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- The uniform harmonic improvement step at a flat boundary. Every
polynomial and reflection property is proved from the actual weak equation. -/
theorem exists_flat_harmonic_quadratic_approximation [NeZero n] :
    ∃ K : ℝ, 0 < K ∧ ∀ (j : Fin n) (u : KernelSpace n → ℝ), MemLp u 2 volume →
      ∀ C : ℝ, 0 ≤ C →
      (∀ x, x j ≤ 0 → u x = 0) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ C * |x j|) →
      ContinuousOn u (Metric.ball 0 2 ∩ {x | 0 < x j}) →
      (∀ φ : KernelSpace n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball 0 2 ∩ {x | 0 < x j} → (∫ x, u x * kernelLaplacian φ x) = 0) →
      ∀ B : ℝ, 0 ≤ B → (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ B) →
      ∃ A : KernelSpace n →L[ℝ] ℝ, ∃ Q : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ,
        (∀ x, x j = 0 → flatTaylorPolynomial A Q x = 0) ∧
        (∀ x, kernelLaplacian (flatTaylorPolynomial A Q) x = 0) ∧
        (∀ z ∈ Metric.ball (0 : KernelSpace n) (1/4), 0 ≤ z j →
          |u z - flatTaylorPolynomial A Q z| ≤ K * B * ‖z‖ ^ 3) := by
  obtain ⟨K, hK, hTaylor⟩ := exists_local_harmonic_quadratic_remainder_bound (n := n)
  refine ⟨K, hK, ?_⟩
  intro j u hu C hC hu0 hug huc heq B hB hb
  let h := flatOddExtension j u
  have hs := (flatOddExtension_smooth_rep_eqOn j hu (by norm_num : (0 : ℝ) ≤ 2) hC hu0 hug huc heq).2
  have hh : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, ContDiffAt ℝ 2 h x :=
    fun x hx => contDiffAt_infty.mp (hs x hx) 2
  have hhar := flatOddExtension_harmonic_on_ball j hu (by norm_num : (0 : ℝ) ≤ 2) hC hu0 hug huc heq
  have hbound (x : KernelSpace n) (hx : x ∈ Metric.ball (0 : KernelSpace n) 2) : |h x| ≤ B := by
    by_cases hxj : 0 ≤ x j
    · rw [show h x = u x from flatOddExtension_eq_upper j hu0 hxj]
      exact hb x hx
    · have hxj0 : x j ≤ 0 := (lt_of_not_ge hxj).le
      have hxT : flatReflection j x ∈ Metric.ball (0 : KernelSpace n) 2 := by
        simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
      change |u x - u (flatReflection j x)| ≤ B
      rw [hu0 x hxj0, zero_sub, abs_neg]
      exact hb _ hxT
  have hplane (x : KernelSpace n) (hx : x j = 0) : h x = 0 := by
    change u x - u (flatReflection j x) = 0
    rw [flatReflection_fixed j hx, sub_self]
  have h0 : h 0 = 0 := hplane 0 (by simp)
  have h02 : (0 : KernelSpace n) ∈ Metric.ball 0 2 := Metric.mem_ball_self (by norm_num)
  refine ⟨fderiv ℝ h 0, fderiv ℝ (fderiv ℝ h) 0, ?_, ?_, ?_⟩
  · intro x hx
    exact flat_harmonic_taylor_zero_on_plane j (hh 0 h02) hplane x hx
  · intro x
    exact flatTaylorPolynomial_harmonic (hh 0 h02) (hhar 0 h02) x
  · intro z hz hzj
    have ht := hTaylor h hh hhar B hB hbound z hz
    rw [h0, sub_zero, show h z = u z from flatOddExtension_eq_upper j hu0 hzj] at ht
    convert ht using 1
    unfold flatTaylorPolynomial
    ring

end GaussianTilt.MomentMapLinearDirichlet
