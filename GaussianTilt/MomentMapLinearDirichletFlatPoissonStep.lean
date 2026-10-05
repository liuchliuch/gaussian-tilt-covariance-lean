import GaussianTilt.MomentMapLinearDirichletFlatReplacement

/-!
# Genuine flat Poisson quadratic improvement step

The half-ball correction is actually constructed from the Hilbert inverse
and the two quadratic barriers. Its literal weak identity cancels the
forcing, so the proved reflected harmonic Taylor theorem gives the
quadratic approximation with an explicit forcing error.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Uniform one-step boundary quadratic approximation for the actual
Poisson equation. No harmonic replacement or regularity estimate is a
hypothesis; the only analytic inputs are the literal equation and data. -/
theorem exists_flat_poisson_quadratic_step [NeZero n] :
    ∃ K : ℝ, 0 < K ∧ ∀ (j : Fin n) (u : KernelSpace n → ℝ), MemLp u 2 volume →
      ∀ C B : ℝ, 0 ≤ C → 0 ≤ B →
      (∀ x, x j ≤ 0 → u x = 0) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ C * |x j|) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ B) →
      ContinuousOn u (Metric.ball 0 2 ∩ {x | 0 < x j}) →
      ∀ f : KernelSpace n → ℝ, Continuous f → HasCompactSupport f →
      ∀ α H F : ℝ, 0 < α → α < 1 → 0 ≤ H → 0 ≤ F →
      (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2 ∩ {x | 0 < x j}, |f x| ≤ F) →
      (∀ φ : KernelSpace n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball 0 2 ∩ {x | 0 < x j} →
        (∫ x, u x * kernelLaplacian φ x) = -(∫ x, f x * φ x)) →
      ∃ A : KernelSpace n →L[ℝ] ℝ, ∃ Q : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ,
        (∀ x, x j = 0 → flatTaylorPolynomial A Q x = 0) ∧
        (∀ x, kernelLaplacian (flatTaylorPolynomial A Q) x = 0) ∧
        (∀ z ∈ Metric.ball (0 : KernelSpace n) (1/4), 0 ≤ z j →
          |u z - flatTaylorPolynomial A Q z| ≤ K * (B+4*F) * ‖z‖ ^ 3 + 4*F) := by
  obtain ⟨K, hK, hReplace⟩ := exists_flat_harmonic_replacement_bound (n := n)
  refine ⟨K, hK, ?_⟩
  intro j u hu C B hC hB hu0 hug hub huc f hfc hfs α H F hα hα1 hH hF hholder hfb heq
  obtain ⟨v, hvc, hv, hvreg, hvPDE, hv0, hvb, hvg, hvweak⟩ :=
    exists_euclidean_halfBall_poisson_correction_with_weak_identity j (R := 2) (by norm_num) hF
      f hfc hfs hα hα1 hH hholder hfb
  have hvzero (x : KernelSpace n) (hx : x j ≤ 0) : v x = 0 :=
    hv0 x (fun hh => not_lt_of_ge hx hh.2)
  have hvbound (x : KernelSpace n) (_hx : x ∈ Metric.ball (0 : KernelSpace n) 2) : |v x| ≤ 4*F := by
    simpa only [show (2 : ℝ)^2 = 4 by norm_num, mul_comm F 4] using hvb x
  have hvheight (x : KernelSpace n) (_hx : x ∈ Metric.ball (0 : KernelSpace n) 2) :
      |v x| ≤ (4*F)*|x j| := by
    convert hvg x using 1 <;> ring
  exact hReplace j u v hu hv C (4*F) B (4*F) hC (by positivity) hB (by positivity)
    hu0 hvzero hug hvheight hub hvbound huc hvc
    (fun φ hφ hφc hφs => (heq φ hφ hφc hφs).trans (hvweak φ hφ hφc hφs).symm)

end GaussianTilt.MomentMapLinearDirichlet
