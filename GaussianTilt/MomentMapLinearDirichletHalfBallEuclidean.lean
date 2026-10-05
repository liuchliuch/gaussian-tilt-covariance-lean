import GaussianTilt.MomentMapLinearDirichletHalfBallCorrection

/-! # The actual half-ball correction in Euclidean coordinates -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Genuine zero-boundary Poisson correction on the Euclidean half-ball.
The spherical sup bound and linear flat-boundary height bound are proved
from the actual weak inverse, with the correct pointwise Poisson equation. -/
theorem exists_euclidean_halfBall_poisson_correction_with_weak_identity [NeZero n]
    (j : Fin n) {R F α H : ℝ} (hR : 0 < R) (hF : 0 ≤ F)
    (f : KernelSpace n → ℝ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α)
    (hfb : ∀ x ∈ Metric.ball (0 : KernelSpace n) R ∩ {x | 0 < x j}, |f x| ≤ F) :
    ∃ v : KernelSpace n → ℝ, Continuous v ∧ MemLp v 2 volume ∧
      (∀ x ∈ Metric.ball (0 : KernelSpace n) R ∩ {x | 0 < x j}, ContDiffAt ℝ 2 v x) ∧
      (∀ x ∈ Metric.ball (0 : KernelSpace n) R ∩ {x | 0 < x j}, kernelLaplacian v x = -f x) ∧
      (∀ x ∉ Metric.ball (0 : KernelSpace n) R ∩ {x | 0 < x j}, v x = 0) ∧
      (∀ x, |v x| ≤ F * R ^ 2) ∧
      (∀ x, |v x| ≤ 2 * F * R * |x j|) ∧
      (∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball (0 : KernelSpace n) R ∩ {x | 0 < x j} →
        (∫ x, v x * kernelLaplacian ψ x) = -(∫ x, f x * ψ x)) := by
  let L := dirichletCoordinateEquiv n
  have hLeq : coordinateEquiv n = L := rfl
  let g := f ∘ L.symm
  have hgc : Continuous g := hfc.comp L.symm.continuous
  have hgs : HasCompactSupport g := hfs.comp_homeomorph L.symm.toHomeomorph
  let K := H * ‖L.symm.toContinuousLinearMap‖ ^ α
  have hK : 0 ≤ K := mul_nonneg hH (Real.rpow_nonneg (norm_nonneg _) _)
  have hgh : ∀ x y : CoordinateSpace n, |g x - g y| ≤ K * ‖x - y‖ ^ α := by
    intro x y
    have hh := hholder (L.symm x) (L.symm y)
    rw [← map_sub] at hh
    apply hh.trans
    have hp := Real.rpow_le_rpow (norm_nonneg _) (L.symm.toContinuousLinearMap.le_opNorm (x - y)) hα.le
    have hm := mul_le_mul_of_nonneg_left hp hH
    rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] at hm
    exact hm.trans_eq (by dsimp [K]; ring)
  have hmem (x : KernelSpace n) : L x ∈ coordinateHalfBall j R ↔
      x ∈ Metric.ball (0 : KernelSpace n) R ∩ {x | 0 < x j} := by
    simp only [coordinateHalfBall, mem_setOf_eq, hLeq, ContinuousLinearEquiv.symm_apply_apply,
      mem_inter_iff, Metric.mem_ball, dist_zero_right]
    rfl
  have hgb : ∀ x ∈ coordinateHalfBall j R, |g x| ≤ F := by
    intro x hx
    apply hfb (L.symm x)
    apply (hmem (L.symm x)).mp
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hx
  obtain ⟨v, hv, hvLp, hvC2, hvP, hv0, hvB, hvheight, hvweak⟩ :=
    exists_halfBall_poisson_correction_with_weak_identity j hR hF g hgc hgs hα hα1 hK hgh hgb
  refine ⟨v ∘ L, hv.comp L.continuous, hvLp.comp_measurePreserving ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact PiLp.volume_preserving_ofLp (Fin n)
  · intro x hx
    exact (hvC2 (L x) ((hmem x).mpr hx)).comp x L.contDiff.contDiffAt
  · intro x hx
    rw [kernelLaplacian_ofLp_any, hvP (L x) ((hmem x).mpr hx)]
    simp only [g, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  · intro x hx
    exact hv0 (L x) (fun h => hx ((hmem x).mp h))
  · intro x
    exact hvB (L x)
  · intro x
    exact hvheight (L x)

  · intro ψ hψ hψc hψΩ
    have heq : ∀ q : CoordinateSpace n → ℝ, ContDiff ℝ ∞ q → HasCompactSupport q →
        tsupport q ⊆ coordinateHalfBall j R →
        (∫ x, v x * euclideanLaplacian q x) = ∫ x, (-g x) * q x := by
      intro q hq hqc hqΩ
      rw [hvweak q hq hqc hqΩ]
      simp only [neg_mul, integral_neg]
    have hh := distribution_poisson_ofLp heq ψ hψ hψc (fun x hx => (hmem x).mpr (hψΩ hx))
    simpa only [g, Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, neg_mul, integral_neg] using hh

theorem exists_euclidean_halfBall_poisson_correction [NeZero n]
    (j : Fin n) {R F α H : ℝ} (hR : 0 < R) (hF : 0 ≤ F)
    (f : KernelSpace n → ℝ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α)
    (hfb : ∀ x ∈ Metric.ball (0 : KernelSpace n) R ∩ {x | 0 < x j}, |f x| ≤ F) :
    ∃ v : KernelSpace n → ℝ, Continuous v ∧ MemLp v 2 volume ∧
      (∀ x ∈ Metric.ball (0 : KernelSpace n) R ∩ {x | 0 < x j}, ContDiffAt ℝ 2 v x) ∧
      (∀ x ∈ Metric.ball (0 : KernelSpace n) R ∩ {x | 0 < x j}, kernelLaplacian v x = -f x) ∧
      (∀ x ∉ Metric.ball (0 : KernelSpace n) R ∩ {x | 0 < x j}, v x = 0) ∧
      (∀ x, |v x| ≤ F * R ^ 2) ∧
      (∀ x, |v x| ≤ 2 * F * R * |x j|) := by
  obtain ⟨v, hv, hl, hc, hp, hz, hb, hh, _⟩ := exists_euclidean_halfBall_poisson_correction_with_weak_identity
    j hR hF f hfc hfs hα hα1 hH hholder hfb
  exact ⟨v, hv, hl, hc, hp, hz, hb, hh⟩

end GaussianTilt.MomentMapLinearDirichlet
