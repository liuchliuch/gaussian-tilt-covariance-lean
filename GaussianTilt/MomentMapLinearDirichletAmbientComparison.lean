import GaussianTilt.MomentMapLinearDirichletIdeal

/-!
# Weak comparison against genuine nonzero-boundary barriers

The positive-part order ideal theorem supplies an admissible zero-boundary
test even when the supersolution lives only in a larger ambient Sobolev
space. The comparison statement therefore does not assume zero trace of
the barrier or of a proposed truncation.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma dirichletEnergy_inclusion {Ω U : Set (CoordinateSpace n)} (h : Ω ⊆ U)
    (u v : dirichletSobolev Ω) :
    dirichletEnergy U (dirichletInclusion h u) (dirichletInclusion h v) = dirichletEnergy Ω u v := by
  simp only [dirichletEnergy_apply]
  rfl

lemma nonpos_of_dirichletPositivePart_eq_zero {U : Set (CoordinateSpace n)}
    (u : dirichletSobolev U) (hu : dirichletPositivePart u = 0) : dirichletValue U u ≤ 0 := by
  have hh := dirichletPositivePart_value u
  rw [hu, map_zero] at hh
  have hsum : dirichletValue U u + |dirichletValue U u| = 0 :=
    (smul_eq_zero.mp hh.symm).resolve_left (by norm_num)
  rw [eq_neg_of_add_eq_zero_left hsum]
  exact neg_nonpos.mpr (abs_nonneg _)

/-- Actual comparison with an ambient nonnegative weak supersolution. -/
theorem dirichletSobolev_le_ambient_supersolution {Ω U : Set (CoordinateSpace n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΩU : Ω ⊆ U)
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R)
    (u : dirichletSobolev Ω) (v : dirichletSobolev U) (hv : 0 ≤ dirichletValue U v)
    (he : ∀ z : dirichletSobolev Ω, 0 ≤ dirichletValue Ω z →
      dirichletEnergy U (dirichletInclusion hΩU u) (dirichletInclusion hΩU z) ≤
        dirichletEnergy U v (dirichletInclusion hΩU z)) :
    dirichletValue Ω u ≤ dirichletValue U v := by
  let q := dirichletInclusion hΩU u - v
  let p := dirichletPositivePart q
  have hp : p.1 ∈ dirichletSobolev Ω := dirichletPositivePart_sub_mem hΩ hΩb hΩU u v hv
  let z : dirichletSobolev Ω := ⟨p.1, hp⟩
  have hiz : dirichletInclusion hΩU z = p := rfl
  have hz0 : 0 ≤ dirichletValue Ω z := dirichletPositivePart_nonneg q
  have hE : dirichletEnergy Ω z z ≤ 0 := by
    have hpos := dirichletPositivePart_energy q
    change dirichletEnergy U p p ≤ dirichletEnergy U q p at hpos
    have htest := he z hz0
    rw [hiz] at htest
    have hq : dirichletEnergy U q p ≤ 0 := by
      change dirichletEnergy U (dirichletInclusion hΩU u - v) p ≤ 0
      simp only [map_sub, ContinuousLinearMap.sub_apply]
      exact sub_nonpos.mpr htest
    have hid : dirichletEnergy Ω z z = dirichletEnergy U p p :=
      (dirichletEnergy_inclusion hΩU z z).symm
    rw [hid]
    exact hpos.trans hq
  have hbound := dirichlet_norm_sq_le_energy i hR hstrip z
  have hznorm : ‖z‖ = 0 := by
    have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1 + 4 * R ^ 2 by positivity) hE
    nlinarith [norm_nonneg z]
  have hz : z = 0 := norm_eq_zero.mp hznorm
  have hp0 : p = 0 := by rw [← hiz, hz, map_zero]
  have hq := nonpos_of_dirichletPositivePart_eq_zero q hp0
  change dirichletValue U (dirichletInclusion hΩU u - v) ≤ 0 at hq
  rw [map_sub, dirichletInclusion_value] at hq
  exact sub_nonpos.mp hq

/-- The actual weak Laplace inverse is bounded by every ambient
nonnegative supersolution for its load. -/
theorem weakDirichletLaplaceSolution_le_ambient {Ω U : Set (CoordinateSpace n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΩU : Ω ⊆ U)
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (v : dirichletSobolev U) (hv : 0 ≤ dirichletValue U v)
    (he : ∀ z : dirichletSobolev Ω, 0 ≤ dirichletValue Ω z →
      inner ℝ f (dirichletValue Ω z) ≤ dirichletEnergy U v (dirichletInclusion hΩU z)) :
    dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip f) ≤ dirichletValue U v := by
  apply dirichletSobolev_le_ambient_supersolution hΩ hΩb hΩU i hR hstrip
    (weakDirichletLaplaceSolution i hR hstrip f) v hv
  intro z hz
  rw [dirichletEnergy_inclusion, weakDirichletLaplaceSolution_equation]
  exact he z hz

end GaussianTilt.MomentMapLinearDirichlet
