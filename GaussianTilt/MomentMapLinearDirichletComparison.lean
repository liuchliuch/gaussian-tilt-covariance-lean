import GaussianTilt.MomentMapLinearDirichletMaximum

/-!
# Weak subsolution comparison from the actual Dirichlet lattice

The positive part is constructed inside the genuine closure of compact
interior jets. The proved absolute-value energy contraction yields the
positive-part energy inequality, hence the weak subsolution maximum
principle and comparison with weak supersolutions.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The actual positive part belongs to H₀¹, with the energy inequality
needed to test a weak subsolution. -/
theorem exists_positivePart_dirichletSobolev {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) :
    ∃ v : dirichletSobolev Ω,
      dirichletValue Ω v = (2 : ℝ)⁻¹ • (dirichletValue Ω u + |dirichletValue Ω u|) ∧
      0 ≤ dirichletValue Ω v ∧
      dirichletEnergy Ω v v ≤ dirichletEnergy Ω u v := by
  obtain ⟨a, ha, _, hEa⟩ := exists_abs_dirichletSobolev u
  let v : dirichletSobolev Ω := (2 : ℝ)⁻¹ • (u + a)
  have hv : dirichletValue Ω v =
      (2 : ℝ)⁻¹ • (dirichletValue Ω u + |dirichletValue Ω u|) := by
    simp [v, ha]
  refine ⟨v, hv, ?_, ?_⟩
  · rw [hv]
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [Lp.coeFn_smul ((2 : ℝ)⁻¹) (dirichletValue Ω u + |dirichletValue Ω u|),
      Lp.coeFn_add (dirichletValue Ω u) |dirichletValue Ω u|,
      Lp.coeFn_abs (dirichletValue Ω u)] with x hx hy hz
    simp only [hx, hy, hz, Pi.smul_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul]
    have hh := neg_le_abs (dirichletValue Ω u x)
    exact mul_nonneg (by norm_num) (by linarith)
  · have hsym := dirichletEnergy_symm Ω a u
    dsimp [v]
    simp only [map_smul, ContinuousLinearMap.smul_apply, map_add,
      ContinuousLinearMap.add_apply, smul_eq_mul]
    linarith

/-- A genuine weak maximum principle with nonpositive forcing, expressed
only through the actual energy and nonnegative H₀¹ tests. -/
theorem dirichletSobolev_nonpos_of_subsolution {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (u : dirichletSobolev Ω)
    (hu : ∀ v : dirichletSobolev Ω, 0 ≤ dirichletValue Ω v →
      dirichletEnergy Ω u v ≤ 0) :
    dirichletValue Ω u ≤ 0 := by
  obtain ⟨v, hv, hv0, hEv⟩ := exists_positivePart_dirichletSobolev u
  have hE : dirichletEnergy Ω v v ≤ 0 := hEv.trans (hu v hv0)
  have hbound := dirichlet_norm_sq_le_energy i hR hΩ v
  have hnorm : ‖v‖ = 0 := by
    have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1 + 4 * R ^ 2 by positivity) hE
    nlinarith [norm_nonneg v]
  have hvzero : v = 0 := norm_eq_zero.mp hnorm
  have hsum : dirichletValue Ω u + |dirichletValue Ω u| = 0 := by
    rw [hvzero, map_zero] at hv
    exact (smul_eq_zero.mp hv.symm).resolve_left (by norm_num)
  rw [eq_neg_of_add_eq_zero_left hsum]
  exact neg_nonpos.mpr (abs_nonneg _)

/-- Comparison for actual weak sub- and supersolutions in H₀¹. -/
theorem dirichletSobolev_le_of_energy_le {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (u v : dirichletSobolev Ω)
    (huv : ∀ z : dirichletSobolev Ω, 0 ≤ dirichletValue Ω z →
      dirichletEnergy Ω u z ≤ dirichletEnergy Ω v z) :
    dirichletValue Ω u ≤ dirichletValue Ω v := by
  have hh := dirichletSobolev_nonpos_of_subsolution i hR hΩ (u - v) (by
    intro z hz
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    exact sub_nonpos.mpr (huv z hz))
  rw [map_sub] at hh
  exact sub_nonpos.mp hh

/-- The constructed weak inverse lies below every actual H₀¹ weak
supersolution for the same load. -/
theorem weakDirichletLaplaceSolution_le_supersolution {Ω : Set (CoordinateSpace n)}
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (v : dirichletSobolev Ω)
    (hv : ∀ z : dirichletSobolev Ω, 0 ≤ dirichletValue Ω z →
      inner ℝ f (dirichletValue Ω z) ≤ dirichletEnergy Ω v z) :
    dirichletValue Ω (weakDirichletLaplaceSolution i hR hΩ f) ≤ dirichletValue Ω v := by
  apply dirichletSobolev_le_of_energy_le i hR hΩ
  intro z hz
  rw [weakDirichletLaplaceSolution_equation]
  exact hv z hz

end GaussianTilt.MomentMapLinearDirichlet
