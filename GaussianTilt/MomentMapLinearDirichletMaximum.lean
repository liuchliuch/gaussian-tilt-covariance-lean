import GaussianTilt.MomentMapLinearDirichletMarkov

/-!
# Genuine weak maximum principle for the constructed Dirichlet inverse

The actual H₀¹ absolute-value contraction and the proved variational
identity imply positivity and comparison of the weak Laplace inverse.
There is no weak maximum-principle or Sobolev truncation premise.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma dirichletEnergy_symm (Ω : Set (CoordinateSpace n)) (u v : dirichletSobolev Ω) :
    dirichletEnergy Ω u v = dirichletEnergy Ω v u := by
  rw [dirichletEnergy_apply, dirichletEnergy_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_comm _ _

lemma dirichletEnergy_sub_self (Ω : Set (CoordinateSpace n)) (v u : dirichletSobolev Ω) :
    dirichletEnergy Ω (v - u) (v - u) =
      dirichletEnergy Ω v v - 2 * dirichletEnergy Ω u v + dirichletEnergy Ω u u := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [dirichletEnergy_symm Ω v u]
  ring

/-- The constructed weak solution is the unique minimizer of its actual
Dirichlet energy minus twice the load pairing. -/
theorem weakDirichletLaplaceSolution_minimizer {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (v : dirichletSobolev Ω)
    (hv : dirichletEnergy Ω v v - 2 * inner ℝ f (dirichletValue Ω v) ≤
      dirichletEnergy Ω (weakDirichletLaplaceSolution i hR hΩ f) (weakDirichletLaplaceSolution i hR hΩ f) -
        2 * inner ℝ f (dirichletValue Ω (weakDirichletLaplaceSolution i hR hΩ f))) :
    v = weakDirichletLaplaceSolution i hR hΩ f := by
  let u := weakDirichletLaplaceSolution i hR hΩ f
  have hEu : dirichletEnergy Ω u u = inner ℝ f (dirichletValue Ω u) :=
    weakDirichletLaplaceSolution_equation i hR hΩ f u
  have hEuv : dirichletEnergy Ω u v = inner ℝ f (dirichletValue Ω v) :=
    weakDirichletLaplaceSolution_equation i hR hΩ f v
  have hE : dirichletEnergy Ω (v - u) (v - u) ≤ 0 := by
    rw [dirichletEnergy_sub_self, hEuv]
    change dirichletEnergy Ω v v - 2 * inner ℝ f (dirichletValue Ω v) ≤
      dirichletEnergy Ω u u - 2 * inner ℝ f (dirichletValue Ω u) at hv
    linarith
  have hbound := dirichlet_norm_sq_le_energy i hR hΩ (v - u)
  have hnorm : ‖v - u‖ = 0 := by
    have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1 + 4 * R ^ 2 by positivity) hE
    nlinarith [norm_nonneg (v - u)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

lemma inner_L2_nonneg_of_nonneg
    {f g : Lp ℝ 2 (volume : Measure (CoordinateSpace n))} (hf : 0 ≤ f) (hg : 0 ≤ g) :
    0 ≤ inner ℝ f g := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf, (Lp.coeFn_nonneg g).mpr hg] with x hx hy
  simpa only [RCLike.inner_apply, conj_trivial, Pi.zero_apply] using mul_nonneg hy hx

lemma inner_L2_abs_ge_of_nonneg
    {f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))} (hf : 0 ≤ f)
    (g : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) : inner ℝ f g ≤ inner ℝ f |g| := by
  have hh := inner_L2_nonneg_of_nonneg hf (sub_nonneg.mpr (le_abs_self g))
  rw [inner_sub_right] at hh
  linarith

/-- Actual positivity of the weak zero-boundary inverse for `-Δ`. -/
theorem weakDirichletLaplaceSolution_nonneg {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    {f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))} (hf : 0 ≤ f) :
    0 ≤ dirichletValue Ω (weakDirichletLaplaceSolution i hR hΩ f) := by
  let u := weakDirichletLaplaceSolution i hR hΩ f
  obtain ⟨v, hv, hnorm, henergy⟩ := exists_abs_dirichletSobolev u
  have hpair := inner_L2_abs_ge_of_nonneg hf (dirichletValue Ω u)
  have hmin : dirichletEnergy Ω v v - 2 * inner ℝ f (dirichletValue Ω v) ≤
      dirichletEnergy Ω u u - 2 * inner ℝ f (dirichletValue Ω u) := by
    rw [hv]
    linarith
  have heq : v = u := weakDirichletLaplaceSolution_minimizer i hR hΩ f v hmin
  have habs : |dirichletValue Ω u| = dirichletValue Ω u := by
    rw [← hv, heq]
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [Lp.coeFn_abs (dirichletValue Ω u)] with x hx
  rw [habs] at hx
  rw [hx]
  exact abs_nonneg _

/-- Comparison of actual weak Dirichlet solutions, derived from positivity
and linearity of the constructed inverse. -/
theorem weakDirichletLaplaceSolution_mono {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    {f g : Lp ℝ 2 (volume : Measure (CoordinateSpace n))} (hfg : f ≤ g) :
    dirichletValue Ω (weakDirichletLaplaceSolution i hR hΩ f) ≤
      dirichletValue Ω (weakDirichletLaplaceSolution i hR hΩ g) := by
  have hh := weakDirichletLaplaceSolution_nonneg i hR hΩ (sub_nonneg.mpr hfg)
  have he : weakDirichletLaplaceSolution i hR hΩ (g - f) =
      weakDirichletLaplaceSolution i hR hΩ g - weakDirichletLaplaceSolution i hR hΩ f :=
    map_sub (weakDirichletLaplaceInverse i hR hΩ) g f
  rw [he, map_sub] at hh
  exact sub_nonneg.mp hh

end GaussianTilt.MomentMapLinearDirichlet
