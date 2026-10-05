import GaussianTilt.MomentMapLinearDirichletHolderLaplace

/-! # Classical zero-boundary existence from an actual continuous weak barrier

The barrier need not be a smooth defining function. This permits corners,
using the minimum of independently proved smooth barriers.
-/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- The actual weak inverse, its distributional equation and the proved
interior Hölder theory construct the classical representative. Only the
explicit AE barrier bound is passed, for subsequent discharge by concrete barriers. -/
theorem exists_classicalDirichletLaplaceSolution_of_weak_barrier [NeZero n]
    {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R)
    (f : CoordinateSpace n → ℝ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    {α H : ℝ} (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x-y‖ ^ α)
    {w : CoordinateSpace n → ℝ} (hw : Continuous w) (hwb : ∀ x ∈ frontier Ω, w x = 0)
    (hweak : ∀ᵐ x ∂volume, x ∈ Ω →
      |dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip
        ((hfc.memLp_of_hasCompactSupport hfs (p := 2) (μ := (volume : Measure (CoordinateSpace n)))).toLp f)) x| ≤ |w x|) :
    ∃ v : CoordinateSpace n → ℝ, Continuous v ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 v x) ∧
      (∀ x ∈ Ω, euclideanLaplacian v x = -f x) ∧
      (∀ x ∉ Ω, v x = 0) ∧
      (∀ x, |v x| ≤ |w x|) ∧
      v =ᵐ[volume] dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip
        ((hfc.memLp_of_hasCompactSupport hfs (p := 2) (μ := (volume : Measure (CoordinateSpace n)))).toLp f)) := by
  let fL := (hfc.memLp_of_hasCompactSupport hfs (p := 2) (μ := (volume : Measure (CoordinateSpace n)))).toLp f
  let u := weakDirichletLaplaceSolution i hR hstrip fL
  obtain ⟨u₀, hu₀, hu₀out, hu₀bound, _⟩ := exists_boundary_continuous_representative hΩ.measurableSet
    u hw (by norm_num : (0 : ℝ) ≤ 1) (by simpa only [one_mul] using hweak)
  have hu₀Lp : MemLp u₀ 2 volume := (memLp_congr_ae hu₀).mpr (Lp.memLp (dirichletValue Ω u))
  obtain ⟨W, hW⟩ := hΩb.isCompact_closure.exists_bound_of_continuousOn hw.continuousOn
  have hu₀B : ∀ x ∈ Ω, |u₀ x| ≤ W := by
    intro x hx
    have hb := hu₀bound x
    rw [one_mul] at hb
    exact hb.trans (by simpa only [Real.norm_eq_abs] using hW x (subset_closure hx))
  have hdist : ∀ ψ : CoordinateSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u₀ y * euclideanLaplacian ψ y) = ∫ y, (-f y) * ψ y := by
    intro ψ hψ hψc hψΩ
    calc
      _ = ∫ y, dirichletValue Ω u y * euclideanLaplacian ψ y := by
        apply integral_congr_ae
        filter_upwards [hu₀] with y hy
        rw [hy]
      _ = -(∫ y, fL y * ψ y) := weakDirichletLaplaceSolution_distribution i hR hstrip fL hψ hψc hψΩ
      _ = _ := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [(hfc.memLp_of_hasCompactSupport hfs (p := 2) (μ := volume)).coeFn_toLp] with y hy
        change -(fL y * ψ y) = -f y * ψ y
        rw [show fL y = f y from hy]
        ring
  obtain ⟨q, hqu, hq, hqeq⟩ := exists_coordinate_classical_rep_of_holder_distribution_poisson
    hΩ hΩb hu₀Lp hu₀B hfc.neg hfs.neg hα hα1 hH
    (fun x y => by simpa only [neg_sub_neg, abs_sub_comm] using hholder x y) hdist
  let v := Ω.indicator q
  have hqcont : ContinuousOn q Ω := hΩ.continuousOn_iff.mpr (fun _ hx => (hq _ hx).continuousAt)
  have hqbound : ∀ᵐ x ∂volume, x ∈ Ω → |q x| ≤ (1 : ℝ) * |w x| := by
    filter_upwards [hqu] with x hx _
    rw [hx]
    exact hu₀bound x
  have hvcont : Continuous v := continuous_zero_extension_of_boundary_barrier hΩ hqcont hw hwb
    (by norm_num : (0 : ℝ) ≤ 1) hqbound
  have hveq (x : CoordinateSpace n) (hx : x ∈ Ω) : v =ᶠ[𝓝 x] q := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact indicator_of_mem hy q
  refine ⟨v, hvcont, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hq x hx).congr_of_eventuallyEq (hveq x hx)
  · intro x hx
    rw [euclideanLaplacian_congr_nhds (hveq x hx)]
    exact hqeq x hx
  · intro x hx
    exact indicator_of_notMem hx q
  · intro x
    by_cases hx : x ∈ Ω
    · rw [show v x = q x from indicator_of_mem hx q]
      simpa only [one_mul] using continuousOn_bound_of_ae hΩ hqcont hw hqbound x hx
    · rw [show v x = 0 from indicator_of_notMem hx q, abs_zero]
      exact abs_nonneg _
  · exact (zero_extension_ae_eq (hqu.mono (fun _ h _ => h))
      (hu₀out |> fun h => ae_of_all _ h)).trans hu₀

end GaussianTilt.MomentMapLinearDirichlet
