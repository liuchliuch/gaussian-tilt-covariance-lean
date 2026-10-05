import GaussianTilt.MomentMapLinearDirichletHolderInterior

/-!
# Constructed classical zero-boundary solutions for Hölder Laplace data

The genuine weak inverse and boundary barriers are assembled with the
proved Hölder-data Newtonian potential and harmonic smoothing. This gives
continuous zero-boundary solutions with the actual classical interior PDE.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Genuine classical zero-boundary existence for the Laplace starting
operator. The source is an actual continuous compact Hölder function; no classical
solution, trace theorem, or elliptic solvability statement is a premise. -/
theorem exists_classicalDirichletLaplaceSolution_holder_data [NeZero n]
    {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R)
    (f : CoordinateSpace n → ℝ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    {α H : ℝ} (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x-y‖ ^ α)
    {w : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w) (hw0 : ∀ x ∈ Ω, w x ≤ 0)
    (hwb : ∀ x ∈ frontier Ω, w x = 0)
    {a F : ℝ} (ha : 0 < a) (hF : 0 ≤ F)
    (hwlap : ∀ x ∈ Ω, a ≤ euclideanLaplacian w x)
    (hf : ∀ x ∈ Ω, |f x| ≤ F) :
    ∃ v : CoordinateSpace n → ℝ, Continuous v ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 v x) ∧
      (∀ x ∈ Ω, euclideanLaplacian v x = -f x) ∧
      (∀ x ∉ Ω, v x = 0) ∧
      v =ᵐ[volume] dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip ((hfc.memLp_of_hasCompactSupport hfs (p := 2) (μ := (volume : Measure (CoordinateSpace n)))).toLp f)) := by
  let fL := (hfc.memLp_of_hasCompactSupport hfs (p := 2) (μ := (volume : Measure (CoordinateSpace n)))).toLp f
  let u := weakDirichletLaplaceSolution i hR hstrip fL
  have hforce : ∀ᵐ x ∂volume, x ∈ Ω → |fL x| ≤ F := by
    filter_upwards [(hfc.memLp_of_hasCompactSupport hfs (p := 2) (μ := volume)).coeFn_toLp] with x hx hxΩ
    rw [show fL x = f x from hx]
    exact hf x hxΩ
  obtain ⟨u₀, hu₀, hu₀out, hu₀bound, _⟩ := weakDirichletLaplaceSolution_boundary_continuous_representative
    hΩ hΩb i hR hstrip fL hw hw0 hwb ha hF hwlap hforce
  have hu₀Lp : MemLp u₀ 2 volume := (memLp_congr_ae hu₀).mpr (Lp.memLp (dirichletValue Ω u))
  obtain ⟨W, hW⟩ := hΩb.isCompact_closure.exists_bound_of_continuousOn hw.continuous.continuousOn
  have hu₀B : ∀ x ∈ Ω, |u₀ x| ≤ (F / a) * W := by
    intro x hx
    exact (hu₀bound x).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using hW x (subset_closure hx)) (div_nonneg hF ha.le))
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
  have hqbound : ∀ᵐ x ∂volume, x ∈ Ω → |q x| ≤ (F / a) * |w x| := by
    filter_upwards [hqu] with x hx _
    rw [hx]
    exact hu₀bound x
  have hvcont : Continuous v := continuous_zero_extension_of_boundary_barrier hΩ hqcont hw.continuous hwb
    (div_nonneg hF ha.le) hqbound
  have hveq (x : CoordinateSpace n) (hx : x ∈ Ω) : v =ᶠ[𝓝 x] q := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact indicator_of_mem hy q
  refine ⟨v, hvcont, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hq x hx).congr_of_eventuallyEq (hveq x hx)
  · intro x hx
    rw [euclideanLaplacian_congr_nhds (hveq x hx)]
    exact hqeq x hx
  · intro x hx
    exact indicator_of_notMem hx q
  · exact (zero_extension_ae_eq (hqu.mono (fun _ h _ => h))
      (ae_of_all _ (fun x hx => hu₀out x hx))).trans hu₀


end GaussianTilt.MomentMapLinearDirichlet
