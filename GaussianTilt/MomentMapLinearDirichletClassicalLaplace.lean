import GaussianTilt.MomentMapLinearDirichletBoundaryPatch

/-!
# Constructed classical zero-boundary Laplace solutions

The actual Hilbert-space solution, its distributional equation, the proved
barrier, exact Euclidean transfer, Newtonian particular solution, and Weyl
regularity are assembled. For smooth compact forcing this constructs a
continuous zero-boundary solution that is genuinely C² and solves the
pointwise equation in the interior. Boundary C²,α is a separate next step.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Exact coordinate transfer and genuine interior regularity for a bounded
weak Poisson solution with smooth compact data. -/
theorem exists_coordinate_classical_rep_of_distribution_poisson [NeZero n]
    {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {u f : CoordinateSpace n → ℝ} (hu : MemLp u 2 volume)
    {B : ℝ} (huB : ∀ x ∈ Ω, |u x| ≤ B)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (heq : ∀ ψ : CoordinateSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y * euclideanLaplacian ψ y) = ∫ y, f y * ψ y) :
    ∃ v : CoordinateSpace n → ℝ, v =ᵐ[volume] u ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 v x) ∧
      (∀ x ∈ Ω, euclideanLaplacian v x = f x) := by
  let L := dirichletCoordinateEquiv n
  let ΩE := L ⁻¹' Ω
  let uE := u ∘ L
  let fE := f ∘ L
  have hμ : MeasurePreserving L volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have hμi : MeasurePreserving L.symm volume volume := PiLp.volume_preserving_toLp (Fin n)
  have huE : LocallyIntegrable uE volume := (hu.comp_measurePreserving hμ).locallyIntegrable (by norm_num)
  have hΩE : IsOpen ΩE := hΩ.preimage L.continuous
  have hΩEb : Bornology.IsBounded ΩE := by
    have hc : IsCompact (L.symm '' closure Ω) := hΩb.isCompact_closure.image L.symm.continuous
    apply hc.isBounded.subset
    intro x hx
    exact ⟨L x, subset_closure hx, L.symm_apply_apply x⟩
  have hC := harmonicRepresentative_classical_of_smooth_distribution_poisson hΩE hΩEb huE
    (fun x hx => huB (L x) hx) (hf.comp L.contDiff) (hfc.comp_homeomorph L.toHomeomorph)
    (distribution_poisson_ofLp heq)
  let v := harmonicRepresentative uE ∘ L.symm
  have hAE : v =ᵐ[volume] u := by
    have hh := hμi.quasiMeasurePreserving.ae (harmonicRepresentative_ae_eq huE)
    simpa only [v, uE, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hh
  refine ⟨v, hAE, ?_, ?_⟩
  · intro x hx
    have hxe : L.symm x ∈ ΩE := by simpa only [ΩE, mem_preimage, L.apply_symm_apply] using hx
    exact (hC.1 _ hxe).comp x L.symm.contDiff.contDiffAt
  · intro x hx
    change euclideanLaplacian (harmonicRepresentative uE ∘ (dirichletCoordinateEquiv n).symm) x = _
    rw [euclideanLaplacian_toLp_any]
    have hxe : L.symm x ∈ ΩE := by simpa only [ΩE, mem_preimage, L.apply_symm_apply] using hx
    simpa only [fE, Function.comp_apply, L.apply_symm_apply] using hC.2 _ hxe

/-- Genuine classical zero-boundary existence for the Laplace starting
operator. The source is an actual smooth compact function; no classical
solution, trace theorem, or elliptic solvability statement is a premise. -/
theorem exists_classicalDirichletLaplaceSolution_smooth_data [NeZero n]
    {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R)
    (f : smoothCompactCore n)
    {w : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w) (hw0 : ∀ x ∈ Ω, w x ≤ 0)
    (hwb : ∀ x ∈ frontier Ω, w x = 0)
    {a F : ℝ} (ha : 0 < a) (hF : 0 ≤ F)
    (hwlap : ∀ x ∈ Ω, a ≤ euclideanLaplacian w x)
    (hf : ∀ x ∈ Ω, |f.1 x| ≤ F) :
    ∃ v : CoordinateSpace n → ℝ, Continuous v ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 v x) ∧
      (∀ x ∈ Ω, euclideanLaplacian v x = -f.1 x) ∧
      (∀ x ∉ Ω, v x = 0) ∧
      v =ᵐ[volume] dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip (smoothCompactToL2 volume f)) := by
  let fL := smoothCompactToL2 volume f
  let u := weakDirichletLaplaceSolution i hR hstrip fL
  have hforce : ∀ᵐ x ∂volume, x ∈ Ω → |fL x| ≤ F := by
    filter_upwards [smoothCompactToL2_ae volume f] with x hx hxΩ
    rw [show fL x = f.1 x from hx]
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
      (∫ y, u₀ y * euclideanLaplacian ψ y) = ∫ y, (-f.1 y) * ψ y := by
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
        filter_upwards [smoothCompactToL2_ae volume f] with y hy
        change -(fL y * ψ y) = -f.1 y * ψ y
        rw [show fL y = f.1 y from hy]
        ring
  obtain ⟨q, hqu, hq, hqeq⟩ := exists_coordinate_classical_rep_of_distribution_poisson
    hΩ hΩb hu₀Lp hu₀B f.2.1.neg f.2.2.neg hdist
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
