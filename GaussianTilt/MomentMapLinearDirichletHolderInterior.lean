import GaussianTilt.MomentMapLinearDirichletClassicalLaplace
import GaussianTilt.MomentMapLinearDirichletNewtonianPotentialRegularity

/-!
# Genuine interior regularity for weak Poisson solutions with Hölder data

The constructed Hölder-data Newtonian potential is subtracted from the
literal weak solution. The actual harmonic smoothing and patching theorem
then gives the canonical C² representative and its pointwise equation.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma kernelLaplacian_const_mul_C2 (c : ℝ) {q : KernelSpace n → ℝ}
    (hq : ContDiff ℝ 2 q) (x : KernelSpace n) :
    kernelLaplacian (fun y => c * q y) x = c * kernelLaplacian q x := by
  have hd {g : KernelSpace n → ℝ} (hg : Differentiable ℝ g) (v y : KernelSpace n) :
      kernelDirectionalDerivative v (fun z => c * g z) y = c * kernelDirectionalDerivative v g y := by
    unfold kernelDirectionalDerivative
    rw [((hg y).hasFDerivAt.const_mul c).fderiv]
    rfl
  have hD (v : KernelSpace n) : kernelDirectionalDerivative v (fun y => c * q y) =
      fun y => c * kernelDirectionalDerivative v q y := funext (hd (hq.differentiable (by norm_num)) v)
  unfold kernelLaplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change kernelDirectionalDerivative _ (kernelDirectionalDerivative _ (fun y => c * q y)) x = _
  have hi : Differentiable ℝ (kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) q) :=
    (contDiff_directional_fderiv hq _).differentiable le_rfl
  rw [hD, hd hi]
  rfl

/-- Actual weak-to-classical interior Poisson regularity with compact
Hölder forcing. Neither the solution nor the potential is assumed C². -/
theorem harmonicRepresentative_classical_of_holder_distribution_poisson [NeZero n]
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {u f : KernelSpace n → ℝ} (hu : LocallyIntegrable u volume)
    {B : ℝ} (huB : ∀ x ∈ Ω, |u x| ≤ B)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    {α H : ℝ} (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x-y‖ ^ α)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y * kernelLaplacian ψ y) = ∫ y, f y * ψ y) :
    (∀ x ∈ Ω, ContDiffAt ℝ 2 (harmonicRepresentative u) x) ∧
      (∀ x ∈ Ω, kernelLaplacian (harmonicRepresentative u) x = f x) := by
  let C := 2 * (n : ℝ) * fundamentalApproxMass n
  have hC : C ≠ 0 := by
    have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    exact (mul_pos (mul_pos (by norm_num) hn) (fundamentalApproxMass_pos n)).ne'
  let q := fun x => C⁻¹ * newtonianPotential f x
  have hP := newtonianPotential_contDiff_two hf hfc hα hα1 hH hholder
  have hq : ContDiff ℝ 2 q := contDiff_const.mul hP
  have hqlap (x : KernelSpace n) : kernelLaplacian q x = f x := by
    rw [kernelLaplacian_const_mul_C2 _ hP, newtonianPotential_laplacian_holder hf hfc hα hα1 hH hholder]
    exact inv_mul_cancel_left₀ hC _
  have hlocal := fun x hx => exists_local_C2_rep_of_distribution_poisson_particular hΩ hΩb hu huB hq
    (fun y _ => hqlap y) heq (x₀ := x) hx
  exact ⟨contDiffAt_harmonicRepresentative_of_local_representatives hlocal,
    harmonicRepresentative_laplacian_of_local_representatives hΩ hf hlocal heq⟩

lemma norm_dirichletCoordinateEquiv_le (x : KernelSpace n) : ‖dirichletCoordinateEquiv n x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  exact PiLp.norm_apply_le x i

/-- Hölder forcing transfers to Euclidean coordinates with no loss in its
constant because the coordinate max norm is bounded by the Euclidean norm. -/
lemma holder_comp_dirichletCoordinateEquiv {f : CoordinateSpace n → ℝ} {H α : ℝ}
    (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hf : ∀ x y, |f x - f y| ≤ H * ‖x-y‖ ^ α) :
    ∀ x y : KernelSpace n, |f (dirichletCoordinateEquiv n x) - f (dirichletCoordinateEquiv n y)| ≤
      H * ‖x-y‖ ^ α := by
  intro x y
  apply (hf _ _).trans
  apply mul_le_mul_of_nonneg_left _ hH
  apply Real.rpow_le_rpow (norm_nonneg _) _ hα
  rw [← map_sub]
  exact norm_dirichletCoordinateEquiv_le _

/-- The actual C² representative and pointwise equation in the raw
coordinate space used by the classical Dirichlet operator. -/
theorem exists_coordinate_classical_rep_of_holder_distribution_poisson [NeZero n]
    {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {u f : CoordinateSpace n → ℝ} (hu : MemLp u 2 volume)
    {B : ℝ} (huB : ∀ x ∈ Ω, |u x| ≤ B)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    {α H : ℝ} (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x-y‖ ^ α)
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
  have hC := harmonicRepresentative_classical_of_holder_distribution_poisson hΩE hΩEb huE
    (fun x hx => huB (L x) hx) (hf.comp L.continuous) (hfc.comp_homeomorph L.toHomeomorph)
    hα hα1 hH (holder_comp_dirichletCoordinateEquiv hH hα.le hholder) (distribution_poisson_ofLp heq)
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

end GaussianTilt.MomentMapLinearDirichlet
