import GaussianTilt.MomentMapLinearDirichletHarmonicLocal
import GaussianTilt.MomentMapLinearDirichletNewtonianPotential

/-!
# Weak-to-classical interior Poisson regularity

Subtracting the actual Newtonian particular solution leaves a genuinely
harmonic distribution. The proved Weyl construction then supplies local
regular representatives; canonical mollifier limits patch them. The
particular-solution helper is instantiated with the constructed Newtonian
potential, so the smooth-data endpoint assumes no regular solution.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma integrable_locally_mul_laplacian {u ψ : KernelSpace n → ℝ}
    (hu : LocallyIntegrable u volume) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun y => u y * kernelLaplacian ψ y) volume :=
  hu.integrable_smul_right_of_hasCompactSupport (continuous_kernelLaplacian hψ)
    (hasCompactSupport_kernelLaplacian hψc)

/-- Actual local representatives from a particular solution and the literal
weak equation. This is a subtraction lemma, not an assumed regularity theorem. -/
theorem exists_local_C2_rep_of_distribution_poisson_particular [NeZero n]
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {u f q : KernelSpace n → ℝ} (hu : LocallyIntegrable u volume)
    {B : ℝ} (huB : ∀ x ∈ Ω, |u x| ≤ B)
    (hq : ContDiff ℝ 2 q) (hqlap : ∀ x ∈ Ω, kernelLaplacian q x = f x)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y * kernelLaplacian ψ y) = ∫ y, f y * ψ y)
    {x₀ : KernelSpace n} (hx₀ : x₀ ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : KernelSpace n → ℝ, ContDiff ℝ 2 v ∧
      ∀ᵐ x ∂volume, x ∈ Metric.ball x₀ r → v x = u x := by
  let h := fun x => u x - q x
  have hhi : LocallyIntegrable h volume := hu.sub hq.continuous.locallyIntegrable
  obtain ⟨M, hM⟩ := hΩb.isCompact_closure.exists_bound_of_continuousOn hq.continuous.continuousOn
  have hhB : ∀ x ∈ Ω, |h x| ≤ B + M := by
    intro x hx
    exact (abs_sub _ _).trans (add_le_add (huB x hx) (by
      simpa only [Real.norm_eq_abs] using hM x (subset_closure hx)))
  have hhdist : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, h y * kernelLaplacian ψ y) = 0 := by
    intro ψ hψ hψc hψΩ
    have hψ2 := contDiff_infty.mp hψ 2
    have hp : (∫ y, q y * kernelLaplacian ψ y) = ∫ y, f y * ψ y := by
      have hs := integral_mul_kernelLaplacian_swap hψ2 hq hψc
      calc
        _ = ∫ y, kernelLaplacian ψ y * q y := by
          apply integral_congr_ae; exact ae_of_all _ (fun y => mul_comm _ _)
        _ = ∫ y, ψ y * kernelLaplacian q y := hs.symm
        _ = _ := by
          apply integral_congr_ae
          exact ae_of_all _ (fun y => by
            dsimp only
            by_cases hy : y ∈ tsupport ψ
            · rw [hqlap y (hψΩ hy), mul_comm]
            · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, mul_zero])
    change (∫ y, (u y - q y) * kernelLaplacian ψ y) = 0
    simp_rw [sub_mul]
    rw [integral_sub (integrable_locally_mul_laplacian hu hψ2 hψc)
      (integrable_locally_mul_laplacian hq.continuous.locallyIntegrable hψ2 hψc),
      heq ψ hψ hψc hψΩ, hp, sub_self]
  obtain ⟨r, hr, v, hv, hvh⟩ := exists_local_smooth_rep_of_bounded_distribution_harmonic
    hΩ hhi hhB hhdist hx₀
  refine ⟨r, hr, fun x => v x + q x, (contDiff_infty.mp hv 2).add hq, ?_⟩
  filter_upwards [hvh] with x hx hxr
  rw [hx hxr]
  dsimp [h]
  ring

lemma kernelLaplacian_const_mul_smooth (c : ℝ) {q : KernelSpace n → ℝ}
    (hq : ContDiff ℝ ∞ q) (x : KernelSpace n) :
    kernelLaplacian (fun y => c * q y) x = c * kernelLaplacian q x := by
  have hd {g : KernelSpace n → ℝ} (hg : Differentiable ℝ g) (v y : KernelSpace n) :
      kernelDirectionalDerivative v (fun z => c * g z) y = c * kernelDirectionalDerivative v g y := by
    unfold kernelDirectionalDerivative
    rw [((hg y).hasFDerivAt.const_mul c).fderiv]
    rfl
  have hD (v : KernelSpace n) : kernelDirectionalDerivative v (fun y => c * q y) =
      fun y => c * kernelDirectionalDerivative v q y := funext (hd (hq.differentiable (by simp)) v)
  unfold kernelLaplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change kernelDirectionalDerivative _ (kernelDirectionalDerivative _ (fun y => c * q y)) x = _
  rw [hD, hd ((smooth_kernelDirectionalDerivative hq _).differentiable (by simp))]
  rfl

/-- Actual C² interior regularity for bounded distributional Poisson
solutions with smooth compact data, with no regular-solution premise. -/
theorem harmonicRepresentative_C2_of_smooth_distribution_poisson [NeZero n]
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {u f : KernelSpace n → ℝ} (hu : LocallyIntegrable u volume)
    {B : ℝ} (huB : ∀ x ∈ Ω, |u x| ≤ B)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y * kernelLaplacian ψ y) = ∫ y, f y * ψ y) :
    ∀ x ∈ Ω, ContDiffAt ℝ 2 (harmonicRepresentative u) x := by
  let C := 2 * (n : ℝ) * fundamentalApproxMass n
  have hC : C ≠ 0 := by
    have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    exact (mul_pos (mul_pos (by norm_num) hn) (fundamentalApproxMass_pos n)).ne'
  let q := fun x => C⁻¹ * newtonianPotential f x
  have hq : ContDiff ℝ 2 q := contDiff_const.mul (contDiff_infty.mp (smooth_newtonianPotential hf hfc) 2)
  have hqlap (x : KernelSpace n) : kernelLaplacian q x = f x := by
    rw [kernelLaplacian_const_mul_smooth _ (smooth_newtonianPotential hf hfc), newtonianPotential_laplacian hf hfc]
    exact inv_mul_cancel_left₀ hC _
  apply contDiffAt_harmonicRepresentative_of_local_representatives
  intro x hx
  exact exists_local_C2_rep_of_distribution_poisson_particular hΩ hΩb hu huB hq (fun y _ => hqlap y) heq hx

/-- Actual local representatives from a particular solution and the literal
weak equation. This is a subtraction lemma, not an assumed regularity theorem. -/
theorem exists_local_smooth_remainder_of_distribution_poisson_particular [NeZero n]
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {u f q : KernelSpace n → ℝ} (hu : LocallyIntegrable u volume)
    {B : ℝ} (huB : ∀ x ∈ Ω, |u x| ≤ B)
    (hq : ContDiff ℝ 2 q) (hqlap : ∀ x ∈ Ω, kernelLaplacian q x = f x)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y * kernelLaplacian ψ y) = ∫ y, f y * ψ y)
    {x₀ : KernelSpace n} (hx₀ : x₀ ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : KernelSpace n → ℝ, ContDiff ℝ ∞ v ∧
      ∀ᵐ x ∂volume, x ∈ Metric.ball x₀ r → v x + q x = u x := by
  let h := fun x => u x - q x
  have hhi : LocallyIntegrable h volume := hu.sub hq.continuous.locallyIntegrable
  obtain ⟨M, hM⟩ := hΩb.isCompact_closure.exists_bound_of_continuousOn hq.continuous.continuousOn
  have hhB : ∀ x ∈ Ω, |h x| ≤ B + M := by
    intro x hx
    exact (abs_sub _ _).trans (add_le_add (huB x hx) (by
      simpa only [Real.norm_eq_abs] using hM x (subset_closure hx)))
  have hhdist : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, h y * kernelLaplacian ψ y) = 0 := by
    intro ψ hψ hψc hψΩ
    have hψ2 := contDiff_infty.mp hψ 2
    have hp : (∫ y, q y * kernelLaplacian ψ y) = ∫ y, f y * ψ y := by
      have hs := integral_mul_kernelLaplacian_swap hψ2 hq hψc
      calc
        _ = ∫ y, kernelLaplacian ψ y * q y := by
          apply integral_congr_ae; exact ae_of_all _ (fun y => mul_comm _ _)
        _ = ∫ y, ψ y * kernelLaplacian q y := hs.symm
        _ = _ := by
          apply integral_congr_ae
          exact ae_of_all _ (fun y => by
            dsimp only
            by_cases hy : y ∈ tsupport ψ
            · rw [hqlap y (hψΩ hy), mul_comm]
            · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, mul_zero])
    change (∫ y, (u y - q y) * kernelLaplacian ψ y) = 0
    simp_rw [sub_mul]
    rw [integral_sub (integrable_locally_mul_laplacian hu hψ2 hψc)
      (integrable_locally_mul_laplacian hq.continuous.locallyIntegrable hψ2 hψc),
      heq ψ hψ hψc hψΩ, hp, sub_self]
  obtain ⟨r, hr, v, hv, hvh⟩ := exists_local_smooth_rep_of_bounded_distribution_harmonic
    hΩ hhi hhB hhdist hx₀
  refine ⟨r, hr, v, hv, ?_⟩
  filter_upwards [hvh] with x hx hxr
  rw [hx hxr]
  dsimp [h]
  ring

end GaussianTilt.MomentMapLinearDirichlet
