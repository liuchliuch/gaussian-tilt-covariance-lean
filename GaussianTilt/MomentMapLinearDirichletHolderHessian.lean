import GaussianTilt.MomentMapLinearDirichletHolderInterior
import GaussianTilt.MomentMapHolderSmoothEmbedding

/-!
# Actual local Hessian Hölder regularity of the weak Poisson solution

The canonical representative is locally the sum of the constructed
Newtonian potential and the proved smooth harmonic remainder. The true
second Fréchet derivatives are therefore Hölder with the forcing exponent.
No initial Hessian Hölder condition is used.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma secondFrechet_const_mul_C2 (c : ℝ) {q : KernelSpace n → ℝ}
    (hq : ContDiff ℝ 2 q) (x : KernelSpace n) :
    fderiv ℝ (fderiv ℝ (fun y => c * q y)) x = c • fderiv ℝ (fderiv ℝ q) x := by
  have he : fderiv ℝ (fun y => c * q y) = fun y => c • fderiv ℝ q y := by
    funext y
    change fderiv ℝ (c • q) y = _
    exact fderiv_const_smul (hq.differentiable (by norm_num) y) c
  rw [he]
  change fderiv ℝ (c • fderiv ℝ q) x = _
  exact fderiv_const_smul ((hq.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl x) c

lemma secondFrechet_add_C2 {g q : KernelSpace n → ℝ}
    (hg : ContDiff ℝ 2 g) (hq : ContDiff ℝ 2 q) (x : KernelSpace n) :
    fderiv ℝ (fderiv ℝ (fun y => g y + q y)) x =
      fderiv ℝ (fderiv ℝ g) x + fderiv ℝ (fderiv ℝ q) x := by
  have he : fderiv ℝ (fun y => g y + q y) = fun y => fderiv ℝ g y + fderiv ℝ q y := by
    funext y
    exact fderiv_fun_add (hg.differentiable (by norm_num) y) (hq.differentiable (by norm_num) y)
  rw [he]
  exact fderiv_fun_add ((hg.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl x)
    ((hq.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl x)

/-- The literal second derivative of a globally smooth function has a
finite Hölder modulus on each actual compact Euclidean ball. -/
lemma exists_secondFrechet_holder_of_smooth {g : KernelSpace n → ℝ}
    (hg : ContDiff ℝ ∞ g) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.closedBall (0 : KernelSpace n) R,
      ∀ y ∈ Metric.closedBall (0 : KernelSpace n) R,
        ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) y‖ ≤ C * ‖x-y‖ ^ α := by
  let S := Metric.closedBall (0 : KernelSpace n) R
  let F := KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  obtain ⟨G, hG⟩ := GaussianTilt.HolderSpace.exists_holder_restriction_of_smooth
    (convex_closedBall (0 : KernelSpace n) R) (isCompact_closedBall _ _) hα hα1 _ hd
  refine ⟨‖G‖, norm_nonneg _, ?_⟩
  intro x hx y hy
  have hb := GaussianTilt.HolderSpace.norm_value_sub_le S F α G ⟨x, hx⟩ ⟨y, hy⟩
  have hxG := hG ⟨x, hx⟩
  have hyG := hG ⟨y, hy⟩
  change GaussianTilt.HolderSpace.value S F α G ⟨x, hx⟩ = _ at hxG
  change GaussianTilt.HolderSpace.value S F α G ⟨y, hy⟩ = _ at hyG
  rw [hxG, hyG] at hb
  simpa only [Subtype.dist_eq, dist_eq_norm] using hb

/-- Genuine local C²,α regularity of a bounded distributional Poisson
solution with compact Hölder forcing, with the same positive exponent. -/
theorem harmonicRepresentative_hessian_locally_holder [NeZero n]
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {u f : KernelSpace n → ℝ} (hu : LocallyIntegrable u volume)
    {B : ℝ} (huB : ∀ x ∈ Ω, |u x| ≤ B)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    {α H : ℝ} (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x-y‖ ^ α)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y * kernelLaplacian ψ y) = ∫ y, f y * ψ y) :
    ∀ x ∈ Ω, ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball x r,
        ‖fderiv ℝ (fderiv ℝ (harmonicRepresentative u)) y -
          fderiv ℝ (fderiv ℝ (harmonicRepresentative u)) z‖ ≤ C * ‖y-z‖ ^ α := by
  intro x hx
  let N := 2 * (n : ℝ) * fundamentalApproxMass n
  have hN : N ≠ 0 := by
    have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    exact (mul_pos (mul_pos (by norm_num) hn) (fundamentalApproxMass_pos n)).ne'
  let q := fun y => N⁻¹ * newtonianPotential f y
  have hP := newtonianPotential_contDiff_two hf hfc hα hα1 hH hholder
  have hq : ContDiff ℝ 2 q := contDiff_const.mul hP
  have hqlap (y : KernelSpace n) : kernelLaplacian q y = f y := by
    rw [kernelLaplacian_const_mul_C2 _ hP, newtonianPotential_laplacian_holder hf hfc hα hα1 hH hholder]
    exact inv_mul_cancel_left₀ hN _
  obtain ⟨r, hr, g, hg, hgu⟩ := exists_local_smooth_remainder_of_distribution_poisson_particular
    hΩ hΩb hu huB hq (fun y _ => hqlap y) heq hx
  have hlocal := harmonicRepresentative_eqOn_of_local_ae_eq Metric.isOpen_ball
    (hg.continuous.add hq.continuous) (by
      filter_upwards [hgu] with y hy hyr
      exact (hy hyr).symm)
  let R := ‖x‖ + 1
  obtain ⟨Cg, hCg, hgH⟩ := exists_secondFrechet_holder_of_smooth hg hα.le hα1.le R
  obtain ⟨Cp, hCp, hpH⟩ := newtonianPotential_hessian_locally_holder hf hfc hα hα1 hH hholder R
    (by dsimp [R]; positivity)
  let δ := min r 1
  have hδ : 0 < δ := lt_min hr zero_lt_one
  have hin {y : KernelSpace n} (hy : y ∈ Metric.ball x δ) : y ∈ Metric.closedBall 0 R := by
    have hd : ‖y-x‖ < δ := hy
    have hn := norm_sub_le_norm_sub_add_norm_sub y x (0 : KernelSpace n)
    simp only [sub_zero] at hn
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp [δ, R] at *
    linarith [min_le_right r (1 : ℝ)]
  have hsecond {y : KernelSpace n} (hy : y ∈ Metric.ball x δ) :
      fderiv ℝ (fderiv ℝ (harmonicRepresentative u)) y =
        fderiv ℝ (fderiv ℝ g) y + N⁻¹ • fderiv ℝ (fderiv ℝ (newtonianPotential f)) y := by
    have hyr : y ∈ Metric.ball x r := Metric.ball_subset_ball (min_le_left r 1) hy
    have he : harmonicRepresentative u =ᶠ[𝓝 y] (fun z => g z + q z) :=
      eventually_of_mem (Metric.isOpen_ball.mem_nhds hyr) hlocal
    rw [he.fderiv.fderiv_eq, secondFrechet_add_C2 (contDiff_infty.mp hg 2) hq,
      secondFrechet_const_mul_C2 _ hP]
  refine ⟨δ, Cg + |N⁻¹| * Cp + 1, hδ, by positivity, ?_⟩
  intro y hy z hz
  rw [hsecond hy, hsecond hz]
  have hid : (fderiv ℝ (fderiv ℝ g) y + N⁻¹ • fderiv ℝ (fderiv ℝ (newtonianPotential f)) y) -
      (fderiv ℝ (fderiv ℝ g) z + N⁻¹ • fderiv ℝ (fderiv ℝ (newtonianPotential f)) z) =
      (fderiv ℝ (fderiv ℝ g) y - fderiv ℝ (fderiv ℝ g) z) +
        N⁻¹ • (fderiv ℝ (fderiv ℝ (newtonianPotential f)) y - fderiv ℝ (fderiv ℝ (newtonianPotential f)) z) := by module
  rw [hid]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ g) y - fderiv ℝ (fderiv ℝ g) z‖ +
        ‖N⁻¹ • (fderiv ℝ (fderiv ℝ (newtonianPotential f)) y - fderiv ℝ (fderiv ℝ (newtonianPotential f)) z)‖ := norm_add_le _ _
    _ ≤ Cg * ‖y-z‖ ^ α + |N⁻¹| * (Cp * ‖y-z‖ ^ α) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add (hgH y (hin hy) z (hin hz))
        (mul_le_mul_of_nonneg_left (hpH y (hin hy) z (hin hz)) (abs_nonneg _))
    _ ≤ _ := by nlinarith [Real.rpow_nonneg (norm_nonneg (y-z)) α]

end GaussianTilt.MomentMapLinearDirichlet
