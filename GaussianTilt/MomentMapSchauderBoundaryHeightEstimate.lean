import GaussianTilt.MomentMapSchauderBoundaryScaledPoisson

/-! # Interior jets of a remainder at the boundary-height scale -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2000000
open Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- If an actual Poisson remainder is of size `d² d^α` on a ball at
height scale `d`, its gradient and Hessian have the correct vanishing
orders, and its interior Hessian has a scale-independent Hölder bound. -/
theorem exists_height_scale_poisson_jet_bound [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w g : KernelSpace n → ℝ) (x : KernelSpace n) (d M H : ℝ),
      0 < d → 0 ≤ M → 0 ≤ H → ContDiffOn ℝ 2 w (Metric.ball x (d/4)) → Continuous g →
      (∀ y ∈ Metric.ball x (d/4), kernelLaplacian w y=g y) →
      (∀ y ∈ Metric.ball x (d/4), |w y| ≤ M*d^2*d^α) →
      (∀ y ∈ Metric.ball x (d/2), |g y| ≤ H*d^α) →
      (∀ y ∈ Metric.ball x (d/2), ∀ z ∈ Metric.ball x (d/2), |g y-g z| ≤ H*‖y-z‖^α) →
      ‖fderiv ℝ w x‖ ≤ K*(M+H)*d*d^α ∧
      ‖fderiv ℝ (fderiv ℝ w) x‖ ≤ K*(M+H)*d^α ∧
      (∀ y ∈ Metric.ball x (d/64), ∀ z ∈ Metric.ball x (d/64),
        ‖fderiv ℝ (fderiv ℝ w) y-fderiv ℝ (fderiv ℝ w) z‖ ≤ K*(M+H)*‖y-z‖^α) := by
  obtain ⟨C,hC,hscaled⟩ := exists_scaled_poisson_jet_bound (n := n) hα hα1
  let K := 128*C*(1+8^α)
  have hK : 0 < K := by dsimp [K]; positivity
  have hCK : 128*C ≤ K := by dsimp [K]; nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ)≤8) α]
  have hCKα : 128*C*8^α ≤ K := by dsimp [K]; nlinarith
  refine ⟨K,hK,?_⟩
  intro w g x d M H hd hM hH hw hg heq hwB hgB hgH
  let r := d/8
  have hr : 0 < r := by dsimp [r]; positivity
  have hr2 : r*2=d/4 := by dsimp [r]; ring
  have hr4 : r*4=d/2 := by dsimp [r]; ring
  have hr8 : r/8=d/64 := by dsimp [r]; ring
  have hrle : r ≤ d := by dsimp [r]; linarith
  have hrpow : r^α ≤ d^α := Real.rpow_le_rpow hr.le hrle hα.le
  have hdα : 0 ≤ d^α := Real.rpow_nonneg hd.le α
  have hrpow2 : r^2 ≤ d^2 := sq_le_sq₀ hr.le hd.le |>.mpr hrle
  have hh := hscaled w g x r hr (by rwa [hr2]) hg (by rwa [hr2])
    (M*d^2*d^α) (H*d^α) H (by positivity) (by positivity) hH
    (by rwa [hr2]) (by rwa [hr4]) (by rwa [hr4])
  have hdata : M*d^2*d^α+r^2*(H*d^α)+r^2*H*r^α ≤ 2*(M+H)*d^2*d^α := by
    have h1 := mul_le_mul_of_nonneg_right hrpow2 (mul_nonneg hH hdα)
    have h2 := mul_le_mul (mul_le_mul_of_nonneg_right hrpow2 hH) hrpow (by positivity) (by positivity)
    nlinarith [mul_nonneg (mul_nonneg hM (sq_nonneg d)) hdα]
  have hdataC := mul_le_mul_of_nonneg_left hdata hC.le
  have hDb := hh.1.trans hdataC
  have hQb := hh.2.1.trans hdataC
  have hD : ‖fderiv ℝ w x‖ ≤ 16*C*(M+H)*d*d^α := by
    dsimp [r] at hDb
    nlinarith
  have hQ : ‖fderiv ℝ (fderiv ℝ w) x‖ ≤ 128*C*(M+H)*d^α := by
    dsimp [r] at hQb
    nlinarith [sq_pos_of_pos hd]
  refine ⟨hD.trans ?_,hQ.trans ?_,?_⟩
  · have hh : 16*C ≤ K := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (by positivity)) hd.le) hdα
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK (by positivity)) hdα
  · intro y hy z hz
    have hb := hh.2.2 y (by rwa [hr8]) z (by rwa [hr8])
    have hp : 0 ≤ (r⁻¹*‖y-z‖)^α := by positivity
    have hb' := hb.trans (mul_le_mul_of_nonneg_right hdataC hp)
    have hcancel : d^α*(r⁻¹*‖y-z‖)^α=8^α*‖y-z‖^α := by
      rw [← Real.mul_rpow hd.le (by positivity)]
      have he : d*(r⁻¹*‖y-z‖)=8*‖y-z‖ := by dsimp [r]; field_simp
      rw [he,Real.mul_rpow (by norm_num : (0:ℝ)≤8) (norm_nonneg _)]
    have hrhs : C*(2*(M+H)*d^2*d^α)*(r⁻¹*‖y-z‖)^α=
        (2*C*(M+H)*d^2)*(8^α*‖y-z‖^α) := by
      calc
        _ = (2*C*(M+H)*d^2)*(d^α*(r⁻¹*‖y-z‖)^α) := by ring
        _ = _ := by rw [hcancel]
    rw [hrhs] at hb'
    have hsmall : ‖fderiv ℝ (fderiv ℝ w) y-fderiv ℝ (fderiv ℝ w) z‖ ≤
        128*C*8^α*(M+H)*‖y-z‖^α := by
      dsimp [r] at hb'
      nlinarith [sq_pos_of_pos hd]
    exact hsmall.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCKα (by positivity)) (Real.rpow_nonneg (norm_nonneg _) α))

end GaussianTilt.MomentMapSchauder
