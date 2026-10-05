import GaussianTilt.MomentMapLinearDirichletVariableInteriorIteration
import GaussianTilt.MomentMapLinearDirichletExcessRadiusInterpolation

/-! # Uniform all-radius interior excess from a scale-correct starting error -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma ballGradientExcess_mono (u : VolumeJet n) (a : KernelSpace n) {r R : ℝ}
    (hrR : r ≤ R) : ballGradientExcess u a r ≤ ballGradientExcess u a R := by
  apply (ballGradientExcess_le_error u a r (ballMeanGradient u a R)).trans
  haveI : Fact (volume (Metric.ball a R) < ∞) := ⟨measure_ball_lt_top⟩
  have hI : IntegrableOn (fun x=>‖euclideanWeakGradient u x-ballMeanGradient u a R‖^2) (Metric.ball a R) :=
    (((euclideanWeakGradient_memLp u).restrict _).sub (memLp_const _)).integrable_norm_pow (p := 2) (by norm_num)
  apply setIntegral_mono_set hI (ae_of_all _ (fun x=>sq_nonneg _))
  exact ae_of_all _ (fun x hx=>Metric.ball_subset_ball hrR hx)

/-- An actual height-scale starting error cancels the initial-radius
factor in the proved interior PDE iteration. The resulting constant is
uniform even as the center approaches the boundary. -/
theorem ballGradientExcess_all_radii_of_scale_bound (u : VolumeJet n) (a : KernelSpace n)
    {R ρ θ C M P β : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hρ : 0 < ρ)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hC : 0 ≤ C) (hM : 0 ≤ M) (hP : 0 ≤ P) (hβ : 0 ≤ β)
    (hInitial : ballGradientEnergy u a R ≤ M*R^((n:ℝ)+β))
    (hGeometric : ∀ k : ℕ, ballGradientExcess u a ((R*ρ)*θ^k) ≤
      C*(ballGradientEnergy u a R+P*R^((n:ℝ)+2*β))*(ρ*θ^k)^((n:ℝ)+β)) :
    ∀ r : ℝ, 0 < r → r ≤ R*ρ → ballGradientExcess u a r ≤
      (C*θ^(-((n:ℝ)+β)))*(M+P)*r^((n:ℝ)+β) := by
  have hforce : P*R^((n:ℝ)+2*β) ≤ P*R^((n:ℝ)+β) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hR hR1 (by linarith)) hP
  have hGeometric' : ∀ k : ℕ, ballGradientExcess u a ((R*ρ)*θ^k) ≤
      (C*(M+P))*((R*ρ)*θ^k)^((n:ℝ)+β) := by
    intro k
    apply (hGeometric k).trans
    have ht : ballGradientEnergy u a R+P*R^((n:ℝ)+2*β) ≤ (M+P)*R^((n:ℝ)+β) := by
      linarith
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hC)
      (Real.rpow_nonneg (mul_pos hρ (pow_pos hθ k)).le ((n:ℝ)+β))
    convert hm using 1
    rw [mul_assoc R ρ (θ^k),Real.mul_rpow hR.le (mul_pos hρ (pow_pos hθ k)).le]
    ring
  have hh := geometric_power_bound_to_all_radii (ballGradientExcess u a) (mul_pos hR hρ) hθ hθ1
    (mul_nonneg hC (add_nonneg hM hP)) (by positivity : 0 ≤ (n:ℝ)+β)
    (fun r hr s hs hrs=>ballGradientExcess_mono u a hrs) hGeometric'
  intro r hr hrr
  convert hh r hr hrr using 1 <;> ring

end GaussianTilt.MomentMapLinearDirichlet
