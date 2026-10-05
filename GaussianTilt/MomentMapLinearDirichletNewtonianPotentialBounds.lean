import GaussianTilt.MomentMapLinearDirichletNewtonianPotential

/-! # Actual local size and dominated limits of Newtonian potentials -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Convolution
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

def newtonianLocalMass (n : ℕ) (r : ℝ) : ℝ :=
  ∫ y in Metric.closedBall (0 : KernelSpace n) r, |newtonianKernel n y|

lemma newtonianLocalMass_nonneg (n : ℕ) (r : ℝ) : 0 ≤ newtonianLocalMass n r :=
  integral_nonneg (fun _ => abs_nonneg _)

lemma norm_sub_exceeds_support {A R : ℝ} {x y : KernelSpace n}
    (hx : ‖x‖ ≤ R) (hy : R + A < ‖y‖) : A < ‖x - y‖ := by
  have ht : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    calc
      ‖y‖ = ‖x - (x - y)‖ := by congr 1; module
      _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le x (x - y)
  linarith

lemma potential_integrand_bound {f : KernelSpace n → ℝ} {A R F : ℝ}
    (hF : 0 ≤ F) (hfb : ∀ z, |f z| ≤ F)
    (hfs : Function.support f ⊆ Metric.closedBall 0 A)
    {x : KernelSpace n} (hx : ‖x‖ ≤ R) (y : KernelSpace n) :
    ‖newtonianKernel n y * f (x - y)‖ ≤
      (Metric.closedBall (0 : KernelSpace n) (R + A)).indicator
        (fun z => |newtonianKernel n z| * F) y := by
  by_cases hy : y ∈ Metric.closedBall (0 : KernelSpace n) (R + A)
  · rw [indicator_of_mem hy, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hfb _) (abs_nonneg _)
  · rw [indicator_of_notMem hy]
    have hfy : f (x - y) = 0 := by
      by_contra hz
      have hs := hfs hz
      have hn := norm_sub_exceeds_support hx (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy)
      have hn' : ‖x - y‖ ≤ A := by simpa only [Metric.mem_closedBall, dist_zero_right] using hs
      linarith
    simp only [hfy, mul_zero, norm_zero, le_refl]

lemma integrable_potential_dominator (n : ℕ) (r F : ℝ) :
    Integrable ((Metric.closedBall (0 : KernelSpace n) r).indicator
      (fun z => |newtonianKernel n z| * F)) volume := by
  rw [integrable_indicator_iff measurableSet_closedBall]
  exact (integrableOn_newtonianKernel_closedBall n r).norm.mul_const F

/-- The true locally integrable power/logarithmic kernel gives a common
local bound depending only on support radius and data supnorm. -/
theorem newtonianPotential_local_bound {f : KernelSpace n → ℝ} {A R F : ℝ}
    (hF : 0 ≤ F) (hfb : ∀ z, |f z| ≤ F)
    (hfs : Function.support f ⊆ Metric.closedBall 0 A)
    {x : KernelSpace n} (hx : ‖x‖ ≤ R) :
    |newtonianPotential f x| ≤ F * newtonianLocalMass n (R + A) := by
  have hb := norm_integral_le_of_norm_le (integrable_potential_dominator n (R + A) F)
    (ae_of_all volume (potential_integrand_bound hF hfb hfs hx))
  simpa only [newtonianPotential, convolution_def, ContinuousLinearMap.mul_apply',
    Real.norm_eq_abs, integral_indicator measurableSet_closedBall, integral_mul_const,
    integral_const_mul, newtonianLocalMass] using hb.trans_eq (by
      rw [integral_indicator measurableSet_closedBall, integral_mul_const]
      ring)

/-- The actual Newtonian convolutions converge pointwise under bounded,
common-compact-support approximation of the source. -/
theorem newtonianPotential_tendsto {f : ℕ → KernelSpace n → ℝ} {g : KernelSpace n → ℝ}
    {A F : ℝ} (hF : 0 ≤ F) (hfc : ∀ k, Continuous (f k))
    (hfb : ∀ k z, |f k z| ≤ F)
    (hfs : ∀ k, Function.support (f k) ⊆ Metric.closedBall 0 A)
    (hfg : ∀ z, Tendsto (fun k => f k z) atTop (𝓝 (g z))) (x : KernelSpace n) :
    Tendsto (fun k => newtonianPotential (f k) x) atTop (𝓝 (newtonianPotential g x)) := by
  apply tendsto_integral_of_dominated_convergence
    ((Metric.closedBall (0 : KernelSpace n) (‖x‖ + A)).indicator
      (fun z => |newtonianKernel n z| * F))
  · intro k
    exact (locallyIntegrable_newtonianKernel n).aestronglyMeasurable.mul
      ((hfc k).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact integrable_potential_dominator n (‖x‖ + A) F
  · intro k
    exact ae_of_all volume (potential_integrand_bound hF (hfb k) (hfs k) le_rfl)
  · exact ae_of_all volume (fun z => tendsto_const_nhds.mul (hfg (x - z)))

end GaussianTilt.MomentMapLinearDirichlet
