import GaussianTilt.MomentMapBoundaryRegularityBernsteinHarnack
import GaussianTilt.MomentMapRegularityReferenceExtension

/-! # The actual logarithmic equation and its forcing estimates -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateGradient_log_at {v : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hv : DifferentiableAt ℝ v x) (hv0 : v x ≠ 0) :
    coordinateGradient (fun y => Real.log (v y)) x = (v x)⁻¹ • coordinateGradient v x := by
  ext i
  exact coordinateDerivative_log_at hv hv0 i

lemma logarithmic_equation_of_linear_equation {v : CoordinateSpace n → ℝ}
    (hv : ContDiff ℝ ∞ v) (A : Matrix (Fin n) (Fin n) ℝ) {x : CoordinateSpace n}
    (hv0 : v x ≠ 0) :
    linearizedMA A (fun y => Real.log (v y)) x +
      coordinateGradient (fun y => Real.log (v y)) x ⬝ᵥ
        (A *ᵥ coordinateGradient (fun y => Real.log (v y)) x) = linearizedMA A v x / v x := by
  rw [linearizedMA_log_at _ (contDiff_infty.mp hv 2).contDiffAt hv0,
    coordinateGradient_log_at (hv.differentiable (by simp) x) hv0]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  field_simp
  ring

lemma coordinateDerivative_quotient_log {f v : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : DifferentiableAt ℝ f x) (hv : DifferentiableAt ℝ v x) (hv0 : v x ≠ 0) (k : Fin n) :
    coordinateDerivative k (fun y => f y / v y) x = coordinateDerivative k f x / v x -
      (f x / v x) * coordinateDerivative k (fun y => Real.log (v y)) x := by
  rw [coordinateDerivative_log_at hv hv0]
  simp only [div_eq_mul_inv]
  have hvi : DifferentiableAt ℝ (fun y => (v y)⁻¹) x := hv.inv hv0
  rw [coordinateDerivative_mul_at hf hvi, coordinateDerivative_inv_at hv hv0]
  ring

lemma logarithmic_forcing_bounds {f v : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : DifferentiableAt ℝ f x) (hv : DifferentiableAt ℝ v x) (hvpos : 0 < v x)
    {G : ℝ} (hG : 0 ≤ G) (hb : |f x| ≤ G * v x)
    (hDb : ∀ k, |coordinateDerivative k f x| ≤ G * v x) :
    |f x / v x| ≤ G ∧ ∀ k, |coordinateDerivative k (fun y => f y / v y) x| ≤
      G * (1 + |coordinateDerivative k (fun y => Real.log (v y)) x|) := by
  have hh : |f x / v x| ≤ G := by
    rw [abs_div, abs_of_pos hvpos]
    exact (div_le_iff₀ hvpos).mpr hb
  refine ⟨hh, ?_⟩
  intro k
  rw [coordinateDerivative_quotient_log hf hv hvpos.ne' k]
  have hD : |coordinateDerivative k f x / v x| ≤ G := by
    rw [abs_div, abs_of_pos hvpos]
    exact (div_le_iff₀ hvpos).mpr (hDb k)
  calc
    _ ≤ |coordinateDerivative k f x / v x| +
        |(f x / v x) * coordinateDerivative k (fun y => Real.log (v y)) x| := abs_sub _ _
    _ ≤ G + G * |coordinateDerivative k (fun y => Real.log (v y)) x| := by
      rw [abs_mul]
      exact add_le_add hD (mul_le_mul_of_nonneg_right hh (abs_nonneg _))
    _ = _ := by ring

/-- Local positivity is enough: a genuine cutoff constructs a globally
smooth logarithmic representative near the closed unit ball. -/
lemma exists_smooth_logarithm_near_unit_ball {v : CoordinateSpace n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hpos : ∀ y, ‖(coordinateEquiv n).symm y‖ < 2 → 0 < v y) :
    ∃ φ : CoordinateSpace n → ℝ, ContDiff ℝ ∞ φ ∧
      ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → φ =ᶠ[𝓝 y] (fun z => Real.log (v z)) := by
  let e := coordinateEquiv n
  have hlog : ContDiffOn ℝ ∞ (fun x : E n => Real.log (v (e x))) (Metric.ball 0 2) := by
    apply (hv.comp e.contDiff).contDiffOn.log
    intro x hx
    exact (hpos (e x) (by simpa only [e.symm_apply_apply, Metric.mem_ball, dist_zero_right] using hx)).ne'
  obtain ⟨ψ,hψ,heq⟩ := exists_global_smooth_eq_near_compact Metric.isOpen_ball hlog
    (isCompact_closedBall (0 : E n) 1)
    (show Metric.closedBall (0 : E n) 1 ⊆ Metric.ball 0 2 from fun x hx => by
      simp only [Metric.mem_closedBall, Metric.mem_ball, dist_zero_right] at hx ⊢
      linarith)
  refine ⟨ψ ∘ e.symm, hψ.comp e.symm.contDiff, ?_⟩
  intro y hy
  have hnear := e.symm.continuousAt.tendsto.eventually
    (heq (e.symm y) (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy))
  filter_upwards [hnear] with z hz
  simpa only [Function.comp_def, e.apply_symm_apply] using hz

end GaussianTilt.MomentMapRegularity
