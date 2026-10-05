import GaussianTilt.MomentMapSchauderLocalEquation

/-! # Local source equations with genuinely variable smooth spatial forcing -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 1800000
open Matrix Set Filter
open scoped ContDiff BigOperators Topology
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Jacobi differentiates the actual local equation logdet Hφ=g(x).
Neither positivity nor the equation is required outside the open set. -/
theorem local_spatial_directional_equation {φ g : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) {U : Set (KernelSpace n)} (hU : IsOpen U)
    (hpos : ∀ x ∈ U, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x ∈ U, Real.log (euclideanHessianMatrix φ x).det=g x)
    (v : KernelSpace n) {x : KernelSpace n} (hx : x ∈ U) :
    euclideanEllipticOperator (euclideanHessianMatrix φ x)⁻¹ (kernelDirectionalDerivative v φ) x=
      kernelDirectionalDerivative v g x := by
  have hH : ∀ i j, ContDiff ℝ 1 (fun y => euclideanHessianMatrix φ y i j) :=
    contDiff_euclideanHessianMatrix_entry hφ
  have he : (fun y => Real.log (euclideanHessianMatrix φ y).det) =ᶠ[𝓝 x] g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hMA y hy
  have hj := fderiv_matrix_logdet_field_apply_at hH v x (hpos x hx).det_pos.ne'
  rw [he.fderiv_eq, matrixDirectionalDerivative_euclideanHessian hφ] at hj
  have hD : ContDiff ℝ 2 (kernelDirectionalDerivative v φ) := contDiff_kernelDirectionalDerivative hφ v
  have hsym := euclideanHessianMatrix_isSymm hD x
  change euclideanEllipticOperator _ _ x=fderiv ℝ g x v
  rw [hj]
  simp only [euclideanEllipticOperator, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hsym.apply i j]
  rfl

theorem local_spatial_iterated_equation (k : ℕ) {φ g : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ (↑(k+3) : WithTop ℕ∞) φ)
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    {U : Set (KernelSpace n)} (hU : IsOpen U)
    (hpos : ∀ x ∈ U, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x ∈ U, Real.log (euclideanHessianMatrix φ x).det=g x)
    (hAe : ∀ x ∈ U, A x=(euclideanHessianMatrix φ x)⁻¹)
    (d : Fin k → KernelSpace n) (v : KernelSpace n) {x : KernelSpace n} (hx : x ∈ U) :
    euclideanEllipticOperator (A x) (scalarDerivativeJet (k+1) φ (Fin.snoc d v)) x=
      iteratedEllipticForcing A (kernelDirectionalDerivative v φ) (kernelDirectionalDerivative v g) k d x := by
  have hφ3 : ContDiff ℝ 3 φ := hφ.of_le (by exact_mod_cast (show 3 ≤ k+3 by omega))
  have hD : ContDiff ℝ (↑(k+2) : WithTop ℕ∞) (kernelDirectionalDerivative v φ) :=
    contDiff_kernelDirectionalDerivative (by simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc] using hφ) v
  have hbase : ∀ y ∈ U, euclideanEllipticOperator (A y) (kernelDirectionalDerivative v φ) y=
      kernelDirectionalDerivative v g y := by
    intro y hy
    rw [hAe y hy]
    exact local_spatial_directional_equation hφ3 hU hpos hMA v hy
  have hh := iterated_differentiated_elliptic_equation_on k hD hA hU hbase d hx
  rw [scalarDerivativeJet_directional (hφ.of_le (by exact_mod_cast (show k+1 ≤ k+3 by omega)))] at hh
  exact hh

/-- First local C³,α gain with smooth spatial forcing, derived from the
actual nonlinear quotient equation and the proved interior estimate. -/
theorem exists_local_spatial_third_order [NeZero n]
    {φ g : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 2 g) (a : KernelSpace n)
    {R H α : ℝ} (hR : 0 < R) (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ Metric.closedBall a (2*R), (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x ∈ Metric.closedBall a (2*R), Real.log (euclideanHessianMatrix φ x).det=g x)
    (hφH : ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
      ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ ≤ H*‖x-y‖^α) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ R ∧ 0 < C ∧ ContDiffOn ℝ 3 φ (Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x‖ ≤ C) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y‖ ≤ C*‖x-y‖^α) := by
  obtain ⟨Hg, hHg, _, hgH⟩ := exists_contDiff_holder_bound_on_compact_convex
    (hg.fderiv_right (m := 1) (by norm_num)) (isCompact_closedBall a (2*R))
    (convex_closedBall a (2*R)) hα.le hα1.le
  obtain ⟨r, C, hr, hrR, hC, hq⟩ := exists_uniform_source_difference_schauder_local
    hφ (hg.of_le (by norm_num)) a hR hpos hMA hH hHg.le hα hα1 hφH hgH
  obtain ⟨hc, hb, hh⟩ := contDiffOn_three_of_uniform_second_difference_bounds hφ a hr hR hC.le hα hq
  exact ⟨r/2, C, by linarith, by linarith, hC, hc, hb, hh⟩

end GaussianTilt.MomentMapSchauder
