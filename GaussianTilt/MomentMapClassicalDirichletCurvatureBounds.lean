import GaussianTilt.MomentMapClassicalDirichletIntrinsicChartForcing
import GaussianTilt.MomentMapClassicalDirichletIntrinsicTangentDerivatives

/-! # Actual bounded and scale-weighted curvature drift before flattening -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

lemma exists_coordinate_hessian_third_bound_on_compact
    {S : Set (CoordinateSpace n)} (hS : IsCompact S) {w : CoordinateSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S,
      (∀ i l, |coordinateHessian w x i l| ≤ C) ∧
      (∀ i l k, |coordinateThirdDerivative w x i l k| ≤ C) := by
  have h2 : Continuous (fun x => fun i l => coordinateHessian w x i l) :=
    continuous_pi (fun i => continuous_pi (fun l => (smooth_coordinateHessian hw i l).continuous))
  have h3 : Continuous (fun x => fun i l k => coordinateThirdDerivative w x i l k) :=
    continuous_pi (fun i => continuous_pi (fun l => continuous_pi (fun k =>
      (smooth_coordinateDerivative (smooth_coordinateHessian hw i l) k).continuous)))
  obtain ⟨C₂,hC₂⟩ := hS.exists_bound_of_continuousOn h2.continuousOn
  obtain ⟨C₃,hC₃⟩ := hS.exists_bound_of_continuousOn h3.continuousOn
  refine ⟨max (max C₂ C₃) 0,le_max_right _ _,?_⟩
  intro x hx
  constructor
  · intro i l
    exact ((norm_le_pi_norm (fun l => coordinateHessian w x i l) l).trans
      ((norm_le_pi_norm (fun i l => coordinateHessian w x i l) i).trans (hC₂ x hx))).trans
      ((le_max_left C₂ C₃).trans (le_max_left _ _))
  · intro i l k
    exact ((norm_le_pi_norm (fun k => coordinateThirdDerivative w x i l k) k).trans
      ((norm_le_pi_norm (fun l k => coordinateThirdDerivative w x i l k) l).trans
        ((norm_le_pi_norm (fun i l k => coordinateThirdDerivative w x i l k) i).trans (hC₃ x hx)))).trans
      ((le_max_right C₂ C₃).trans (le_max_left _ _))

lemma scaled_variable_linearizedMA_derivative_bound
    {w : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i l, Differentiable ℝ (fun x => A x i l))
    (x : CoordinateSpace n) (k : Fin n) {r I D B₂ B₃ : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hI : 0 ≤ I) (hD : 0 ≤ D)
    (hA0 : ∀ i l, |A x i l| ≤ I)
    (hA1 : ∀ i l, r*|matrixCoordinateDerivative A k x i l| ≤ D)
    (h2 : ∀ i l, |coordinateHessian w x i l| ≤ B₂)
    (h3 : ∀ i l, |coordinateThirdDerivative w x i l k| ≤ B₃) :
    r*|coordinateDerivative k (fun y => linearizedMA (A y) w y) x| ≤ (n:ℝ)^2*(D*B₂+I*B₃) := by
  rw [coordinateDerivative_variable_linearizedMA hw hA]
  have hfirst : r*|(matrixCoordinateDerivative A k x*coordinateHessian w x).trace| ≤ (n:ℝ)^2*D*B₂ := by
    have hscaled : ∀ i l, |(r • matrixCoordinateDerivative A k x) i l| ≤ D := by
      intro i l
      simpa only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg hr] using hA1 i l
    have hh := abs_trace_product_le_entry_bounds hD hscaled h2
    simpa only [Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,abs_mul,abs_of_nonneg hr] using hh
  have hsecond : r*|(A x*matrixCoordinateDerivative (coordinateHessian w) k x).trace| ≤ (n:ℝ)^2*I*B₃ :=
    scaled_abs_le_of_abs_le hr1 (abs_trace_product_le_entry_bounds hI hA0 h3)
  have hh := mul_le_mul_of_nonneg_left (abs_add_le
    (matrixCoordinateDerivative A k x*coordinateHessian w x).trace
    (A x*matrixCoordinateDerivative (coordinateHessian w) k x).trace) hr
  nlinarith

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- The original curvature coefficient `L_(H⁻¹) w` is actually bounded,
and its first derivatives satisfy the scale bound needed after flattening. -/
theorem intrinsic_dirichletContinuation_curvature_bounds [NeZero n] {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      let b := fun x => linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ d.coordinateDefining x
      (∀ x ∈ {y | d.coordinateDefining y ≤ 0}, |b x| ≤ C) ∧
      (∀ x : CoordinateSpace n, ∀ r : ℝ, 0 < r → r ≤ 1 →
        (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r →
          y ∈ interior {z | d.coordinateDefining z ≤ 0}) → ∀ k, r*|coordinateDerivative k b x| ≤ C) := by
  obtain ⟨K,hK,hHess⟩ := d.intrinsic_dirichletContinuation_uniform_hessian hα
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨Ca,hCa,hDA⟩ := d.intrinsic_dirichletContinuation_scaled_inverse_derivative_bound hα
  obtain ⟨B,hB,hBw⟩ := exists_coordinate_hessian_third_bound_on_compact d.coordinate_body_compact d.coordinateDefining_smooth
  let I := ((n.factorial:ℝ)*(max K 1)^n)/c
  have hI : 0 ≤ I := by dsimp [I]; positivity
  let C₀ := (n:ℝ)^2*I*B
  let C₁ := (n:ℝ)^2*(Ca*B+I*B)
  refine ⟨max (max C₀ C₁) 0,le_max_right _ _,?_⟩
  intro t ht j hs hp hMA
  have hInv (x : CoordinateSpace n) (hx : d.coordinateDefining x ≤ 0) (i l : Fin n) :
      |(intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ i l| ≤ I :=
    inverse_entry_bound_of_det_lower hc (by rw [hMA x hx]; exact (hdens t ht x hx).1)
      (hHess t ht j hs hp hMA x hx) i l
  constructor
  · intro x hx
    exact (abs_trace_product_le_entry_bounds hI (hInv x hx) (hBw x hx).1).trans
      ((le_max_left C₀ C₁).trans (le_max_left _ _))
  · intro x r hr hr1 hball k
    have hx : x ∈ interior {y | d.coordinateDefining y ≤ 0} := hball x (by simpa using hr)
    have hxs := interior_subset hx
    let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
    have hF : ContDiff ℝ ∞ F := by
      apply ContDiff.log _ (fun y => (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y)).ne')
      exact (contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp (contDiff_const.prodMk contDiff_id)
    have hMAlog (y : CoordinateSpace n) (hy : y ∈ interior {z | d.coordinateDefining z ≤ 0}) :
        (intrinsicHessian d.coordinate_body_convex α j.1 y).det = Real.exp (F y) := by
      dsimp [F]
      rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
      exact hMA y (interior_subset hy)
    obtain ⟨u,hu,hDu,hHu,hAux,hSource⟩ := intrinsic_local_representative_coefficient_source d.coordinate_body_convex
      hα j.1 hs (β := d.coordinateDefining) hMAlog hx k k
    have he : (fun y => linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 y)⁻¹ d.coordinateDefining y) =ᶠ[𝓝 x]
        (fun y => linearizedMA (variableInverseHessian u F y) d.coordinateDefining y) :=
      hAux.mono (fun y hy => congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => linearizedMA M d.coordinateDefining y) hy)
    rw [coordinateDerivative_congr_nhds he]
    apply (scaled_variable_linearizedMA_derivative_bound d.coordinateDefining_smooth
      (fun i l => (smooth_variableInverseHessian hu hF i l).differentiable (by simp)) x k hr.le hr1 hI hCa
      (by intro i l; rw [← hAux.self_of_nhds]; exact hInv x hxs i l)
      (by
        intro i l
        change r*|coordinateDerivative k (fun y => variableInverseHessian u F y i l) x| ≤ Ca
        rw [coordinateDerivative_congr_nhds (hAux.symm.mono (fun y hy => congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i l) hy))]
        exact hDA t ht j hs hp hMA x r hr hr1 hball k i l)
      (hBw x hxs).1 (fun i l => (hBw x hxs).2 i l k)).trans
    exact (le_max_right C₀ C₁).trans (le_max_left _ _)

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
