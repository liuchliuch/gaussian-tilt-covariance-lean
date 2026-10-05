import GaussianTilt.MomentMapClassicalDirichletUniformExponentCoefficients
import GaussianTilt.MomentMapClassicalDirichletIntrinsicFlatSystem
import GaussianTilt.MomentMapClassicalDirichletIntrinsicHessianRecovery

/-! # Domain-only a priori constants chosen before the input Hölder exponent -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

theorem intrinsic_dirichletContinuation_chart_tangent_derivative_bounds_all_exponents [NeZero n]
     (p : BoundaryChartPatch d.coordinateDefining) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : ℝ), 0 < α → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ x ∈ Metric.closedBall p.center p.radius, ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r →
        y ∈ interior {z | d.coordinateDefining z ≤ 0}) → ∀ a k l,
      let T := intrinsicTangentField d.coordinate_body_convex α j.1
        (boundaryChartCoefficient d.coordinateDefining p.index a) a p.index
      |coordinateDerivative k T x| ≤ C ∧ r*|coordinateHessian T x k l| ≤ C := by
  obtain ⟨G,hG,hgrad⟩ := d.intrinsic_dirichletContinuation_uniform_first_all_exponents
  obtain ⟨K,hK,hHess⟩ := d.intrinsic_dirichletContinuation_uniform_hessian_all_exponents
  obtain ⟨T,hT,hthird⟩ := d.intrinsic_dirichletContinuation_scaled_third_bound_all_exponents
  let C₁ := (1+p.bound₀)*K+p.bound₁*G
  let C₂ := (1+p.bound₀)*T+2*p.bound₁*K+p.bound₂*G
  refine ⟨max (max C₁ C₂) 0,le_max_right _ _,?_⟩
  intro α hα t ht j hs hp hMA x hxp r hr hr1 hball a k l
  have hx : x ∈ interior {y | d.coordinateDefining y ≤ 0} := hball x (by simpa using hr)
  have hxs := interior_subset hx
  have hβ := p.smooth x hxp a
  constructor
  · apply (intrinsicTangentField_first_bound d.coordinate_body_convex hα j.1 hx
      (hβ.differentiableAt (by simp)) a p.index k p.bound₀_nonneg p.bound₁_nonneg
      (hgrad α hα t ht j hs (fun y hy => hp y (interior_subset hy))
        (fun y hy => hMA y (interior_subset hy)) x hxs p.index)
      (hHess α hα t ht j hs hp hMA x hxs) (p.value_bound x hxp a) (p.derivative_bound x hxp a k)).trans
    exact (le_max_left C₁ C₂).trans (le_max_left _ _)
  · apply (intrinsicTangentField_scaled_second_bound d.coordinate_body_convex hα j.1 hs hx
      (contDiffAt_infty.mp hβ 2) a p.index k l hr hr1 p.bound₀_nonneg p.bound₁_nonneg p.bound₂_nonneg
      (hgrad α hα t ht j hs (fun y hy => hp y (interior_subset hy))
        (fun y hy => hMA y (interior_subset hy)) x hxs p.index)
      (hHess α hα t ht j hs hp hMA x hxs)
      (fun i m z => hthird α hα t ht j hs hp hMA x r hr hr1 hball z i m)
      (p.value_bound x hxp a) (p.derivative_bound x hxp a) (p.hessian_bound x hxp a k l)).trans
    exact (le_max_right C₁ C₂).trans (le_max_left _ _)


theorem intrinsic_dirichletContinuation_chart_forcing_bounds_all_exponents [NeZero n] 
    (p : BoundaryChartPatch d.coordinateDefining) :
    ∃ β : Fin n → CoordinateSpace n → ℝ, ∃ C : ℝ, 0 ≤ C ∧
      (∀ a, ContDiff ℝ ∞ (β a)) ∧
      (∀ x ∈ Metric.closedBall p.center p.radius, ∀ a,
        β a =ᶠ[𝓝 x] boundaryChartCoefficient d.coordinateDefining p.index a) ∧
      ∀ (α : ℝ), 0 < α → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ x ∈ Metric.closedBall p.center p.radius, ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r →
        y ∈ interior {z | d.coordinateDefining z ≤ 0}) → ∀ a,
      let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
      |intrinsicTangentSource d.coordinate_body_convex α j.1 F (β a) a p.index x| ≤ C ∧
      ∀ k, r*|coordinateDerivative k (intrinsicTangentSource d.coordinate_body_convex α j.1 F (β a) a p.index) x| ≤ C := by
  obtain ⟨β,B₃,hB₃,hβs,heβ,hβ3⟩ := p.exists_smooth_chart_representatives_with_third_bound d.coordinateDefining_smooth
  obtain ⟨G,hG,hgrad⟩ := d.intrinsic_dirichletContinuation_uniform_first_all_exponents
  obtain ⟨H,hH,hHess⟩ := d.intrinsic_dirichletContinuation_uniform_hessian_all_exponents
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K₁,hK₁,hF₁⟩ := dirichletContinuationDensity_uniform_log_coordinateDerivative d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K₂,hK₂,hF₂⟩ := dirichletContinuationDensity_uniform_log_hessian d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨Cₐ,hCₐ,hDA⟩ := d.intrinsic_dirichletContinuation_scaled_inverse_derivative_bound_all_exponents
  let I := ((n.factorial:ℝ)*(max H 1)^n)/c
  have hI : 0 ≤ I := by dsimp [I]; positivity
  let C₀ := K₁+p.bound₀*K₁+G*((n:ℝ)^2*I*p.bound₂)+2*p.bound₁
  let C₁ := K₂+p.bound₁*K₁+p.bound₀*K₂+H*((n:ℝ)^2*I*p.bound₂)+
    G*((n:ℝ)^2*(Cₐ*p.bound₂+I*B₃))+2*p.bound₂
  let C := max (max C₀ C₁) 0
  refine ⟨β,C,le_max_right _ _,hβs,heβ,?_⟩
  intro α hα t ht j hs hp hMA x hxp r hr hr1 hball a
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  have hx : x ∈ interior {y | d.coordinateDefining y ≤ 0} := hball x (by simpa using hr)
  have hxs := interior_subset hx
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.log _ (fun y => (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y)).ne')
    exact (contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp (contDiff_const.prodMk contDiff_id)
  have hMAlog (y : CoordinateSpace n) (hy : y ∈ interior {z | d.coordinateDefining z ≤ 0}) :
      (intrinsicHessian d.coordinate_body_convex α j.1 y).det = Real.exp (F y) := by
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
    exact hMA y (interior_subset hy)
  obtain ⟨u,hu,hDu,hHu,hAux,hSource⟩ := intrinsic_local_representative_coefficient_source d.coordinate_body_convex
    hα j.1 hs (β := β a) hMAlog hx a p.index
  let B := variableInverseHessian u F
  have hInv : ∀ i l, |B x i l| ≤ I := by
    dsimp only [B]
    rw [← hAux.self_of_nhds]
    exact inverse_entry_bound_of_det_lower hc (by rw [hMA x hxs]; exact (hdens t ht x hxs).1)
      (hHess α hα t ht j hs hp hMA x hxs)
  have hDB (k i l : Fin n) : r*|matrixCoordinateDerivative B k x i l| ≤ Cₐ := by
    have he : (fun y => B y i l) =ᶠ[𝓝 x] (fun y => (intrinsicHessian d.coordinate_body_convex α j.1 y)⁻¹ i l) :=
      hAux.symm.mono (fun y hy => congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i l) hy)
    change r*|coordinateDerivative k (fun y => B y i l) x| ≤ Cₐ
    rw [coordinateDerivative_congr_nhds he]
    exact hDA α hα t ht j hs hp hMA x r hr hr1 hball k i l
  have hGrad (i : Fin n) : |coordinateDerivative i u x| ≤ G := by
    rw [← (hDu i).self_of_nhds]
    exact hgrad α hα t ht j hs (fun y hy => hp y (interior_subset hy))
      (fun y hy => hMA y (interior_subset hy)) x hxs i
  have hHessU (i l : Fin n) : |coordinateHessian u x i l| ≤ H := by
    rw [← hHu.self_of_nhds]
    exact hHess α hα t ht j hs hp hMA x hxs i l
  have hβ0 : |β a x| ≤ p.bound₀ := by rw [(heβ x hxp a).self_of_nhds]; exact p.value_bound x hxp a
  have hβ1 (k : Fin n) : |coordinateDerivative k (β a) x| ≤ p.bound₁ := by
    rw [coordinateDerivative_congr_nhds (heβ x hxp a)]
    exact p.derivative_bound x hxp a k
  have hβ2 (i l : Fin n) : |coordinateHessian (β a) x i l| ≤ p.bound₂ := by
    rw [coordinateHessian_congr_nhds (heβ x hxp a)]
    exact p.hessian_bound x hxp a i l
  constructor
  · rw [hSource.self_of_nhds]
    have hh := tangentialFieldForcing_abs_bound x a p.index hI hG p.bound₀_nonneg hInv
      (hGrad p.index) hβ0 (hβ1 p.index) hβ2 (hF₁ t ht x hxs a) (hF₁ t ht x hxs p.index)
    exact hh.trans ((le_max_left C₀ C₁).trans (le_max_left _ _))
  · intro k
    rw [coordinateDerivative_congr_nhds hSource]
    have hh := scaled_tangentialFieldForcing_derivative_bound hu hF (hβs a)
      (fun i l => (smooth_variableInverseHessian hu hF i l).differentiable (by simp)) x a p.index k
      hr.le hr1 hI hCₐ hG hH p.bound₀_nonneg p.bound₁_nonneg hInv (hDB k)
      (hGrad p.index) (hHessU p.index k) hβ0 (hβ1 k) hβ2
      (fun i l => hβ3 x hxp a i l k) (hF₁ t ht x hxs p.index)
      (hF₂ t ht x hxs a k) (hF₂ t ht x hxs p.index k)
    exact hh.trans ((le_max_right C₀ C₁).trans (le_max_left _ _))


theorem intrinsic_dirichletContinuation_curvature_bounds_all_exponents [NeZero n]  :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : ℝ), 0 < α → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      let b := fun x => linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ d.coordinateDefining x
      (∀ x ∈ {y | d.coordinateDefining y ≤ 0}, |b x| ≤ C) ∧
      (∀ x : CoordinateSpace n, ∀ r : ℝ, 0 < r → r ≤ 1 →
        (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r →
          y ∈ interior {z | d.coordinateDefining z ≤ 0}) → ∀ k, r*|coordinateDerivative k b x| ≤ C) := by
  obtain ⟨K,hK,hHess⟩ := d.intrinsic_dirichletContinuation_uniform_hessian_all_exponents
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨Ca,hCa,hDA⟩ := d.intrinsic_dirichletContinuation_scaled_inverse_derivative_bound_all_exponents
  obtain ⟨B,hB,hBw⟩ := exists_coordinate_hessian_third_bound_on_compact d.coordinate_body_compact d.coordinateDefining_smooth
  let I := ((n.factorial:ℝ)*(max K 1)^n)/c
  have hI : 0 ≤ I := by dsimp [I]; positivity
  let C₀ := (n:ℝ)^2*I*B
  let C₁ := (n:ℝ)^2*(Ca*B+I*B)
  refine ⟨max (max C₀ C₁) 0,le_max_right _ _,?_⟩
  intro α hα t ht j hs hp hMA
  have hInv (x : CoordinateSpace n) (hx : d.coordinateDefining x ≤ 0) (i l : Fin n) :
      |(intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ i l| ≤ I :=
    inverse_entry_bound_of_det_lower hc (by rw [hMA x hx]; exact (hdens t ht x hx).1)
      (hHess α hα t ht j hs hp hMA x hx) i l
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
        exact hDA α hα t ht j hs hp hMA x r hr hr1 hball k i l)
      (hBw x hxs).1 (fun i l => (hBw x hxs).2 i l k)).trans
    exact (le_max_right C₀ C₁).trans (le_max_left _ _)


theorem intrinsic_dirichletContinuation_chart_within_bounds_all_exponents [NeZero n] 
    (p : BoundaryChartPatch d.coordinateDefining) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : ℝ), 0 < α → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ x ∈ Metric.closedBall p.center p.radius, d.coordinateDefining x ≤ 0 →
      ∀ a (β : CoordinateSpace n → ℝ),
      β =ᶠ[𝓝 x] boundaryChartCoefficient d.coordinateDefining p.index a →
      |intrinsicTangentField d.coordinate_body_convex α j.1 β a p.index x| ≤ C ∧
      ‖intrinsicTangentDifferential d.coordinate_body_convex α j.1 β a p.index x‖ ≤ C := by
  obtain ⟨G,hG,hgrad⟩ := d.intrinsic_dirichletContinuation_uniform_first_all_exponents
  obtain ⟨K,hK,hH⟩ := d.intrinsic_dirichletContinuation_uniform_hessian_all_exponents
  let C₀ := (1+p.bound₀)*G
  let C₁ := (n:ℝ)*((1+p.bound₀)*K+p.bound₁*G)
  refine ⟨max (max C₀ C₁) 0,le_max_right _ _,?_⟩
  intro α hα t ht j hs hp hMA x hxp hx a β he
  have hgs (i : Fin n) := hgrad α hα t ht j hs (fun y hy => hp y (interior_subset hy))
    (fun y hy => hMA y (interior_subset hy)) x hx i
  have hβ0 : |β x| ≤ p.bound₀ := by rw [he.self_of_nhds]; exact p.value_bound x hxp a
  have hβ1 (k : Fin n) : |coordinateDerivative k β x| ≤ p.bound₁ := by
    rw [coordinateDerivative_congr_nhds he]; exact p.derivative_bound x hxp a k
  constructor
  · have hh : |intrinsicTangentField d.coordinate_body_convex α j.1 β a p.index x| ≤ C₀ := by
      unfold intrinsicTangentField
      calc
        _ ≤ |intrinsicDerivative d.coordinate_body_convex α j.1 a x|+
            |β x| * |intrinsicDerivative d.coordinate_body_convex α j.1 p.index x| := by
          simpa only [abs_mul] using abs_sub (intrinsicDerivative d.coordinate_body_convex α j.1 a x)
            (β x*intrinsicDerivative d.coordinate_body_convex α j.1 p.index x)
        _ ≤ G+p.bound₀*G := add_le_add (hgs a) (mul_le_mul hβ0 (hgs p.index) (abs_nonneg _) p.bound₀_nonneg)
        _ = C₀ := by dsimp [C₀]; ring
    exact hh.trans ((le_max_left C₀ C₁).trans (le_max_left _ _))
  · exact (norm_intrinsicTangentDifferential_bound d.coordinate_body_convex α j.1 β a p.index x
      hG hK p.bound₀_nonneg p.bound₁_nonneg (hgs p.index) (hH α hα t ht j hs hp hMA x hx) hβ0 hβ1).trans
      ((le_max_right C₀ C₁).trans (le_max_left _ _))


theorem intrinsic_dirichletContinuation_chart_scalar_bounds_all_exponents [NeZero n] 
    (p : BoundaryChartPatch d.coordinateDefining) :
    ∃ β : Fin n → CoordinateSpace n → ℝ, ∃ M : ℝ, 0 ≤ M ∧
      (∀ a, ContDiff ℝ ∞ (β a)) ∧
      (∀ x ∈ Metric.closedBall p.center p.radius, ∀ a,
        β a =ᶠ[𝓝 x] boundaryChartCoefficient d.coordinateDefining p.index a) ∧
      ∀ (α : ℝ), 0 < α → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ x ∈ Metric.closedBall p.center p.radius, ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r →
        y ∈ interior {z | d.coordinateDefining z ≤ 0}) → ∀ a,
      let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
      let T := intrinsicTangentField d.coordinate_body_convex α j.1 (β a) a p.index
      let g := intrinsicTangentSource d.coordinate_body_convex α j.1 F (β a) a p.index
      let b := fun x => linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ d.coordinateDefining x
      |T x| ≤ M ∧ (∀ k, |coordinateDerivative k T x| ≤ M) ∧
      (∀ k l, r*|coordinateHessian T x k l| ≤ M) ∧
      |g x| ≤ M ∧ (∀ k, r*|coordinateDerivative k g x| ≤ M) ∧
      |b x| ≤ M ∧ (∀ k, r*|coordinateDerivative k b x| ≤ M) := by
  obtain ⟨β,Cg,hCg,hβ,heβ,hg⟩ := d.intrinsic_dirichletContinuation_chart_forcing_bounds_all_exponents p
  obtain ⟨Ct,hCt,htan⟩ := d.intrinsic_dirichletContinuation_chart_tangent_derivative_bounds_all_exponents p
  obtain ⟨Cb,hCb,hcurv⟩ := d.intrinsic_dirichletContinuation_curvature_bounds_all_exponents
  obtain ⟨G,hG,hgrad⟩ := d.intrinsic_dirichletContinuation_uniform_first_all_exponents
  let M := Cg+Ct+Cb+(1+p.bound₀)*G
  have hMG : 0 ≤ (1+p.bound₀)*G := mul_nonneg (by linarith [p.bound₀_nonneg]) hG
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨β,M,hM,hβ,heβ,?_⟩
  intro α hα t ht j hs hp hMA x hxp r hr hr1 hball a
  have hx : x ∈ interior {y | d.coordinateDefining y ≤ 0} := hball x (by simpa using hr)
  have hxs := interior_subset hx
  have hT := intrinsicTangentField_congr_nhds_beta d.coordinate_body_convex α j.1 (heβ x hxp a) a p.index
  have hT0 : |intrinsicTangentField d.coordinate_body_convex α j.1 (β a) a p.index x| ≤ (1+p.bound₀)*G := by
    have hga := hgrad α hα t ht j hs (fun y hy => hp y (interior_subset hy))
      (fun y hy => hMA y (interior_subset hy)) x hxs a
    have hgq := hgrad α hα t ht j hs (fun y hy => hp y (interior_subset hy))
      (fun y hy => hMA y (interior_subset hy)) x hxs p.index
    rw [hT.self_of_nhds]
    unfold intrinsicTangentField
    calc
      _ ≤ |intrinsicDerivative d.coordinate_body_convex α j.1 a x|+
        |boundaryChartCoefficient d.coordinateDefining p.index a x| * |intrinsicDerivative d.coordinate_body_convex α j.1 p.index x| := by
          simpa only [abs_mul] using abs_sub (intrinsicDerivative d.coordinate_body_convex α j.1 a x)
            (boundaryChartCoefficient d.coordinateDefining p.index a x*intrinsicDerivative d.coordinate_body_convex α j.1 p.index x)
      _ ≤ G+p.bound₀*G := add_le_add hga (mul_le_mul (p.value_bound x hxp a) hgq (abs_nonneg _) p.bound₀_nonneg)
      _ = _ := by ring
  have hgdata := hg α hα t ht j hs hp hMA x hxp r hr hr1 hball a
  have hbdata := hcurv α hα t ht j hs hp hMA
  refine ⟨hT0.trans (by dsimp [M]; linarith),?_,?_,hgdata.1.trans (by dsimp [M]; linarith),?_,
    (hbdata.1 x hxs).trans (by dsimp [M]; linarith),?_⟩
  · intro k
    rw [coordinateDerivative_congr_nhds hT]
    exact ((htan α hα t ht j hs hp hMA x hxp r hr hr1 hball a k k).1).trans (by dsimp [M]; linarith)
  · intro k l
    rw [coordinateHessian_congr_nhds hT]
    exact ((htan α hα t ht j hs hp hMA x hxp r hr hr1 hball a k l).2).trans (by dsimp [M]; linarith)
  · intro k
    exact (hgdata.2 k).trans (by dsimp [M]; linarith)
  · intro k
    exact (hbdata.2 x r hr hr1 hball k).trans (by dsimp [M]; linarith)


end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
