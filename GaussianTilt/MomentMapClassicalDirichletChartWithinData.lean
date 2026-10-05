import GaussianTilt.MomentMapClassicalDirichletChartScalarData

/-! # Actual continuous closed-domain derivatives of the tangential fields -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

lemma continuousOn_intrinsicTangentDifferential
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) {β : CoordinateSpace n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (a q : Fin n) :
    ContinuousOn (intrinsicTangentDifferential hS α j β a q) S := by
  have hH : ContinuousOn (intrinsicSecond hS α j) S := continuousOn_extendValue α _
  have ha : ContinuousOn (fun x => (ContinuousLinearMap.apply ℝ ℝ (Pi.single a 1)).comp
      (intrinsicSecond hS α j x)) S := continuousOn_const.clm_comp hH
  have hq : ContinuousOn (fun x => (ContinuousLinearMap.apply ℝ ℝ (Pi.single q 1)).comp
      (intrinsicSecond hS α j x)) S := continuousOn_const.clm_comp hH
  exact ha.sub ((hβ.continuous.continuousOn.smul hq).add
    ((continuousOn_intrinsicDerivative hS α j q).smul (hβ.continuous_fderiv (by simp)).continuousOn))

lemma norm_intrinsicTangentDifferential_bound
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) (β : CoordinateSpace n → ℝ) (a q : Fin n)
    (x : CoordinateSpace n) {G K B₀ B₁ : ℝ}
    (hG : 0 ≤ G) (hK : 0 ≤ K) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hgrad : |intrinsicDerivative hS α j q x| ≤ G)
    (hH : ∀ i l, |intrinsicHessian hS α j x i l| ≤ K)
    (hβ0 : |β x| ≤ B₀) (hβ1 : ∀ k, |coordinateDerivative k β x| ≤ B₁) :
    ‖intrinsicTangentDifferential hS α j β a q x‖ ≤ (n:ℝ)*((1+B₀)*K+B₁*G) := by
  apply norm_covector_le_of_coordinate_bound _ (by positivity)
  intro k
  rw [intrinsicTangentDifferential_apply_coordinate]
  calc
    _ ≤ |intrinsicHessian hS α j x a k|+|β x| * |intrinsicHessian hS α j x q k|+
        |coordinateDerivative k β x| * |intrinsicDerivative hS α j q x| := by
      calc
        _ ≤ _ := (abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)
        _ = _ := by simp only [abs_mul]
    _ ≤ K+B₀*K+B₁*G := by gcongr <;> first | exact hH _ _ | exact hβ1 _
    _ = _ := by ring

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- Boundary-safe first-derivative bounds for every smooth representative
of a fixed chart coefficient. They use the actual continuous within jet. -/
theorem intrinsic_dirichletContinuation_chart_within_bounds [NeZero n] {α : ℝ} (hα : 0 < α)
    (p : BoundaryChartPatch d.coordinateDefining) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ x ∈ Metric.closedBall p.center p.radius, d.coordinateDefining x ≤ 0 →
      ∀ a (β : CoordinateSpace n → ℝ),
      β =ᶠ[𝓝 x] boundaryChartCoefficient d.coordinateDefining p.index a →
      |intrinsicTangentField d.coordinate_body_convex α j.1 β a p.index x| ≤ C ∧
      ‖intrinsicTangentDifferential d.coordinate_body_convex α j.1 β a p.index x‖ ≤ C := by
  obtain ⟨G,hG,hgrad⟩ := d.intrinsic_dirichletContinuation_uniform_first hα
  obtain ⟨K,hK,hH⟩ := d.intrinsic_dirichletContinuation_uniform_hessian hα
  let C₀ := (1+p.bound₀)*G
  let C₁ := (n:ℝ)*((1+p.bound₀)*K+p.bound₁*G)
  refine ⟨max (max C₀ C₁) 0,le_max_right _ _,?_⟩
  intro t ht j hs hp hMA x hxp hx a β he
  have hgs (i : Fin n) := hgrad t ht j hs (fun y hy => hp y (interior_subset hy))
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
      hG hK p.bound₀_nonneg p.bound₁_nonneg (hgs p.index) (hH t ht j hs hp hMA x hx) hβ0 hβ1).trans
      ((le_max_right C₀ C₁).trans (le_max_left _ _))

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
