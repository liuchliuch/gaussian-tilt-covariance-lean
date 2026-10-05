import GaussianTilt.MomentMapClassicalDirichletIntrinsicThirdBounds
import GaussianTilt.MomentMapClassicalDirichletIntrinsicMixedCalculus

/-! # Genuine scaled tangential-field derivatives, including curvature-drift data -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

lemma coordinateDerivative_intrinsicDerivative
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α) {x : CoordinateSpace n} (hx : x ∈ interior S)
    (a k : Fin n) :
    coordinateDerivative k (intrinsicDerivative hS α j a) x = intrinsicHessian hS α j x a k := by
  have hd := (intrinsicDerivative_hasFDerivWithinAt hS hα j (interior_subset hx) a).hasFDerivAt
    (mem_interior_iff_mem_nhds.mp hx)
  exact congrArg (fun L : CoordinateSpace n →L[ℝ] ℝ => L (Pi.single k 1)) hd.fderiv

lemma coordinateHessian_intrinsicDerivative
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α) {x : CoordinateSpace n} (hx : x ∈ interior S)
    (a k l : Fin n) :
    coordinateHessian (intrinsicDerivative hS α j a) x k l =
      coordinateDerivative l (fun y => intrinsicHessian hS α j y a k) x := by
  apply coordinateDerivative_congr_nhds
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  exact coordinateDerivative_intrinsicDerivative hS hα j hy a k

lemma coordinateDerivative_intrinsicTangentField
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α) {x : CoordinateSpace n} (hx : x ∈ interior S)
    {β : CoordinateSpace n → ℝ} (hβ : DifferentiableAt ℝ β x) (a q k : Fin n) :
    coordinateDerivative k (intrinsicTangentField hS α j β a q) x =
      intrinsicHessian hS α j x a k - β x*intrinsicHessian hS α j x q k -
        coordinateDerivative k β x*intrinsicDerivative hS α j q x := by
  have hd := (intrinsicTangentField_hasFDerivWithinAt hS hα j (interior_subset hx) hβ a q).hasFDerivAt
    (mem_interior_iff_mem_nhds.mp hx)
  exact (congrArg (fun L : CoordinateSpace n →L[ℝ] ℝ => L (Pi.single k 1)) hd.fderiv).trans
    (intrinsicTangentDifferential_apply_coordinate hS α j β a q k x)

lemma coordinateHessian_intrinsicTangentField
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S))
    {x : CoordinateSpace n} (hx : x ∈ interior S)
    {β : CoordinateSpace n → ℝ} (hβ : ContDiffAt ℝ 2 β x) (a q k l : Fin n) :
    coordinateHessian (intrinsicTangentField hS α j β a q) x k l =
      coordinateDerivative l (fun y => intrinsicHessian hS α j y a k) x -
      β x*coordinateDerivative l (fun y => intrinsicHessian hS α j y q k) x -
      coordinateDerivative k β x*intrinsicHessian hS α j x q l -
      coordinateDerivative l β x*intrinsicHessian hS α j x q k -
      coordinateHessian β x k l*intrinsicDerivative hS α j q x := by
  have ha := contDiffAt_infty.mp (contDiffAt_intrinsicDerivative hS hα j hs hx a) 2
  have hq := contDiffAt_infty.mp (contDiffAt_intrinsicDerivative hS hα j hs hx q) 2
  change coordinateHessian (fun y => intrinsicDerivative hS α j a y - β y*intrinsicDerivative hS α j q y) x k l = _
  rw [coordinateHessian_sub_at ha (hβ.mul hq), coordinateHessian_mul_at hβ hq]
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,
    Matrix.vecMulVec_apply,smul_eq_mul,coordinateGradient,
    coordinateHessian_intrinsicDerivative hS hα j hx,
    coordinateDerivative_intrinsicDerivative hS hα j hx]
  ring

lemma intrinsicTangentField_first_bound
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α) {x : CoordinateSpace n} (hx : x ∈ interior S)
    {β : CoordinateSpace n → ℝ} (hβ : DifferentiableAt ℝ β x) (a q k : Fin n)
    {G K B₀ B₁ : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hG : |intrinsicDerivative hS α j q x| ≤ G)
    (hK : ∀ i l, |intrinsicHessian hS α j x i l| ≤ K)
    (hb₀ : |β x| ≤ B₀) (hb₁ : |coordinateDerivative k β x| ≤ B₁) :
    |coordinateDerivative k (intrinsicTangentField hS α j β a q) x| ≤ (1+B₀)*K+B₁*G := by
  rw [coordinateDerivative_intrinsicTangentField hS hα j hx hβ]
  calc
    _ ≤ |intrinsicHessian hS α j x a k| + |β x| * |intrinsicHessian hS α j x q k| +
        |coordinateDerivative k β x| * |intrinsicDerivative hS α j q x| := by
      calc
        _ ≤ _ := (abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)
        _ = _ := by simp only [abs_mul]
    _ ≤ K+B₀*K+B₁*G := by gcongr <;> exact hK _ _
    _ = _ := by ring

lemma intrinsicTangentField_scaled_second_bound
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S))
    {x : CoordinateSpace n} (hx : x ∈ interior S)
    {β : CoordinateSpace n → ℝ} (hβ : ContDiffAt ℝ 2 β x) (a q k l : Fin n)
    {r G K T B₀ B₁ B₂ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hG : |intrinsicDerivative hS α j q x| ≤ G)
    (hK : ∀ i m, |intrinsicHessian hS α j x i m| ≤ K)
    (hT : ∀ i m z, r*|coordinateDerivative z (fun y => intrinsicHessian hS α j y i m) x| ≤ T)
    (hb₀ : |β x| ≤ B₀) (hb₁ : ∀ z, |coordinateDerivative z β x| ≤ B₁)
    (hb₂ : |coordinateHessian β x k l| ≤ B₂) :
    r*|coordinateHessian (intrinsicTangentField hS α j β a q) x k l| ≤
      (1+B₀)*T+2*B₁*K+B₂*G := by
  rw [coordinateHessian_intrinsicTangentField hS hα j hs hx hβ]
  have hnonG : 0 ≤ G := (abs_nonneg _).trans hG
  have hnonK : 0 ≤ K := (abs_nonneg _).trans (hK q k)
  have hbase : |coordinateDerivative l (fun y => intrinsicHessian hS α j y a k) x -
      β x*coordinateDerivative l (fun y => intrinsicHessian hS α j y q k) x -
      coordinateDerivative k β x*intrinsicHessian hS α j x q l -
      coordinateDerivative l β x*intrinsicHessian hS α j x q k -
      coordinateHessian β x k l*intrinsicDerivative hS α j q x| ≤
      |coordinateDerivative l (fun y => intrinsicHessian hS α j y a k) x| +
      |β x| * |coordinateDerivative l (fun y => intrinsicHessian hS α j y q k) x| +
      |coordinateDerivative k β x| * |intrinsicHessian hS α j x q l| +
      |coordinateDerivative l β x| * |intrinsicHessian hS α j x q k| +
      |coordinateHessian β x k l| * |intrinsicDerivative hS α j q x| := by
    calc
      _ ≤ _ := (abs_sub _ _).trans (add_le_add_right ((abs_sub _ _).trans
        (add_le_add_right ((abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)) _)) _)
      _ = _ := by simp only [abs_mul]
  calc
    _ ≤ r*(_ + _ + _ + _ + _) := mul_le_mul_of_nonneg_left hbase hr.le
    _ = r*|coordinateDerivative l (fun y => intrinsicHessian hS α j y a k) x| +
        |β x| * (r*|coordinateDerivative l (fun y => intrinsicHessian hS α j y q k) x|) +
        r*(|coordinateDerivative k β x| * |intrinsicHessian hS α j x q l|) +
        r*(|coordinateDerivative l β x| * |intrinsicHessian hS α j x q k|) +
        r*(|coordinateHessian β x k l| * |intrinsicDerivative hS α j q x|) := by ring
    _ ≤ T+B₀*T+1*(B₁*K)+1*(B₁*K)+1*(B₂*G) := by gcongr <;> first | exact hT _ _ _ | exact hK _ _ | exact hb₁ _
    _ = _ := by ring

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- Both actual derivative controls needed for differentiating the curvature
term in the flattened tangential equation, with constants constructed from
the fixed domain and chart. -/
theorem intrinsic_dirichletContinuation_chart_tangent_derivative_bounds [NeZero n]
    {α : ℝ} (hα : 0 < α) (p : BoundaryChartPatch d.coordinateDefining) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) 1,
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
  obtain ⟨G,hG,hgrad⟩ := d.intrinsic_dirichletContinuation_uniform_first hα
  obtain ⟨K,hK,hHess⟩ := d.intrinsic_dirichletContinuation_uniform_hessian hα
  obtain ⟨T,hT,hthird⟩ := d.intrinsic_dirichletContinuation_scaled_third_bound hα
  let C₁ := (1+p.bound₀)*K+p.bound₁*G
  let C₂ := (1+p.bound₀)*T+2*p.bound₁*K+p.bound₂*G
  refine ⟨max (max C₁ C₂) 0,le_max_right _ _,?_⟩
  intro t ht j hs hp hMA x hxp r hr hr1 hball a k l
  have hx : x ∈ interior {y | d.coordinateDefining y ≤ 0} := hball x (by simpa using hr)
  have hxs := interior_subset hx
  have hβ := p.smooth x hxp a
  constructor
  · apply (intrinsicTangentField_first_bound d.coordinate_body_convex hα j.1 hx
      (hβ.differentiableAt (by simp)) a p.index k p.bound₀_nonneg p.bound₁_nonneg
      (hgrad t ht j hs (fun y hy => hp y (interior_subset hy))
        (fun y hy => hMA y (interior_subset hy)) x hxs p.index)
      (hHess t ht j hs hp hMA x hxs) (p.value_bound x hxp a) (p.derivative_bound x hxp a k)).trans
    exact (le_max_left C₁ C₂).trans (le_max_left _ _)
  · apply (intrinsicTangentField_scaled_second_bound d.coordinate_body_convex hα j.1 hs hx
      (contDiffAt_infty.mp hβ 2) a p.index k l hr hr1 p.bound₀_nonneg p.bound₁_nonneg p.bound₂_nonneg
      (hgrad t ht j hs (fun y hy => hp y (interior_subset hy))
        (fun y hy => hMA y (interior_subset hy)) x hxs p.index)
      (hHess t ht j hs hp hMA x hxs)
      (fun i m z => hthird t ht j hs hp hMA x r hr hr1 hball z i m)
      (p.value_bound x hxp a) (p.derivative_bound x hxp a) (p.hessian_bound x hxp a k l)).trans
    exact (le_max_right C₁ C₂).trans (le_max_left _ _)

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
