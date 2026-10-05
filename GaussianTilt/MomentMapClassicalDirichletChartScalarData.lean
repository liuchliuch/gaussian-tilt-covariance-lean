import GaussianTilt.MomentMapClassicalDirichletFlattenedEquation

/-! # Constructed scalar data for the intrinsic boundary chart equation -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

lemma contDiffOn_intrinsicTangentField
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S))
    {β : CoordinateSpace n → ℝ} (hβ : ContDiff ℝ ∞ β) (a q : Fin n) :
    ContDiffOn ℝ ∞ (intrinsicTangentField hS α j β a q) (interior S) := by
  intro x hx
  exact ((contDiffAt_intrinsicDerivative hS hα j hs hx a).sub
    (hβ.contDiffAt.mul (contDiffAt_intrinsicDerivative hS hα j hs hx q))).contDiffWithinAt

lemma continuousOn_intrinsicTangentField
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) {β : CoordinateSpace n → ℝ}
    (hβ : ContinuousOn β S) (a q : Fin n) :
    ContinuousOn (intrinsicTangentField hS α j β a q) S :=
  (continuousOn_intrinsicDerivative hS α j a).sub (hβ.mul (continuousOn_intrinsicDerivative hS α j q))

lemma intrinsicTangentField_congr_nhds_beta
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) {β γ : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (he : β =ᶠ[𝓝 x] γ) (a q : Fin n) :
    intrinsicTangentField hS α j β a q =ᶠ[𝓝 x] intrinsicTangentField hS α j γ a q := by
  filter_upwards [he] with y hy
  simp only [intrinsicTangentField,hy]

lemma contDiffOn_intrinsicCurvature
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S))
    {F w : CoordinateSpace n → ℝ} (hF : ContDiff ℝ ∞ F) (hw : ContDiff ℝ ∞ w)
    (hMA : ∀ y ∈ interior S, (intrinsicHessian hS α j y).det = Real.exp (F y)) :
    ContDiffOn ℝ ∞ (fun x => linearizedMA (intrinsicHessian hS α j x)⁻¹ w x) (interior S) := by
  unfold linearizedMA Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply]
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro l _
  exact (contDiffOn_intrinsicInverseHessian hS hα j hs hF hMA i l).mul
    (smooth_coordinateHessian hw l i).contDiffOn

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- Fixed smooth chart representatives and one uniform constant control
all scalar fields occurring in the genuine flattened tangential PDE. -/
theorem intrinsic_dirichletContinuation_chart_scalar_bounds [NeZero n] {α : ℝ} (hα : 0 < α)
    (p : BoundaryChartPatch d.coordinateDefining) :
    ∃ β : Fin n → CoordinateSpace n → ℝ, ∃ M : ℝ, 0 ≤ M ∧
      (∀ a, ContDiff ℝ ∞ (β a)) ∧
      (∀ x ∈ Metric.closedBall p.center p.radius, ∀ a,
        β a =ᶠ[𝓝 x] boundaryChartCoefficient d.coordinateDefining p.index a) ∧
      ∀ t ∈ Icc (0:ℝ) 1,
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
  obtain ⟨β,Cg,hCg,hβ,heβ,hg⟩ := d.intrinsic_dirichletContinuation_chart_forcing_bounds hα p
  obtain ⟨Ct,hCt,htan⟩ := d.intrinsic_dirichletContinuation_chart_tangent_derivative_bounds hα p
  obtain ⟨Cb,hCb,hcurv⟩ := d.intrinsic_dirichletContinuation_curvature_bounds hα
  obtain ⟨G,hG,hgrad⟩ := d.intrinsic_dirichletContinuation_uniform_first hα
  let M := Cg+Ct+Cb+(1+p.bound₀)*G
  have hMG : 0 ≤ (1+p.bound₀)*G := mul_nonneg (by linarith [p.bound₀_nonneg]) hG
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨β,M,hM,hβ,heβ,?_⟩
  intro t ht j hs hp hMA x hxp r hr hr1 hball a
  have hx : x ∈ interior {y | d.coordinateDefining y ≤ 0} := hball x (by simpa using hr)
  have hxs := interior_subset hx
  have hT := intrinsicTangentField_congr_nhds_beta d.coordinate_body_convex α j.1 (heβ x hxp a) a p.index
  have hT0 : |intrinsicTangentField d.coordinate_body_convex α j.1 (β a) a p.index x| ≤ (1+p.bound₀)*G := by
    have hga := hgrad t ht j hs (fun y hy => hp y (interior_subset hy))
      (fun y hy => hMA y (interior_subset hy)) x hxs a
    have hgq := hgrad t ht j hs (fun y hy => hp y (interior_subset hy))
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
  have hgdata := hg t ht j hs hp hMA x hxp r hr hr1 hball a
  have hbdata := hcurv t ht j hs hp hMA
  refine ⟨hT0.trans (by dsimp [M]; linarith),?_,?_,hgdata.1.trans (by dsimp [M]; linarith),?_,
    (hbdata.1 x hxs).trans (by dsimp [M]; linarith),?_⟩
  · intro k
    rw [coordinateDerivative_congr_nhds hT]
    exact ((htan t ht j hs hp hMA x hxp r hr hr1 hball a k k).1).trans (by dsimp [M]; linarith)
  · intro k l
    rw [coordinateHessian_congr_nhds hT]
    exact ((htan t ht j hs hp hMA x hxp r hr hr1 hball a k l).2).trans (by dsimp [M]; linarith)
  · intro k
    exact (hgdata.2 k).trans (by dsimp [M]; linarith)
  · intro k
    exact (hbdata.2 x r hr hr1 hball k).trans (by dsimp [M]; linarith)

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
