import GaussianTilt.MomentMapClassicalDirichletChartLowerOrderModuli
import GaussianTilt.MomentMapClassicalDirichletHessianDifference

/-! # Genuine per-chart full Hessian approach from tangential derivatives -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators NNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- Actual full Hessian recovery at a pair of points of the closed body.
All lower-order moduli and nonsingularity constants are constructed. The
only new modulus input is the proved tangential-field derivative estimate. -/
theorem intrinsic_hessian_approach_of_tangent_derivative_approach [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (p : BoundaryChartPatch d.coordinateDefining) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ L : ℝ, γ ≤ 1 → 0 ≤ L →
      ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ β : Fin n → CoordinateSpace n → ℝ, (∀ a, ContDiff ℝ ∞ (β a)) →
      (∀ x ∈ Metric.closedBall p.center p.radius, ∀ a,
        β a =ᶠ[𝓝 x] boundaryChartCoefficient d.coordinateDefining p.index a) →
      ∀ x ∈ Metric.closedBall p.center p.radius, d.coordinateDefining x ≤ 0 →
      ∀ z ∈ Metric.closedBall p.center p.radius, d.coordinateDefining z ≤ 0 →
      ‖(coordinateEquiv n).symm x-(coordinateEquiv n).symm z‖ ≤ 1 →
      (∀ a k, |intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index x (Pi.single k 1)-
        intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index z (Pi.single k 1)| ≤
        L*‖(coordinateEquiv n).symm x-(coordinateEquiv n).symm z‖^γ) →
      ∀ i l, |intrinsicHessian d.coordinate_body_convex α j.1 x i l-intrinsicHessian d.coordinate_body_convex α j.1 z i l| ≤
        C*(1+L)*‖(coordinateEquiv n).symm x-(coordinateEquiv n).symm z‖^γ := by
  obtain ⟨K,hK,hHess⟩ := d.intrinsic_dirichletContinuation_uniform_hessian hα
  obtain ⟨G,hG,hgrad⟩ := d.intrinsic_dirichletContinuation_uniform_first hα
  obtain ⟨P,hP,hwithin⟩ := d.intrinsic_dirichletContinuation_chart_within_bounds hα p
  obtain ⟨c,F,hc,hF,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨Jg,hJg⟩ := d.intrinsic_dirichletContinuation_uniform_first_lipschitz hα
  obtain ⟨Jf,hJf⟩ := dirichletContinuationDensity_uniform_lipschitz d.coordinate_body_compact
    d.coordinate_body_convex d.coordinateDefining_smooth
  obtain ⟨C₀,hC₀,hrec⟩ := exists_hessian_difference_bound_of_tangent_field_data p.index hc hK
    p.bound₀_nonneg p.bound₁_nonneg hG hP hF.le
  let J := (n:ℝ)*p.bound₁+(n:ℝ)*p.bound₂+(Jg:ℝ)+(Jf:ℝ)
  have hnb₁ : 0 ≤ (n:ℝ)*p.bound₁ := mul_nonneg (Nat.cast_nonneg _) p.bound₁_nonneg
  have hnb₂ : 0 ≤ (n:ℝ)*p.bound₂ := mul_nonneg (Nat.cast_nonneg _) p.bound₂_nonneg
  have hJ : 0 ≤ J := by dsimp [J]; linarith [Jg.coe_nonneg,Jf.coe_nonneg]
  refine ⟨C₀*(J+1),mul_nonneg hC₀ (by linarith),?_⟩
  intro γ L hγ hL t ht j hp hMA β hβ heβ x hxp hx z hzp hz hdist hWT i l
  have hs := d.intrinsic_dirichletContinuation_interior_smooth hα hα1 ht j hp hMA
  let d₀ := ‖(coordinateEquiv n).symm x-(coordinateEquiv n).symm z‖
  have hd₀ : 0 ≤ d₀^γ := Real.rpow_nonneg (norm_nonneg _) _
  let ε := (J+L)*d₀^γ
  have hε : 0 ≤ ε := mul_nonneg (add_nonneg hJ hL) hd₀
  have hsub (Z : ℝ) (hZ : Z ≤ J) : Z*d₀^γ ≤ ε :=
    mul_le_mul_of_nonneg_right (by linarith) hd₀
  have hβ0 (y : CoordinateSpace n) (hy : y ∈ Metric.closedBall p.center p.radius) (a : Fin n) :
      |β a y| ≤ p.bound₀ := by rw [(heβ y hy a).self_of_nhds]; exact p.value_bound y hy a
  have hβ1 (y : CoordinateSpace n) (hy : y ∈ Metric.closedBall p.center p.radius) (a k : Fin n) :
      |coordinateDerivative k (β a) y| ≤ p.bound₁ := by
    rw [coordinateDerivative_congr_nhds (heβ y hy a)]; exact p.derivative_bound y hy a k
  have hGval (y : CoordinateSpace n) (hy : d.coordinateDefining y ≤ 0) :
      |intrinsicDerivative d.coordinate_body_convex α j.1 p.index y| ≤ G :=
    hgrad t ht j hs (fun y hy => hp y (interior_subset hy))
      (fun y hy => hMA y (interior_subset hy)) y hy p.index
  have hWval (y : CoordinateSpace n) (hy : y ∈ Metric.closedBall p.center p.radius)
      (hyS : d.coordinateDefining y ≤ 0) (a k : Fin n) :
      |intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index y (Pi.single k 1)| ≤ P := by
    have hh := (hwithin t ht j hs hp hMA y hy hyS a (β a) (heβ y hy a)).2
    have ha := (intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index y).le_opNorm (Pi.single k 1)
    simp only [Pi.norm_single,norm_one,mul_one,Real.norm_eq_abs] at ha
    exact ha.trans hh
  have hbm (a : Fin n) : |β a x-β a z| ≤ ε := by
    apply (lipschitzOn_euclidean_holder_small
      (p.coefficient_rep_lipschitz a (hβ a) (fun y hy => heβ y hy a)) hγ hxp hzp hdist).trans
    exact hsub _ (by dsimp [J]; linarith [Jg.coe_nonneg,Jf.coe_nonneg])
  have hbdm (a k : Fin n) : |coordinateDerivative k (β a) x-coordinateDerivative k (β a) z| ≤ ε := by
    apply (lipschitzOn_euclidean_holder_small
      (p.derivative_rep_lipschitz a k (hβ a) (fun y hy => heβ y hy a)) hγ hxp hzp hdist).trans
    exact hsub _ (by dsimp [J]; linarith [Jg.coe_nonneg,Jf.coe_nonneg])
  have hugm : |intrinsicDerivative d.coordinate_body_convex α j.1 p.index x-
      intrinsicDerivative d.coordinate_body_convex α j.1 p.index z| ≤ ε := by
    apply (lipschitzOn_euclidean_holder_small (hJg t ht j hs hp hMA p.index) hγ hx hz hdist).trans
    exact hsub _ (by dsimp [J]; linarith [Jg.coe_nonneg,Jf.coe_nonneg])
  have hfm : |(intrinsicHessian d.coordinate_body_convex α j.1 x).det-
      (intrinsicHessian d.coordinate_body_convex α j.1 z).det| ≤ ε := by
    rw [hMA x hx,hMA z hz]
    apply (lipschitzOn_euclidean_holder_small (hJf t ht) hγ hx hz hdist).trans
    exact hsub _ (by dsimp [J]; linarith [Jg.coe_nonneg,Jf.coe_nonneg])
  have hWm (a k : Fin n) : |intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index x (Pi.single k 1)-
      intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index z (Pi.single k 1)| ≤ ε :=
    (hWT a k).trans (mul_le_mul_of_nonneg_right (by linarith) hd₀)
  have hh := hrec (intrinsicHessian d.coordinate_body_convex α j.1 x) (intrinsicHessian d.coordinate_body_convex α j.1 z)
    (hp x hx) (hp z hz)
    (by rw [hMA x hx]; exact (hdens t ht x hx).1)
    (by rw [hMA z hz]; exact (hdens t ht z hz).1)
    (hHess t ht j hs hp hMA x hx) (hHess t ht j hs hp hMA z hz)
    (by rw [abs_of_pos (hp z hz).det_pos,hMA z hz]; exact (hdens t ht z hz).2)
    (fun a : TangentIndex p.index => β a x) (fun a : TangentIndex p.index => β a z)
    (fun a : TangentIndex p.index => fun k => coordinateDerivative k (β a) x)
    (fun a : TangentIndex p.index => fun k => coordinateDerivative k (β a) z)
    (fun a : TangentIndex p.index => fun k => intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index x (Pi.single k 1))
    (fun a : TangentIndex p.index => fun k => intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index z (Pi.single k 1))
    (intrinsicDerivative d.coordinate_body_convex α j.1 p.index x) (intrinsicDerivative d.coordinate_body_convex α j.1 p.index z)
    (fun a => hβ0 x hxp a) (fun a => hβ0 z hzp a) (fun a k => hβ1 x hxp a k) (fun a k => hβ1 z hzp a k)
    (hGval x hx) (hGval z hz) (fun a k => hWval x hxp hx a k) (fun a k => hWval z hzp hz a k)
    (fun a k => intrinsicTangentDifferential_apply_coordinate d.coordinate_body_convex α j.1 (β a) a p.index k x)
    (fun a k => intrinsicTangentDifferential_apply_coordinate d.coordinate_body_convex α j.1 (β a) a p.index k z)
    ε hε (fun a => hbm a) (fun a k => hbdm a k) hugm (fun a k => hWm a k) hfm i l
  apply hh.trans
  dsimp [ε]
  have hJL : J+L ≤ (J+1)*(1+L) := by nlinarith [mul_nonneg hJ hL]
  have hh' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hJL hd₀) hC₀
  simpa only [d₀,mul_assoc] using hh'

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
