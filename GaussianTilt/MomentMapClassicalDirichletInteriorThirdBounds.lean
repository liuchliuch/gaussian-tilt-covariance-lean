import GaussianTilt.MomentMapClassicalDirichletInteriorCompactness
import GaussianTilt.MomentMapClassicalDirichletForcingThird

/-! # Genuine local third-derivative bounds for the classical homotopy -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinate_dist_le_euclidean_dist (x y : CoordinateSpace n) :
    dist x y ≤ ‖(coordinateEquiv n).symm x-(coordinateEquiv n).symm y‖ := by
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le ((coordinateEquiv n).symm x-(coordinateEquiv n).symm y) i

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- Every interior point has a genuine fixed compact ball on which all
smooth homotopy solutions have uniformly bounded true third derivatives. -/
theorem dirichletContinuation_local_uniform_third_bound [NeZero n]
    {x : CoordinateSpace n} (hx : x ∈ interior {y | d.coordinateDefining y ≤ 0}) :
    ∃ r T : ℝ, 0 < r ∧ 0 ≤ T ∧
      Metric.closedBall x r ⊆ interior {y | d.coordinateDefining y ≤ 0} ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ u : CoordinateSpace n → ℝ,
        ContDiff ℝ ∞ u →
        (∀ y ∈ interior {z | d.coordinateDefining z ≤ 0}, (coordinateHessian u y).PosDef) →
        (∀ y ∈ frontier {z | d.coordinateDefining z ≤ 0}, u y = 0) →
        (∀ y ∈ interior {z | d.coordinateDefining z ≤ 0},
          (coordinateHessian u y).det = dirichletContinuationDensity d.coordinateDefining t y) →
        ∀ y ∈ Metric.closedBall x r, ∀ i j k, |coordinateThirdDerivative u y i j k| ≤ T := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
  let r := δ/4
  have hr : 0 < r := div_pos hδ (by norm_num)
  have hins : Metric.closedBall x r ⊆ interior {y | d.coordinateDefining y ≤ 0} := by
    intro y hy
    apply hball
    change dist y x < δ
    change dist y x ≤ r at hy
    dsimp [r] at hy
    linarith
  obtain ⟨K,hK,hKH⟩ := d.dirichletContinuation_uniform_hessian
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K₂,hK₂,hF₂⟩ := dirichletContinuationDensity_uniform_log_hessian d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K₃,hK₃,hF₃⟩ := dirichletContinuationDensity_uniform_log_thirdDerivatives d.coordinate_body_compact
    d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  let K₀ := max (-Real.log c) 0
  let T := variableThirdDerivativeBound n K K₀ K₂ K₃ r
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  refine ⟨r,T,hr,hT,hins,?_⟩
  intro t ht u hu hH hub hMA y hy i j k
  have hyball (z : CoordinateSpace n)
      (hz : ‖(coordinateEquiv n).symm z-(coordinateEquiv n).symm y‖ < r) :
      z ∈ interior {q | d.coordinateDefining q ≤ 0} := by
    apply hball
    change dist z x < δ
    have hzy := (coordinate_dist_le_euclidean_dist z y).trans_lt hz
    have ht' := dist_triangle z y x
    change dist y x ≤ r at hy
    dsimp [r] at hy hzy
    linarith
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.log _ (fun y => (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y)).ne')
    exact (contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp
      (contDiff_const.prodMk contDiff_id)
  apply variable_thirdDerivative_bound_on_ball_of_hessian_bound (Nat.pos_of_ne_zero (NeZero.ne n))
    hu hF y hr hK₂ hK₃
    (fun z hz => hH z (hyball z hz))
    (fun z hz => ?_)
    (fun z hz => hKH t ht u hu hH hub hMA z (interior_subset (hyball z hz)))
    (fun z hz => ?_)
    (fun z hz => hF₂ t ht z (interior_subset (hyball z hz)))
    (fun z hz => hF₃ t ht z (interior_subset (hyball z hz))) i j k
  · dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef z))]
    exact hMA z (hyball z hz)
  · have hl := Real.log_le_log hc (hdens t ht z (interior_subset (hyball z hz))).1
    have hk : -K₀ ≤ Real.log c := by dsimp [K₀]; linarith [le_max_left (-Real.log c) 0]
    exact hk.trans hl

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
