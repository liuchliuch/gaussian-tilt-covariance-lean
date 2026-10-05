import GaussianTilt.MomentMapClassicalDirichletBoundaryClosure
import GaussianTilt.MomentMapClassicalDirichletMixedChartEstimate
import GaussianTilt.MomentMapClassicalDirichletNormalCoordinates
import GaussianTilt.MomentMapClassicalDirichletBoundaryTangentBounds

/-!
# Genuine full boundary Hessian estimates

Actual tangential jets, the differentiated mixed equation, and the literal
determinant in a determinant-preserving shear control every boundary Hessian
entry. No source Hessian bound or uniform ellipticity is a premise.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateTangentBlock_eq_adapted (u w : CoordinateSpace n → ℝ) (j : Fin n) (x : CoordinateSpace n) :
    coordinateTangentBlock (coordinateHessian u x) j (fun a => boundaryChartCoefficient w j a x) =
      adaptedTangentBlock u w j x := by
  ext a b
  exact (adaptedTangentBlock_entry_formula u w j x a b).symm

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- Uniform full boundary Hessian control on one of the constructed charts.
All constants come from the defining domain, fixed first-order/forcing
bounds, and the genuine scaled barriers. -/
theorem uniform_boundary_hessian_on_chart [NeZero n]
    (p : BoundaryChartPatch d.coordinateDefining) {a b G K D W : ℝ}
    (ha : 0 < a) (hG : 0 ≤ G) (hK : 0 ≤ K) (hD : 0 ≤ D) (hW : 0 ≤ W)
    (hWw : ∀ y ∈ {x | d.coordinateDefining x ≤ 0}, ∀ i,
      |coordinateDerivative i d.coordinateDefining y| ≤ W) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (u F : CoordinateSpace n → ℝ), ContDiff ℝ ∞ u →
      (∀ y ∈ interior {x | d.coordinateDefining x ≤ 0}, (coordinateHessian u y).PosDef) →
      (∀ y ∈ interior {x | d.coordinateDefining x ≤ 0}, (coordinateHessian u y).det = Real.exp (F y)) →
      (∀ y ∈ frontier {x | d.coordinateDefining x ≤ 0}, u y = 0) →
      (∀ y ∈ {x | d.coordinateDefining x ≤ 0}, b*d.coordinateDefining y ≤ u y ∧ u y ≤ a*d.coordinateDefining y) →
      (∀ y ∈ {x | d.coordinateDefining x ≤ 0}, ∀ i, |coordinateDerivative i u y| ≤ G) →
      (∀ y ∈ interior {x | d.coordinateDefining x ≤ 0}, ∀ i, |coordinateDerivative i F y| ≤ K) →
      (∀ y ∈ {x | d.coordinateDefining x ≤ 0}, (coordinateHessian u y).det ≤ D) →
      ∀ z ∈ frontier {x | d.coordinateDefining x ≤ 0}, z ∈ Metric.ball p.center (p.radius/2) →
        ∀ i j, |coordinateHessian u z i j| ≤ B := by
  obtain ⟨δ,I,T,hδ,hI,hT,hblock⟩ := d.actual_coordinate_tangent_block_bounds p (b := b) ha
  let M := ((((1+p.bound₀)*G)/(p.radius^2/8)+
    ((K+p.bound₀*K+2*p.bound₁)*max 1 D+G*(n:ℝ)^2*p.bound₂))/d.modulus)*W+p.bound₁*G
  let N := D/δ+(Fintype.card (TangentIndex p.index):ℝ)^2*I*M^2
  let B := (n:ℝ)*max N (T+2*p.bound₀*M+p.bound₀^2*N)
  have hM : 0 ≤ M := by
    have h0 := p.bound₀_nonneg
    have h1 := p.bound₁_nonneg
    have h2 := p.bound₂_nonneg
    have hκ := d.modulus_pos
    have hr := p.radius_pos
    have hmax : 0 ≤ max 1 D := zero_le_one.trans (le_max_left _ _)
    dsimp [M]
    positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) (hN.trans (le_max_left _ _))
  refine ⟨B,hB,?_⟩
  intro u F hu hH hMA hzero hbar hGu hKF hdet z hzb hz i j
  have hz0 := d.coordinate_zero_boundary z hzb
  have hzS := d.coordinate_body_compact.isClosed.frontier_subset hzb
  have hzchart : z ∈ Metric.closedBall p.center p.radius := by
    change dist z p.center ≤ p.radius
    exact hz.le.trans (by linarith [p.radius_pos])
  have hzero' : ∀ y, d.coordinateDefining y = 0 → u y = 0 := by
    intro y hy
    apply hzero y
    rwa [d.coordinate_body_frontier]
  have hmixed (l : Fin n) : |coordinateHessian u z l p.index -
      boundaryChartCoefficient d.coordinateDefining p.index l z * coordinateHessian u z p.index p.index| ≤ M :=
    p.mixed_hessian_estimate d.coordinateDefining_smooth d.coordinate_body_compact
      d.modulus_pos hG hK hW (fun y _ => d.coordinate_hessian_sub_modulus_posSemidef y)
      hu hH hMA hzero' hGu hKF (fun y hy => hdet y (interior_subset hy)) hWw hz0 hz l
  have ht := hblock u z hzchart hz0 (contDiff_infty.mp hu 2).contDiffAt hzero hbar
  rw [← coordinateTangentBlock_eq_adapted] at ht
  have hps := d.coordinate_hessian_posSemidef_on_body hu hH z hzS
  have hsym := coordinateHessian_isSymm_at (contDiff_infty.mp hu 2).contDiffAt (x := z)
  have hn : coordinateHessian u z p.index p.index ≤ N :=
    coordinate_normal_hessian_bound hsym p.index
      (fun l => boundaryChartCoefficient d.coordinateDefining p.index l z)
      ht.1 hδ hI.le hM hD ht.2.1 ht.2.2.1 (fun l => hmixed l) (hdet z hzS)
  exact coordinate_hessian_entries_bound_of_adapted_bounds hps p.index
    (fun l => boundaryChartCoefficient d.coordinateDefining p.index l z)
    p.bound₀_nonneg hM hN (fun l => ht.2.2.2 l l)
    (fun l => p.value_bound z hzchart l) (fun l => hmixed l) hn i j

/-- The full boundary Hessian bound is uniform over the actual forcing
homotopy. Neither the mixed estimate, tangent bounds, first-order control,
finite atlas nor determinant equation is supplied as a missing theorem. -/
theorem dirichletContinuation_uniform_boundary_hessian [NeZero n] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ u : CoordinateSpace n → ℝ,
      ContDiff ℝ ∞ u →
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0}, (coordinateHessian u x).PosDef) →
      (∀ x ∈ frontier {y | d.coordinateDefining y ≤ 0}, u x = 0) →
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
        (coordinateHessian u x).det = dirichletContinuationDensity d.coordinateDefining t x) →
      ∀ x ∈ frontier {y | d.coordinateDefining y ≤ 0}, ∀ i j, |coordinateHessian u x i j| ≤ B := by
  classical
  obtain ⟨a,b,ha,hb,hbar⟩ := dirichletContinuation_scaled_barriers d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth
    (fun x _ => d.coordinateDefining_hessian_posDef x) d.coordinate_zero_boundary
  obtain ⟨G,hG,hGu⟩ := d.dirichletContinuation_uniform_coordinate_gradient
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K,hK,hKF⟩ := dirichletContinuationDensity_uniform_log_coordinateDerivative d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨W,hW,hwW,hDw⟩ := d.coordinate_defining_first_bounds
  have hp := fun p : BoundaryChartPatch d.coordinateDefining =>
    d.uniform_boundary_hessian_on_chart p (b := b) ha hG hK hD.le hW hDw
  choose B hB hbound using hp
  obtain ⟨P,hcover⟩ := d.exists_finite_coordinate_boundary_atlas
  refine ⟨∑ p ∈ P, B p, Finset.sum_nonneg (fun p _ => hB p), ?_⟩
  intro t ht u hu hH hub hMA x hx i j
  obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hcover hx)
  have hMAlog : ∀ y ∈ interior {z | d.coordinateDefining z ≤ 0},
      (coordinateHessian u y).det = Real.exp (Real.log (dirichletContinuationDensity d.coordinateDefining t y)) := by
    intro y hy
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
    exact hMA y hy
  have hbar' := hbar t ht u hu.continuous.continuousOn
    (fun _ _ => (contDiff_infty.mp hu 2).contDiffAt) hH hub hMA
  have hdet : ∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (coordinateHessian u y).det ≤ D := by
    intro y hy
    rw [d.coordinate_equation_on_body hu hMA y hy]
    exact (hdens t ht y hy).2
  have hlocal := hbound p u (fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y))
    hu hH hMAlog hub hbar' (hGu t ht u hu hH hub hMA)
    (fun y hy => hKF t ht y (interior_subset hy)) hdet x hx hxp i j
  exact hlocal.trans (Finset.single_le_sum (fun p _ => hB p) hp)

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
