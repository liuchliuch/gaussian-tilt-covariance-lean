import GaussianTilt.MomentMapClassicalDirichletIntrinsicInterior
import GaussianTilt.MomentMapClassicalDirichletOperatorBounds
import GaussianTilt.MomentMapClassicalDirichletContinuationFirstOrder

/-! # Actual first-order estimates for intrinsic Dirichlet Hölder jets -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- The real comparison barriers already apply directly to the true
intrinsic jet function: C² is needed only in the interior. -/
theorem intrinsic_dirichletContinuation_scaled_barriers [NeZero n] {α : ℝ} (hα : 0 < α) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
        (intrinsicHessian d.coordinate_body_convex α j.1 x).PosDef) →
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
        (intrinsicHessian d.coordinate_body_convex α j.1 x).det = dirichletContinuationDensity d.coordinateDefining t x) →
      ∀ x ∈ {y | d.coordinateDefining y ≤ 0},
        b*d.coordinateDefining x ≤ intrinsicValue d.coordinate_body_convex α j.1 x ∧
        intrinsicValue d.coordinate_body_convex α j.1 x ≤ a*d.coordinateDefining x := by
  obtain ⟨a,b,ha,hb,hbar⟩ := dirichletContinuation_scaled_barriers d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth
    (fun x _ => d.coordinateDefining_hessian_posDef x) d.coordinate_zero_boundary
  refine ⟨a,b,ha,hb,?_⟩
  intro t ht j hp hMA
  apply hbar t ht (intrinsicValue d.coordinate_body_convex α j.1)
    (continuousOn_extendValue α _) (fun x hx =>
      (jet_contDiffOn_two d.coordinate_body_convex hα j.1).contDiffAt (isOpen_interior.mem_nhds hx))
  · intro x hx
    rw [← intrinsicHessian_eq_actual d.coordinate_body_convex hα j.1 hx]
    exact hp x hx
  · exact fun x hx => zeroBoundary_value d.coordinate_body_convex d.coordinate_body_compact.isClosed α j hx
  · intro x hx
    rw [← intrinsicHessian_eq_actual d.coordinate_body_convex hα j.1 hx]
    exact hMA x hx

/-- The parameter-uniform first derivative bound now applies to actual
Hölder jets smooth only inside the domain. Boundary derivatives are their
intrinsic within-domain fields, never derivatives of the zero extension. -/
theorem intrinsic_dirichletContinuation_uniform_first [NeZero n] {α : ℝ} (hα : 0 < α) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
        (intrinsicHessian d.coordinate_body_convex α j.1 x).PosDef) →
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
        (intrinsicHessian d.coordinate_body_convex α j.1 x).det = dirichletContinuationDensity d.coordinateDefining t x) →
      ∀ x ∈ {y | d.coordinateDefining y ≤ 0}, ∀ i,
        |intrinsicDerivative d.coordinate_body_convex α j.1 i x| ≤ G := by
  obtain ⟨a,b,ha,hb,hbar⟩ := d.intrinsic_dirichletContinuation_scaled_barriers hα
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K,hK,hKF⟩ := dirichletContinuationDensity_uniform_log_coordinateDerivative d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨W,hW,hwW,hDw⟩ := d.coordinate_defining_first_bounds
  let c₀ := d.modulus/max 1 D
  have hmax : 0 < max 1 D := zero_lt_one.trans_le (le_max_left _ _)
  have hc₀ : 0 < c₀ := div_pos d.modulus_pos hmax
  let C := K/c₀
  have hC : 0 ≤ C := div_nonneg hK hc₀.le
  refine ⟨b*W+C*W,add_nonneg (mul_nonneg hb.le hW) (mul_nonneg hC hW),?_⟩
  intro t ht j hs hp hMA x hx i
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  have hMAlog (y : CoordinateSpace n) (hy : y ∈ interior {z | d.coordinateDefining z ≤ 0}) :
      (intrinsicHessian d.coordinate_body_convex α j.1 y).det = Real.exp (F y) := by
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
    exact hMA y hy
  have hbd (y : CoordinateSpace n) (hy : y ∈ frontier {z | d.coordinateDefining z ≤ 0}) :
      |intrinsicDerivative d.coordinate_body_convex α j.1 i y| ≤ b*W := by
    obtain ⟨lam,hlamA,hlamB,hfirst,hsecond⟩ := d.intrinsic_boundary_jet_data hα j hy (hbar t ht j hp hMA)
    have hfirsti := congrArg (fun L : CoordinateSpace n →L[ℝ] ℝ => L (Pi.single i 1)) hfirst
    change intrinsicDerivative d.coordinate_body_convex α j.1 i y = lam*coordinateDerivative i d.coordinateDefining y at hfirsti
    rw [hfirsti,abs_mul,abs_of_nonneg (ha.le.trans hlamA)]
    exact mul_le_mul hlamB (hDw y (d.coordinate_body_compact.isClosed.frontier_subset hy) i) (abs_nonneg _) hb.le
  have hLb (y : CoordinateSpace n) (hy : y ∈ interior {z | d.coordinateDefining z ≤ 0}) :
      c₀ ≤ linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 y)⁻¹ d.coordinateDefining y := by
    have hdet : (intrinsicHessian d.coordinate_body_convex α j.1 y).det ≤ D := by
      rw [hMA y hy]
      exact (hdens t ht y (interior_subset hy)).2
    have htr := trace_inverse_lower_of_det_upper (hp y hy) hdet
    have hlo : 1/max 1 D ≤ (intrinsicHessian d.coordinate_body_convex α j.1 y)⁻¹.trace :=
      (div_le_iff₀ hmax).mpr (by simpa only [mul_comm] using htr)
    have hh := (mul_le_mul_of_nonneg_left hlo d.modulus_pos.le).trans
      (linearizedMA_lower_of_hessian_lower (hp y hy).inv.posSemidef (d.coordinate_hessian_sub_modulus_posSemidef y))
    simpa only [c₀,mul_one_div] using hh
  have hfield := classical_dirichlet_abs_bound_with_barrier d.coordinate_body_compact
    (continuousOn_intrinsicDerivative d.coordinate_body_convex α j.1 i) d.coordinateDefining_smooth.continuous.continuousOn
    (fun y hy => contDiffAt_infty.mp (contDiffAt_intrinsicDerivative d.coordinate_body_convex hα j.1 hs hy i) 2)
    (fun _ _ => (contDiff_infty.mp d.coordinateDefining_smooth 2).contDiffAt)
    (fun y hy => (hp y hy).inv) hK hc₀
    (fun y hy => by
      rw [intrinsic_linearized_first_identity d.coordinate_body_convex hα j.1 hs hMAlog hy]
      exact hKF t ht y (interior_subset hy) i)
    hLb hbd (fun y hy => (d.coordinate_zero_boundary y hy).le) x hx
  have hv := hwW x hx
  dsimp only [C] at *
  nlinarith [neg_abs_le (d.coordinateDefining x)]

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
