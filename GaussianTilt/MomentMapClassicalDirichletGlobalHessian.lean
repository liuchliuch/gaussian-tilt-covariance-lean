import GaussianTilt.MomentMapClassicalDirichletBoundaryHessian
import GaussianTilt.MomentMapClassicalDirichletContinuationForcingHessian

/-!
# Actual global second-order bounds along the classical homotopy

The boundary Hessian estimate propagates through the domain using the true
differentiated equation and positivity of the inverse-weighted trace square.
This gives a global bound without assuming uniform source ellipticity.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma linearizedMA_hessian_diagonal_lower {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) {x : CoordinateSpace n}
    (hH : (coordinateHessian u x).PosDef)
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y)) (i : Fin n) :
    coordinateHessian F x i i ≤ linearizedMA (coordinateHessian u x)⁻¹
      (fun y => coordinateHessian u y i i) x := by
  rw [variable_density_second_trace hu hF hMA]
  have h := weightedTrace_square_nonneg (coordinateHessian u x)⁻¹
    (matrixCoordinateDerivative (coordinateHessian u) i x) hH.inv.posSemidef
    (matrixCoordinateDerivative_hessian_isSymm (contDiff_infty.mp hu 2) i x)
  linarith

/-- A genuine defining-function barrier propagates the boundary diagonal
Hessian bounds, using the actual variable-RHS trace identity. -/
theorem coordinate_hessian_diagonal_bound_from_boundary [NeZero n]
    {w u F : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F)
    (hS : IsCompact {y | w y ≤ 0})
    {κ K D B : ℝ} (hκ : 0 < κ) (hK : 0 ≤ K)
    (hHw : ∀ y ∈ {x | w x ≤ 0},
      (coordinateHessian w y - κ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hH : ∀ y ∈ interior {x | w x ≤ 0}, (coordinateHessian u y).PosDef)
    (hMA : ∀ y ∈ interior {x | w x ≤ 0}, (coordinateHessian u y).det = Real.exp (F y))
    (hKF : ∀ y ∈ interior {x | w x ≤ 0}, ∀ i, -K ≤ coordinateHessian F y i i)
    (hD : ∀ y ∈ interior {x | w x ≤ 0}, (coordinateHessian u y).det ≤ D)
    (hb : ∀ y ∈ frontier {x | w x ≤ 0}, ∀ i, coordinateHessian u y i i ≤ B) :
    ∀ x ∈ {y | w y ≤ 0}, ∀ i,
      coordinateHessian u x i i ≤ B - (K*max 1 D/κ)*w x := by
  let C := K*max 1 D/κ
  have hmax : 0 ≤ max 1 D := zero_le_one.trans (le_max_left _ _)
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hK hmax) hκ.le
  have hCκ : C*κ = K*max 1 D := div_mul_cancel₀ _ hκ.ne'
  intro x hx i
  have hHii : ContDiff ℝ 2 (fun y => coordinateHessian u y i i) :=
    contDiff_infty.mp (smooth_coordinateHessian hu i i) 2
  have hw2 : ContDiff ℝ 2 w := contDiff_infty.mp hw 2
  have hbound : coordinateHessian u x i i - B + C*w x ≤ 0 := by
    apply classical_dirichlet_maximum_principle hS
      ((hHii.continuous.sub continuous_const).add (continuous_const.mul hw.continuous)).continuousOn
      (fun y _ => (hHii.contDiffAt.sub contDiffAt_const).add (contDiffAt_const.mul hw2.contDiffAt))
      (fun y hy => (hH y hy).inv) ?_ ?_ x hx
    · intro y hy
      have hnear : ∀ᶠ z in 𝓝 y, (coordinateHessian u z).det = Real.exp (F z) := by
        filter_upwards [isOpen_interior.mem_nhds hy] with z hz
        exact hMA z hz
      rw [linearizedMA_add_at _ (hHii.contDiffAt.sub contDiffAt_const)
        (contDiffAt_const.mul hw2.contDiffAt),
        linearizedMA_sub_at _ hHii.contDiffAt contDiffAt_const,
        linearizedMA_const,linearizedMA_const_mul_at _ hw2.contDiffAt]
      have hlow := linearizedMA_hessian_diagonal_lower hu hF (hH y hy) hnear i
      have hforce := hKF y hy i
      have hwlow := linearizedMA_lower_of_hessian_lower (hH y hy).inv.posSemidef (hHw y (interior_subset hy))
      have htrace := trace_inverse_lower_of_det_upper (hH y hy) (hD y hy)
      have h1 := mul_le_mul_of_nonneg_left hwlow hC
      have h2 := mul_le_mul_of_nonneg_left htrace hK
      have he := congrArg (fun z => z*(coordinateHessian u y)⁻¹.trace) hCκ
      nlinarith
    · intro y hy
      have hw0 : w y = 0 := frontier_le_subset_eq hw.continuous continuous_const hy
      simpa [hw0] using sub_nonpos.mpr (hb y hy i)
  dsimp only [C] at hbound
  linarith

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- Global, parameter-uniform actual Hessian entry bounds. This is an a
priori estimate for smooth solutions, with no source Hessian upper bound or
uniform ellipticity in its hypotheses. -/
theorem dirichletContinuation_uniform_hessian [NeZero n] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ u : CoordinateSpace n → ℝ,
      ContDiff ℝ ∞ u →
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0}, (coordinateHessian u x).PosDef) →
      (∀ x ∈ frontier {y | d.coordinateDefining y ≤ 0}, u x = 0) →
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
        (coordinateHessian u x).det = dirichletContinuationDensity d.coordinateDefining t x) →
      ∀ x ∈ {y | d.coordinateDefining y ≤ 0}, ∀ i j, |coordinateHessian u x i j| ≤ B := by
  obtain ⟨B₀,hB₀,hboundary⟩ := d.dirichletContinuation_uniform_boundary_hessian
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K,hK,hKF⟩ := dirichletContinuationDensity_uniform_log_hessian d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨W,hW,hwW,hDw⟩ := d.coordinate_defining_first_bounds
  let C := K*max 1 D/d.modulus
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hK (zero_le_one.trans (le_max_left _ _))) d.modulus_pos.le
  refine ⟨(n:ℝ)*(B₀+C*W),mul_nonneg (Nat.cast_nonneg _) (add_nonneg hB₀ (mul_nonneg hC hW)),?_⟩
  intro t ht u hu hH hub hMA x hx i j
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.log _ (fun y => (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y)).ne')
    exact (contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp
      (contDiff_const.prodMk contDiff_id)
  have hMAlog : ∀ y ∈ interior {z | d.coordinateDefining z ≤ 0},
      (coordinateHessian u y).det = Real.exp (F y) := by
    intro y hy
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
    exact hMA y hy
  have hdiag (l : Fin n) : coordinateHessian u x l l ≤ B₀+C*W := by
    have h := coordinate_hessian_diagonal_bound_from_boundary d.coordinateDefining_smooth hu hF
      d.coordinate_body_compact d.modulus_pos hK
      (fun y _ => d.coordinate_hessian_sub_modulus_posSemidef y) hH hMAlog
      (fun y hy l => (abs_le.mp (hKF t ht y (interior_subset hy) l l)).1)
      (fun y hy => (hMA y hy).trans_le (hdens t ht y (interior_subset hy)).2)
      (fun y hy l => (le_abs_self _).trans (hboundary t ht u hu hH hub hMA y hy l l)) x hx l
    have hval := hwW x hx
    dsimp only [C] at *
    nlinarith [neg_abs_le (d.coordinateDefining x)]
  have hps := d.coordinate_hessian_posSemidef_on_body hu hH x hx
  apply (abs_matrix_entry_le_trace hps i j).trans
  calc
    (coordinateHessian u x).trace ≤ ∑ _l : Fin n, (B₀+C*W) := Finset.sum_le_sum (fun l _ => hdiag l)
    _ = _ := by simp; ring

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
