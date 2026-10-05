import GaussianTilt.MomentMapBoundaryRegularityWithinGradientHolder

/-! # Deriving the boundary linear bound from actual first-order jets -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma convex_flatClosedHalfBall (j : Fin n) : Convex ℝ (flatClosedHalfBall j) := by
  intro x hx y hy a b ha hb hab
  constructor
  · have ht := norm_add_le (a • (coordinateEquiv n).symm x) (b • (coordinateEquiv n).symm y)
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb] at ht
    change ‖(coordinateEquiv n).symm (a • x+b • y)‖ ≤ 1
    rw [map_add,map_smul,map_smul]
    nlinarith [mul_le_mul_of_nonneg_left hx.1 ha,mul_le_mul_of_nonneg_left hy.1 hb]
  · change 0 ≤ a*x j+b*y j
    exact add_nonneg (mul_nonneg ha hx.2) (mul_nonneg hb hy.2)

lemma flat_projection_norm_le (x : CoordinateSpace n) (j : Fin n) :
    ‖(coordinateEquiv n).symm (x-x j • (Pi.single j 1 : CoordinateSpace n))‖ ≤
      ‖(coordinateEquiv n).symm x‖ := by
  have hterm (i : Fin n) : ((x-x j • (Pi.single j 1 : CoordinateSpace n)) i)^2 ≤ (x i)^2 := by
    by_cases hi : i=j
    · subst i
      simp
      positivity
    · simp [Pi.single_apply,hi,Ne.symm hi]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  rw [coordinate_square_sum_eq_norm,coordinate_square_sum_eq_norm] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

theorem flat_linear_bound_of_within_derivative_bound {j : Fin n}
    {u : CoordinateSpace n → ℝ} {D : CoordinateSpace n → CoordinateSpace n →L[ℝ] ℝ}
    {B : ℝ}
    (hD : ∀ y ∈ flatClosedHalfBall j, HasFDerivWithinAt u (D y) (flatClosedHalfBall j) y)
    (hB : ∀ y ∈ flatClosedHalfBall j, ‖D y‖ ≤ B)
    (hzero : ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → y j=0 → u y=0) :
    ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |u x| ≤ B*x j := by
  intro x hx hxj
  let z := x-x j • (Pi.single j 1 : CoordinateSpace n)
  have hzj : z j=0 := by simp [z]
  have hzn : ‖(coordinateEquiv n).symm z‖ ≤ 1 := (flat_projection_norm_le x j).trans hx
  have hz : z ∈ flatClosedHalfBall j := ⟨hzn,by rw [hzj]⟩
  have hxx : x ∈ flatClosedHalfBall j := ⟨hx,hxj⟩
  have hm := (convex_flatClosedHalfBall j).norm_image_sub_le_of_norm_hasFDerivWithin_le hD hB hz hxx
  have hd : ‖x-z‖=x j := by
    dsimp only [z]
    rw [sub_sub_cancel,norm_smul,Pi.norm_single]
    simp only [Real.norm_eq_abs,abs_of_nonneg hxj,norm_one,mul_one]
  rw [hzero z hzn hzj,sub_zero,Real.norm_eq_abs,hd] at hm
  exact hm

/-- Final intrinsic flat-boundary gradient estimate. Its boundary linear
growth is a derived consequence of the actual first-order jet and zero
boundary values, not an additional estimate assumption. -/
theorem exists_local_flat_gradient_holder_of_zero_boundary [NeZero n] {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ (j : Fin n) (u f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (D : CoordinateSpace n → CoordinateSpace n →L[ℝ] ℝ) (M B : ℝ),
      0 ≤ M → 0 ≤ B → LocalFlatEllipticSystem j u f A lam Λ K M →
      ContinuousOn D (flatClosedHalfBall j) →
      (∀ y ∈ flatClosedHalfBall j, HasFDerivWithinAt u (D y) (flatClosedHalfBall j) y) →
      (∀ y ∈ flatClosedHalfBall j, ‖D y‖ ≤ B) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → y j=0 → u y=0) →
      ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1/8 → 0 ≤ x j →
      ∀ i, |D x (Pi.single i 1)-D 0 (Pi.single i 1)| ≤
        C*(B+M)*‖(coordinateEquiv n).symm x‖^α := by
  obtain ⟨α,C,hα,hα1,hC,hest⟩ := exists_local_flat_gradient_holder (n := n) hlam hΛ hK
  refine ⟨α,C,hα,hα1,hC,?_⟩
  intro j u f A D M B hM hB hs hDc hD hDb hzero
  exact hest j u f A D M B hM hB hs hDc hD
    (flat_linear_bound_of_within_derivative_bound hD hDb hzero)

end GaussianTilt.MomentMapRegularity
