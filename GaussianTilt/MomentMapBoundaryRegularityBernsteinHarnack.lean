import GaussianTilt.MomentMapBoundaryRegularityBernsteinBall
import GaussianTilt.MomentMapClassicalDirichletSolutionCompactness

/-! # A noncircular logarithmic gradient estimate on interior balls -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff NNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The constant precedes all functions and coefficients. Thus a fixed
rescaled coefficient derivative bound supplies a uniform log-gradient
bound, independent of the oscillation of the positive solution. -/
theorem exists_bernstein_ball_gradient_bound {lam Λ K G R : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) (hG : 0 ≤ G) (hR : 0 < R) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (φ h : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (c : CoordinateSpace n),
      ContDiff ℝ ∞ φ → (∀ i j, Differentiable ℝ (fun y => A y i j)) →
      (∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R → (A y).PosSemidef) →
      (∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
        ∀ v : CoordinateSpace n, lam * ‖(coordinateEquiv n).symm v‖^2 ≤ v ⬝ᵥ (A y *ᵥ v) ∧
          v ⬝ᵥ (A y *ᵥ v) ≤ Λ * ‖(coordinateEquiv n).symm v‖^2) →
      (∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
        ∀ k i j, |matrixCoordinateDerivative A k y i j| ≤ K) →
      (∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R → |h y| ≤ G) →
      (∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
        ∀ k, |coordinateDerivative k h y| ≤ G*(1+|coordinateDerivative k φ y|)) →
      (∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
        linearizedMA (A y) φ y + coordinateGradient φ y ⬝ᵥ (A y *ᵥ coordinateGradient φ y) = h y) →
      gradientSquare φ c ≤ B := by
  obtain ⟨κ, C, hκ, hC, hineq⟩ := exists_bernstein_log_gradient_inequality (n := n) hlam hΛ hK hG
  refine ⟨max (bernsteinBallBound n Λ κ C R) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro φ h A c hφ hAd hA hEll hDA hh hDh hP
  apply le_trans ?_ (le_max_left _ _)
  apply bernstein_ball_center_bound (contDiff_infty.mp (contDiff_gradientSquare hφ) 2)
    (coordinateGradient φ) c hR hκ hΛ hC hA (fun y hy v => (hEll y hy v).2)
    (fun _ _ => le_rfl)
  intro y hy
  have hsym : (A y).IsSymm := by
    simpa only [Matrix.IsSymm, Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using (hA y hy).isHermitian
  have hdiag (i : Fin n) : A y i i ≤ Λ := by
    have ht := (hEll y hy (Pi.single i 1)).2
    simpa [Matrix.mulVec_single_one, single_dotProduct, Matrix.col, coordinateEquiv,
      EuclideanSpace.norm_eq, PiLp.norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq] using ht
  have hnear : ∀ᶠ z in 𝓝 y, linearizedMA (A z) φ z +
      coordinateGradient φ z ⬝ᵥ (A z *ᵥ coordinateGradient φ z) = h z := by
    have ho : IsOpen {z : CoordinateSpace n | ‖(coordinateEquiv n).symm z - (coordinateEquiv n).symm c‖ < R} :=
      isOpen_lt (((coordinateEquiv n).symm.continuous.sub continuous_const).norm) continuous_const
    filter_upwards [ho.mem_nhds hy] with z hz
    exact hP z hz
  exact hineq φ h A hφ hAd y hsym
    (fun v => by rw [coordinate_square_sum_eq_norm]; exact (hEll y hy v).1)
    (abs_entry_le_of_posSemidef_diagonal_bound (hA y hy) hdiag) (hDA y hy) (hh y hy) (hDh y hy) hnear

/-- Squared gradient control gives an actual coordinate derivative bound. -/
lemma abs_coordinateDerivative_le_sqrt_gradient_bound {φ : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} {B : ℝ} (hB : 0 ≤ B) (hφ : gradientSquare φ x ≤ B) (i : Fin n) :
    |coordinateDerivative i φ x| ≤ Real.sqrt B := by
  have ht : (coordinateDerivative i φ x)^2 ≤ B :=
    (Finset.single_le_sum (fun k _ => sq_nonneg (coordinateDerivative k φ x)) (Finset.mem_univ i)).trans hφ
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg B)).mp
  rwa [sq_abs, Real.sq_sqrt hB]

lemma lipschitzOn_of_gradientSquare_bound {φ : CoordinateSpace n → ℝ}
    (hφ : Differentiable ℝ φ) {S : Set (CoordinateSpace n)} (hS : Convex ℝ S)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x ∈ S, gradientSquare φ x ≤ B) :
    LipschitzOnWith ⟨(n:ℝ)*Real.sqrt B, by positivity⟩ φ S := by
  apply hS.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hφ x)
  intro x hx
  exact_mod_cast norm_fderiv_le_of_coordinate_bound (Real.sqrt_nonneg B)
    (abs_coordinateDerivative_le_sqrt_gradient_bound hB (hb x hx))

/-- A uniform log-gradient oscillation bound on the half-ball, obtained
from the actual PDE and coefficient derivatives on the unit ball. -/
theorem exists_bernstein_unit_ball_oscillation {lam Λ K G : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) (hG : 0 ≤ G) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (φ h : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ∞ φ → (∀ i j, Differentiable ℝ (fun y => A y i j)) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → (A y).PosSemidef) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → ∀ v : CoordinateSpace n,
        lam * ‖(coordinateEquiv n).symm v‖^2 ≤ v ⬝ᵥ (A y *ᵥ v) ∧
        v ⬝ᵥ (A y *ᵥ v) ≤ Λ * ‖(coordinateEquiv n).symm v‖^2) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 →
        ∀ k i j, |matrixCoordinateDerivative A k y i j| ≤ K) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → |h y| ≤ G) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 →
        ∀ k, |coordinateDerivative k h y| ≤ G*(1+|coordinateDerivative k φ y|)) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → linearizedMA (A y) φ y +
        coordinateGradient φ y ⬝ᵥ (A y *ᵥ coordinateGradient φ y) = h y) →
      ∀ x y, ‖(coordinateEquiv n).symm x‖ ≤ 1/2 → ‖(coordinateEquiv n).symm y‖ ≤ 1/2 →
        |φ x - φ y| ≤ L * ‖x-y‖ := by
  obtain ⟨B, hB, hgrad⟩ := exists_bernstein_ball_gradient_bound (n := n) hlam hΛ hK hG
    (show 0 < (1/2:ℝ) by norm_num)
  refine ⟨(n:ℝ)*Real.sqrt B+1, by positivity, ?_⟩
  intro φ h A hφ hAd hA hEll hDA hh hDh hP
  let e := coordinateEquiv n
  let S := e '' Metric.closedBall (0 : E n) (1/2)
  have hb : ∀ z ∈ S, gradientSquare φ z ≤ B := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hwn : ‖w‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    have hnear (y : CoordinateSpace n) (hy : ‖e.symm y-e.symm (e w)‖ < 1/2) : ‖e.symm y‖ < 1 := by
      rw [e.symm_apply_apply] at hy
      have ht := norm_add_le (e.symm y-w) w
      rw [sub_add_cancel] at ht
      linarith
    exact hgrad φ h A (e w) hφ hAd
      (fun y hy => hA y (hnear y hy)) (fun y hy => hEll y (hnear y hy))
      (fun y hy => hDA y (hnear y hy)) (fun y hy => hh y (hnear y hy))
      (fun y hy => hDh y (hnear y hy)) (fun y hy => hP y (hnear y hy))
  have hSc : Convex ℝ S := (convex_closedBall (0:E n) (1/2)).linear_image e.toLinearMap
  have hl := lipschitzOn_of_gradientSquare_bound (hφ.differentiable (by simp)) hSc hB.le hb
  intro x y hx hy
  have hxs : x ∈ S := ⟨e.symm x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx, e.apply_symm_apply x⟩
  have hys : y ∈ S := ⟨e.symm y, by simpa only [Metric.mem_closedBall, dist_zero_right] using hy, e.apply_symm_apply y⟩
  have he := hl.dist_le_mul x hxs y hys
  simp only [Real.dist_eq, dist_eq_norm, NNReal.coe_mk] at he
  exact he.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

end GaussianTilt.MomentMapRegularity
