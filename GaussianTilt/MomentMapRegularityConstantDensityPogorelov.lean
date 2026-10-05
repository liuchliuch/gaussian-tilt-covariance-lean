import GaussianTilt.MomentMapRegularityConstantDensityEquation

/-!
# The genuine local Pogorelov maximum inequality

The third-derivative contraction, the actual differentiated determinant
identity, and stationarity of the logarithmic test combine to bound the
weighted directional Hessian at its interior maximum.
-/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma pogorelov_stationarity_cancellation (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (i : Fin n) (v g b : Fin n → ℝ) {w z : ℝ}
    (hw : w ≠ 0) (hz : z ≠ 0) (hAv : A *ᵥ v = Pi.single i 1) (hvi : v i = w)
    (hstat : w⁻¹ • b + z⁻¹ • g + g i • v = 0) :
    (b ⬝ᵥ (A *ᵥ b)) / w ^ 2 - (b i)^2 / w^3 -
      (g ⬝ᵥ (A *ᵥ g)) / z^2 = -(g i)^2 / (z^2 * w) := by
  have hb : w⁻¹ • b = -(z⁻¹ • g + g i • v) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_assoc] using hstat
  have hgv : g ⬝ᵥ (A *ᵥ v) = g i := by rw [hAv, dotProduct_single, mul_one]
  have hvg : v ⬝ᵥ (A *ᵥ g) = g i := by
    rw [symmetric_dot_mulVec A hA, hAv, single_dotProduct, one_mul]
  have hvv : v ⬝ᵥ (A *ᵥ v) = w := by rw [hAv, dotProduct_single, mul_one, hvi]
  have hquad := congrArg (fun q => q ⬝ᵥ (A *ᵥ q)) hb
  dsimp only at hquad
  simp only [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg,
    Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, hgv, hvg, hvv] at hquad
  have hq : (b ⬝ᵥ (A *ᵥ b)) / w ^ 2 =
      (g ⬝ᵥ (A *ᵥ g)) / z^2 + 2 * (g i)^2 / z + (g i)^2 * w := by
    convert hquad using 1 <;> ring
  have hi := congrFun hb i
  simp only [Pi.smul_apply, Pi.neg_apply, Pi.add_apply, smul_eq_mul, hvi] at hi
  have ht : b i / w = -(g i / z + g i * w) := by
    convert hi using 1 <;> ring
  have ht2 : (b i)^2 / w^3 = (g i)^2 / (z^2 * w) + 2 * (g i)^2 / z + (g i)^2 * w := by
    calc
      (b i)^2 / w^3 = (b i / w)^2 / w := by field_simp <;> ring
      _ = (-(g i / z + g i * w))^2 / w := by rw [ht]
      _ = _ := by field_simp <;> ring
  rw [hq, ht2]
  ring

/-- The logarithmic Pogorelov test for one actual coordinate direction. -/
def pogorelovTest (u : CoordinateSpace n → ℝ) (i : Fin n) (y : CoordinateSpace n) : ℝ :=
  Real.log (coordinateHessian u y i i) + Real.log (u y) + (coordinateDerivative i u y)^2 / 2

lemma gradient_coordinateDerivative_eq_hessian_column {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) (i : Fin n) (x : CoordinateSpace n) :
    coordinateGradient (coordinateDerivative i u) x = coordinateHessian u x *ᵥ Pi.single i 1 := by
  rw [Matrix.mulVec_single_one]
  ext a
  exact (coordinateHessian_isSymm hu x).apply a i

lemma pogorelovTest_stationary {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (i : Fin n) {x : CoordinateSpace n}
    (hw : coordinateHessian u x i i ≠ 0) (hx : u x ≠ 0)
    (hmax : IsLocalMax (pogorelovTest u i) x) :
    (coordinateHessian u x i i)⁻¹ • coordinateGradient (fun y => coordinateHessian u y i i) x +
      (u x)⁻¹ • coordinateGradient u x +
      coordinateDerivative i u x • coordinateGradient (coordinateDerivative i u) x = 0 := by
  have hU := hu.differentiable (by simp)
  have hW := (smooth_coordinateHessian hu i i).differentiable (by simp)
  have hG := (smooth_coordinateDerivative hu i).differentiable (by simp)
  have hz := hmax.fderiv_eq_zero
  ext j
  have hj : coordinateDerivative j (pogorelovTest u i) x = 0 := by
    simp only [coordinateDerivative, hz, ContinuousLinearMap.zero_apply]
  unfold pogorelovTest at hj
  rw [coordinateDerivative_add_at ((hW x).log hw |>.fun_add ((hU x).log hx))
    ((((smooth_coordinateDerivative hu i).pow 2).div_const 2).differentiable (by simp) x),
    coordinateDerivative_add_at ((hW x).log hw) ((hU x).log hx),
    coordinateDerivative_log_at (hW x) hw, coordinateDerivative_log_at (hU x) hx,
    coordinateDerivative_half_sq_at (hG x)] at hj
  exact hj

/-- The genuine local weighted maximum inequality. It is obtained from the
actual determinant equation and actual maximum, not from a supplied
elliptic differential inequality. -/
theorem pogorelov_differential_inequality_at_max {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (i : Fin n) {x : CoordinateSpace n}
    (hH : (coordinateHessian u x).PosDef) (hx : u x < 0)
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1)
    (hmax : IsLocalMax (pogorelovTest u i) x) :
    (n : ℝ) / u x - (coordinateDerivative i u x)^2 /
      ((u x)^2 * coordinateHessian u x i i) + coordinateHessian u x i i ≤ 0 := by
  let H := coordinateHessian u x
  let A := H⁻¹
  let D := matrixCoordinateDerivative (coordinateHessian u) i x
  let w := coordinateHessian u x i i
  let b := coordinateGradient (fun y => coordinateHessian u y i i) x
  let g := coordinateGradient u x
  let v := coordinateGradient (coordinateDerivative i u) x
  let e : CoordinateSpace n := Pi.single i 1
  have hU : ContDiffAt ℝ 2 u x := (contDiff_infty.mp hu 2).contDiffAt
  have hW : ContDiffAt ℝ 2 (fun y => coordinateHessian u y i i) x :=
    (contDiff_infty.mp (smooth_coordinateHessian hu i i) 2).contDiffAt
  have hG : ContDiffAt ℝ 2 (coordinateDerivative i u) x :=
    (contDiff_infty.mp (smooth_coordinateDerivative hu i) 2).contDiffAt
  have he : e ≠ 0 := by dsimp [e]; intro hz; have hi := congrFun hz i; simpa using hi
  have hw : 0 < w := by
    have hp := hH.2 e he
    simpa [e, Matrix.mulVec_single_one, single_dotProduct, Matrix.col, w] using hp
  have hAe : A *ᵥ v = e := by
    dsimp [v]
    rw [gradient_coordinateDerivative_eq_hessian_column (contDiff_infty.mp hu 2)]
    change H⁻¹ *ᵥ (H *ᵥ e) = e
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
      Matrix.one_mulVec]
  have hvi : v i = w := rfl
  have hA : A.IsSymm := by
    simpa only [Matrix.IsSymm, Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hH.inv.isHermitian
  have hstat : w⁻¹ • b + (u x)⁻¹ • g + g i • v = 0 := pogorelovTest_stationary hu i hw.ne' hx.ne hmax
  have hcancel := pogorelov_stationarity_cancellation A hA i v g b hw.ne' hx.ne hAe hvi hstat
  have hLw : linearizedMA A (fun y => coordinateHessian u y i i) x = trace (A * D * A * D) :=
    constant_density_second_trace hu hMA i
  have hLu : linearizedMA A u x = n := by
    change trace (H⁻¹ * H) = _
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'), Matrix.trace_one]
    simp
  have hLg : linearizedMA A (coordinateDerivative i u) x = 0 := by
    unfold linearizedMA
    rw [hessian_coordinateDerivative_eq_matrixDerivative hu]
    exact constant_density_first_trace hu hMA i
  have hvg : v ⬝ᵥ (A *ᵥ v) = w := by rw [hAe]; simp [e, dotProduct_single, hvi]
  have hQ : ContDiffAt ℝ 2 (pogorelovTest u i) x :=
    ((hW.log hw.ne').add (hU.log hx.ne)).add ((hG.pow 2).div_const 2)
  have hmaxL := linearizedMA_nonpos_at_max hH.inv.posSemidef hQ hmax
  have hcalc : linearizedMA A (pogorelovTest u i) x =
      trace (A * D * A * D) / w - (b ⬝ᵥ (A *ᵥ b)) / w^2 +
      ((n : ℝ) / u x - (g ⬝ᵥ (A *ᵥ g)) / (u x)^2) + w := by
    unfold pogorelovTest
    rw [linearizedMA_add_at A ((hW.log hw.ne').add (hU.log hx.ne)) ((hG.pow 2).div_const 2),
      linearizedMA_add_at A (hW.log hw.ne') (hU.log hx.ne),
      linearizedMA_log_at A hW hw.ne', linearizedMA_log_at A hU hx.ne,
      linearizedMA_half_sq_at A hG, hLw, hLu, hLg]
    change _ = _
    simp only [mul_zero, zero_add]
    rw [hvg]
  change linearizedMA A (pogorelovTest u i) x ≤ 0 at hmaxL
  rw [hcalc] at hmaxL
  have hD : D.IsSymm := matrixCoordinateDerivative_hessian_isSymm (contDiff_infty.mp hu 2) i x
  have hHe : e ⬝ᵥ (H *ᵥ e) = w := by simp [e, Matrix.mulVec_single_one, single_dotProduct, H, w, Matrix.col]
  have hDb : D *ᵥ e = b := (gradient_hessian_diagonal_eq_matrixDerivative_column hu i x).symm
  have heb : e ⬝ᵥ b = b i := by simp [e, single_dotProduct]
  have hthird := pogorelov_third_derivative_contraction H D hH hD e (hHe ▸ hw)
  rw [hHe, hDb, heb] at hthird
  change 2 * (b ⬝ᵥ (A *ᵥ b)) / w - (b i)^2 / w^2 ≤ trace (A * D * A * D) at hthird
  have hthird' : 2 * (b ⬝ᵥ (A *ᵥ b)) / w^2 - (b i)^2 / w^3 ≤ trace (A * D * A * D) / w := by
    have ht := div_le_div_of_nonneg_right hthird hw.le
    convert ht using 1 <;> ring
  change (n : ℝ) / u x - (g i)^2 / ((u x)^2 * w) + w ≤ 0
  calc
    (n : ℝ) / u x - (g i)^2 / ((u x)^2 * w) + w =
        (2 * (b ⬝ᵥ (A *ᵥ b)) / w^2 - (b i)^2 / w^3) +
          (-(b ⬝ᵥ (A *ᵥ b)) / w^2 + (n : ℝ) / u x - (g ⬝ᵥ (A *ᵥ g)) / (u x)^2 + w) := by
      linear_combination -hcancel
    _ ≤ trace (A * D * A * D) / w +
        (-(b ⬝ᵥ (A *ᵥ b)) / w^2 + (n : ℝ) / u x - (g ⬝ᵥ (A *ᵥ g)) / (u x)^2 + w) :=
      add_le_add_right hthird' _
    _ ≤ 0 := by convert hmaxL using 1 <;> ring

/-- The local Pogorelov estimate for a genuine unit-density smooth solution
at an interior maximum of the actual logarithmic test function. -/
theorem pogorelov_weighted_hessian_bound_at_max {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (i : Fin n) {x : CoordinateSpace n}
    (hH : (coordinateHessian u x).PosDef) (hx : u x < 0)
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1)
    (hmax : IsLocalMax (pogorelovTest u i) x) :
    (-u x) * coordinateHessian u x i i ≤ n + |coordinateDerivative i u x| := by
  let w := coordinateHessian u x i i
  let d := coordinateDerivative i u x
  have hw : 0 < w := by
    have hp := hH.2 (Pi.single i 1) (by intro hz; have hi := congrFun hz i; simpa using hi)
    simpa [Matrix.mulVec_single_one, single_dotProduct, Matrix.col, w] using hp
  have hdiff := pogorelov_differential_inequality_at_max hu i hH hx hMA hmax
  change (n : ℝ) / u x - d^2 / ((u x)^2 * w) + w ≤ 0 at hdiff
  have hpoly : (u x)^2 * w^2 + (n : ℝ) * u x * w ≤ d^2 := by
    have hm := mul_nonpos_of_nonpos_of_nonneg hdiff (mul_nonneg (sq_nonneg (u x)) hw.le)
    have he : ((n : ℝ) / u x - d^2 / ((u x)^2 * w) + w) * ((u x)^2 * w) =
        (n : ℝ) * u x * w - d^2 + (u x)^2 * w^2 := by
      field_simp [hx.ne, hw.ne']
      <;> ring
    rw [he] at hm
    linarith
  change (-u x) * w ≤ (n : ℝ) + |d|
  by_contra hbad
  have ht : (n : ℝ) + |d| < (-u x) * w := lt_of_not_ge hbad
  have hp : 0 < ((-u x) * w - ((n : ℝ) + |d|)) * ((-u x) * w + |d|) :=
    mul_pos (sub_pos.mpr ht) (by have hp := mul_pos (neg_pos.mpr hx) hw; positivity)
  nlinarith [sq_abs d, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (abs_nonneg d)]

end GaussianTilt.MomentMapRegularity
