import GaussianTilt.MomentMapRegularityConstantDensityInterior
import GaussianTilt.MomentMapClassicalDirichletForcing

/-!
# Genuine Pogorelov estimates with variable logarithmic forcing

The continuation equation is det Hess u = exp F. The actual first and
second derivatives of F are retained in the local maximum calculation.
-/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

theorem variable_pogorelov_differential_inequality_at_max {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) (i : Fin n) {x : CoordinateSpace n}
    (hH : (coordinateHessian u x).PosDef) (hx : u x < 0)
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y))
    (hmax : IsLocalMax (pogorelovTest u i) x) :
    (n : ℝ) / u x - (coordinateDerivative i u x)^2 /
      ((u x)^2 * coordinateHessian u x i i) + coordinateHessian u x i i +
      coordinateHessian F x i i / coordinateHessian u x i i +
      coordinateDerivative i u x * coordinateDerivative i F x ≤ 0 := by
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
  have hLw : linearizedMA A (fun y => coordinateHessian u y i i) x = trace (A * D * A * D) + coordinateHessian F x i i :=
    variable_density_second_trace hu hF hMA i i
  have hLu : linearizedMA A u x = n := by
    change trace (H⁻¹ * H) = _
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'), Matrix.trace_one]
    simp
  have hLg : linearizedMA A (coordinateDerivative i u) x = coordinateDerivative i F x := by
    unfold linearizedMA
    rw [hessian_coordinateDerivative_eq_matrixDerivative hu]
    exact variable_density_first_trace hu hMA i
  have hvg : v ⬝ᵥ (A *ᵥ v) = w := by rw [hAe]; simp [e, dotProduct_single, hvi]
  have hQ : ContDiffAt ℝ 2 (pogorelovTest u i) x :=
    ((hW.log hw.ne').add (hU.log hx.ne)).add ((hG.pow 2).div_const 2)
  have hmaxL := linearizedMA_nonpos_at_max hH.inv.posSemidef hQ hmax
  have hcalc : linearizedMA A (pogorelovTest u i) x =
      (trace (A * D * A * D) + coordinateHessian F x i i) / w - (b ⬝ᵥ (A *ᵥ b)) / w^2 +
      ((n : ℝ) / u x - (g ⬝ᵥ (A *ᵥ g)) / (u x)^2) +
      (g i * coordinateDerivative i F x + w) := by
    unfold pogorelovTest
    rw [linearizedMA_add_at A ((hW.log hw.ne').add (hU.log hx.ne)) ((hG.pow 2).div_const 2),
      linearizedMA_add_at A (hW.log hw.ne') (hU.log hx.ne),
      linearizedMA_log_at A hW hw.ne', linearizedMA_log_at A hU hx.ne,
      linearizedMA_half_sq_at A hG, hLw, hLu, hLg]
    change _ = _
    rw [hvg]
    rfl
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
  change (n : ℝ) / u x - (g i)^2 / ((u x)^2 * w) + w +
    coordinateHessian F x i i / w + g i * coordinateDerivative i F x ≤ 0
  calc
    (n : ℝ) / u x - (g i)^2 / ((u x)^2 * w) + w +
      coordinateHessian F x i i / w + g i * coordinateDerivative i F x =
        (2 * (b ⬝ᵥ (A *ᵥ b)) / w^2 - (b i)^2 / w^3) +
          (-(b ⬝ᵥ (A *ᵥ b)) / w^2 + (n : ℝ) / u x - (g ⬝ᵥ (A *ᵥ g)) / (u x)^2 + w +
            coordinateHessian F x i i / w + g i * coordinateDerivative i F x) := by
      linear_combination -hcancel
    _ ≤ trace (A * D * A * D) / w +
        (-(b ⬝ᵥ (A *ᵥ b)) / w^2 + (n : ℝ) / u x - (g ⬝ᵥ (A *ᵥ g)) / (u x)^2 + w +
            coordinateHessian F x i i / w + g i * coordinateDerivative i F x) :=
      add_le_add_right hthird' _
    _ ≤ 0 := by convert hmaxL using 1 <;> ring


/-- The explicit weighted bound with first and second logarithmic forcing. -/
def variablePogorelovConstant (n : ℕ) (C₀ M K₁ K₂ : ℝ) : ℝ :=
  (n : ℝ) + C₀*M*K₁ + Real.sqrt (M^2 + C₀^2*K₂)

/-- Quantitative forced Pogorelov estimate at an actual maximum. Every
forcing error is bounded explicitly; no constant-density cancellation is used. -/
theorem variable_pogorelov_weighted_hessian_bound_at_max {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) (i : Fin n) {x : CoordinateSpace n}
    (hH : (coordinateHessian u x).PosDef) (hx : u x < 0)
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y))
    (hmax : IsLocalMax (pogorelovTest u i) x)
    {C₀ M K₁ K₂ : ℝ} (hC₀ : 0 ≤ C₀) (hM : 0 ≤ M) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hux : -u x ≤ C₀) (hdu : |coordinateDerivative i u x| ≤ M)
    (hF₁ : |coordinateDerivative i F x| ≤ K₁) (hF₂ : -K₂ ≤ coordinateHessian F x i i) :
    (-u x) * coordinateHessian u x i i ≤ variablePogorelovConstant n C₀ M K₁ K₂ := by
  let w := coordinateHessian u x i i
  let d := coordinateDerivative i u x
  let b := -u x
  let t := b*w
  have hw : 0 < w := coordinateHessian_diagonal_pos hH i
  have hb : 0 < b := neg_pos.mpr hx
  have ht : 0 < t := mul_pos hb hw
  have hdp : -M*K₁ ≤ d*coordinateDerivative i F x := by
    have ha : |d*coordinateDerivative i F x| ≤ M*K₁ := by
      rw [abs_mul]
      exact mul_le_mul hdu hF₁ (abs_nonneg _) hM
    simpa only [neg_mul] using (neg_le_neg ha).trans (neg_abs_le _)
  have hdiff := variable_pogorelov_differential_inequality_at_max hu hF i hH hx hMA hmax
  change (n : ℝ)/u x - d^2/((u x)^2*w)+w+coordinateHessian F x i i/w+
    d*coordinateDerivative i F x ≤ 0 at hdiff
  have hpoly : t^2-(n : ℝ)*t-d^2+b^2*coordinateHessian F x i i+
      b*t*(d*coordinateDerivative i F x) ≤ 0 := by
    have hm := mul_nonpos_of_nonpos_of_nonneg hdiff (mul_nonneg (sq_nonneg (u x)) hw.le)
    have he : ((n : ℝ)/u x - d^2/((u x)^2*w)+w+coordinateHessian F x i i/w+
        d*coordinateDerivative i F x) * ((u x)^2*w) =
        t^2-(n : ℝ)*t-d^2+b^2*coordinateHessian F x i i+b*t*(d*coordinateDerivative i F x) := by
      dsimp [t, b]
      field_simp [hx.ne, hw.ne']
      <;> ring
    rwa [he] at hm
  have hdiag := mul_le_mul_of_nonneg_left hF₂ (sq_nonneg b)
  have hcross := mul_le_mul_of_nonneg_left hdp (mul_nonneg hb.le ht.le)
  have hd2 : d^2 ≤ M^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg d) hdu 2
  have hb2 : b^2 ≤ C₀^2 := pow_le_pow_left₀ hb.le hux 2
  have hsecond := mul_le_mul_of_nonneg_right hb2 hK₂
  have hfirst := mul_le_mul_of_nonneg_right hux (show 0 ≤ t*M*K₁ by positivity)
  have hquad : t^2 ≤ ((n : ℝ)+C₀*M*K₁)*t+(M^2+C₀^2*K₂) := by nlinarith
  let A : ℝ := (n : ℝ)+C₀*M*K₁
  let B : ℝ := Real.sqrt (M^2+C₀^2*K₂)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hB2 : B^2 = M^2+C₀^2*K₂ := Real.sq_sqrt (by positivity)
  change t ≤ A+B
  by_contra hnot
  have hlarge : A+B < t := lt_of_not_ge hnot
  have hproduct : 0 < (t-(A+B))*(t+B) := mul_pos (sub_pos.mpr hlarge) (by positivity)
  change t^2 ≤ A*t+(M^2+C₀^2*K₂) at hquad
  nlinarith [mul_nonneg hA hB]

/-- Genuine compact-section maximum estimate for variable forcing, including all first and second forcing errors. -/
theorem variable_pogorelov_weighted_hessian_bound_on_section {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    (hzero : ∀ y ∈ frontier S, u y = 0)
    (hneg : ∀ y ∈ interior S, u y < 0)
    (hH : ∀ y ∈ interior S, (coordinateHessian u y).PosDef)
    (hMA : ∀ y ∈ interior S, (coordinateHessian u y).det = Real.exp (F y))
    {C₀ M K₁ K₂ : ℝ} (hC₀ : 0 ≤ C₀) (hM : 0 ≤ M) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (habs : ∀ y ∈ S, |u y| ≤ C₀)
    (hDu : ∀ y ∈ S, ∀ i : Fin n, |coordinateDerivative i u y| ≤ M)
    (hF₁ : ∀ y ∈ interior S, ∀ i : Fin n, |coordinateDerivative i F y| ≤ K₁)
    (hF₂ : ∀ y ∈ interior S, ∀ i : Fin n, -K₂ ≤ coordinateHessian F y i i) :
    ∀ x ∈ interior S, ∀ i : Fin n,
      (-u x) * coordinateHessian u x i i ≤ variablePogorelovConstant n C₀ M K₁ K₂ * Real.exp (M^2 / 2) := by
  intro x hx i
  have hxw : 0 < coordinateHessian u x i i := coordinateHessian_diagonal_pos (hH x hx) i
  have hxF : 0 < pogorelovWeight u i x :=
    mul_pos (mul_pos (neg_pos.mpr (hneg x hx)) hxw) (Real.exp_pos _)
  obtain ⟨z, hz, hmax⟩ := hS.exists_isMaxOn ⟨x, interior_subset hx⟩
    (continuous_pogorelovWeight hu i).continuousOn
  have hzx : pogorelovWeight u i x ≤ pogorelovWeight u i z := hmax (interior_subset hx)
  have hzi : z ∈ interior S := by
    by_contra hnot
    have hzb : z ∈ frontier S := ⟨subset_closure hz, hnot⟩
    have hzF : pogorelovWeight u i z = 0 := by simp [pogorelovWeight, hzero z hzb]
    rw [hzF] at hzx
    exact hxF.not_ge hzx
  have hzw : 0 < coordinateHessian u z i i := coordinateHessian_diagonal_pos (hH z hzi) i
  have hlocal := hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hzi)
  have hQmax : IsLocalMax (pogorelovTest u i) z := by
    have hun : ∀ᶠ y in 𝓝 z, u y < 0 := hu.continuous.continuousAt.eventually
      (eventually_lt_nhds (hneg z hzi))
    have hwp : ∀ᶠ y in 𝓝 z, 0 < coordinateHessian u y i i :=
      (smooth_coordinateHessian hu i i).continuous.continuousAt.eventually (eventually_gt_nhds hzw)
    filter_upwards [hlocal, hun, hwp] with y hy hyn hyw
    rw [← log_pogorelovWeight hyn hyw, ← log_pogorelovWeight (hneg z hzi) hzw]
    exact Real.log_le_log (mul_pos (mul_pos (neg_pos.mpr hyn) hyw) (Real.exp_pos _)) hy
  have hnearMA : ∀ᶠ y in 𝓝 z, (coordinateHessian u y).det = Real.exp (F y) := by
    filter_upwards [isOpen_interior.mem_nhds hzi] with y hy
    exact hMA y hy
  have hzbound := variable_pogorelov_weighted_hessian_bound_at_max hu hF i (hH z hzi) (hneg z hzi) hnearMA hQmax
    hC₀ hM hK₁ hK₂ ((neg_le_abs _).trans (habs z hz)) (hDu z hz i) (hF₁ z hzi i) (hF₂ z hzi i)
  have hd : |coordinateDerivative i u z| ≤ M := hDu z hz i
  have hd2 : (coordinateDerivative i u z)^2 ≤ M^2 := by
    simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg (coordinateDerivative i u z)) hd 2)
  have hzwBound := hzbound
  have hCP : 0 ≤ variablePogorelovConstant n C₀ M K₁ K₂ := by
    unfold variablePogorelovConstant
    positivity
  have hFbound : pogorelovWeight u i z ≤ variablePogorelovConstant n C₀ M K₁ K₂ * Real.exp (M^2 / 2) := by
    exact mul_le_mul hzwBound (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
      hCP
  have hexp : (1 : ℝ) ≤ Real.exp ((coordinateDerivative i u x)^2 / 2) :=
    Real.one_le_exp_iff.mpr (by positivity)
  calc
    (-u x) * coordinateHessian u x i i ≤ pogorelovWeight u i x := by
      exact le_mul_of_one_le_right (mul_nonneg (neg_pos.mpr (hneg x hx)).le hxw.le) hexp
    _ ≤ pogorelovWeight u i z := hzx
    _ ≤ _ := hFbound


/-- Interior Hessian entries for a genuinely variable right-hand side, with
all prescribed forcing errors included in the constant. -/
theorem variable_pogorelov_hessian_entry_bound_at_depth {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F)
    {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    (hzero : ∀ y ∈ frontier S, u y = 0) (hneg : ∀ y ∈ interior S, u y < 0)
    (hH : ∀ y ∈ interior S, (coordinateHessian u y).PosDef)
    (hMA : ∀ y ∈ interior S, (coordinateHessian u y).det = Real.exp (F y))
    {C₀ M K₁ K₂ δ : ℝ} (hC₀ : 0 ≤ C₀) (hM : 0 ≤ M) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hδ : 0 < δ)
    (habs : ∀ y ∈ S, |u y| ≤ C₀)
    (hDu : ∀ y ∈ S, ∀ i : Fin n, |coordinateDerivative i u y| ≤ M)
    (hF₁ : ∀ y ∈ interior S, ∀ i : Fin n, |coordinateDerivative i F y| ≤ K₁)
    (hF₂ : ∀ y ∈ interior S, ∀ i : Fin n, -K₂ ≤ coordinateHessian F y i i)
    {x : CoordinateSpace n} (hx : x ∈ interior S) (hdepth : δ ≤ -u x) (i j : Fin n) :
    |coordinateHessian u x i j| ≤
      (variablePogorelovConstant n C₀ M K₁ K₂ * Real.exp (M^2 / 2)) / δ := by
  apply abs_entry_le_of_posSemidef_diagonal_bound (hH x hx).posSemidef _ i j
  intro k
  apply (le_div_iff₀ hδ).mpr
  have hh := variable_pogorelov_weighted_hessian_bound_on_section hu hF hS hzero hneg hH hMA
    hC₀ hM hK₁ hK₂ habs hDu hF₁ hF₂ x hx k
  have hp := coordinateHessian_diagonal_pos (hH x hx) k
  nlinarith

end GaussianTilt.MomentMapRegularity
