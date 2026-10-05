import GaussianTilt.MomentMapRegularityVariableDensityPogorelov
import GaussianTilt.MomentMapRegularityConstantDensityCalabiSymmetry

/-!
# Actual Calabi calculus for a variable Monge--Ampère density

The smooth inverse field is exp(−F) adj(Hess u), which agrees with the
literal inverse exactly on det Hess u = exp F. Differentiation retains all
second and third derivatives of the prescribed logarithmic forcing.
-/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def variableInverseHessian (u F : CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    Matrix (Fin n) (Fin n) ℝ := Real.exp (-F x) • (coordinateHessian u x).adjugate

def variableCalabiEnergy (u F : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  cubicMetricEnergy (variableInverseHessian u F x) (coordinateThirdDerivative u x)

lemma variableInverseHessian_eq_inverse {u F : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hMA : (coordinateHessian u x).det = Real.exp (F x)) :
    variableInverseHessian u F x = (coordinateHessian u x)⁻¹ := by
  rw [Matrix.inv_def, hMA, Ring.inverse_eq_inv', ← Real.exp_neg]
  rfl

lemma smooth_variableInverseHessian {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) (a b : Fin n) :
    ContDiff ℝ ∞ (fun x => variableInverseHessian u F x a b) :=
  (hF.neg.exp).mul (smooth_hessian_adjugate hu a b)

lemma variableInverseHessian_symm {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : CoordinateSpace n) : (variableInverseHessian u F x).IsSymm := by
  change (Real.exp (-F x) • (coordinateHessian u x).adjugate)ᵀ = _
  rw [Matrix.transpose_smul, (hessian_adjugate_symm hu x).eq]
  rfl

lemma contDiff_variableCalabiEnergy {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (variableCalabiEnergy u F) := by
  unfold variableCalabiEnergy cubicMetricEnergy
  apply ContDiff.sum; intro a _
  apply ContDiff.sum; intro b _
  apply ContDiff.sum; intro c _
  apply ContDiff.sum; intro i _
  apply ContDiff.sum; intro j _
  apply ContDiff.sum; intro k _
  exact ((((smooth_variableInverseHessian hu hF a i).mul (smooth_variableInverseHessian hu hF b j)).mul
    (smooth_variableInverseHessian hu hF c k)).mul (smooth_coordinateThirdDerivative hu a b c)).mul
    (smooth_coordinateThirdDerivative hu i j k)

/-- The first actual inverse derivative on the variable-density equation. -/
theorem variable_inverse_first {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y)) (i : Fin n) :
    matrixCoordinateDerivative (variableInverseHessian u F) i x =
      -(variableInverseHessian u F x * matrixCoordinateDerivative (coordinateHessian u) i x *
        variableInverseHessian u F x) := by
  let H := coordinateHessian u
  let K := variableInverseHessian u F
  have hHd (a b : Fin n) : Differentiable ℝ (fun y => H y a b) :=
    (smooth_coordinateHessian hu a b).differentiable (by simp)
  have hKd (a b : Fin n) : Differentiable ℝ (fun y => K y a b) :=
    (smooth_variableInverseHessian hu hF a b).differentiable (by simp)
  have hHK : H x * K x = 1 := by
    rw [show K x = (H x)⁻¹ from variableInverseHessian_eq_inverse hMA.self_of_nhds]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (by rw [hMA.self_of_nhds]; exact (Real.exp_pos _).ne'))
  have he : (fun y => K y * H y) =ᶠ[𝓝 x] (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    filter_upwards [hMA] with y hy
    rw [show K y = (H y)⁻¹ from variableInverseHessian_eq_inverse hy]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (by rw [hy]; exact (Real.exp_pos _).ne'))
  have hz : matrixCoordinateDerivative (fun y => K y * H y) i x = 0 := by
    ext a b
    have hij := he.mono (fun y hy => congrFun (congrFun hy a) b)
    change coordinateDerivative i (fun y => (K y * H y) a b) x = 0
    rw [coordinateDerivative_congr_nhds hij i]
    simp [coordinateDerivative]
  rw [matrixCoordinateDerivative_mul hKd hHd] at hz
  have hh := congrArg (fun M => M * K x) hz
  dsimp only at hh
  rw [Matrix.add_mul, Matrix.mul_assoc, hHK, Matrix.mul_one, Matrix.zero_mul] at hh
  exact eq_neg_of_add_eq_zero_left hh

/-- The second inverse derivative at H=I, derived without discarding any
forcing derivative: the inverse identity itself has the same exact form. -/
theorem variable_inverse_second_at_identity {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y))
    (hI : coordinateHessian u x = 1) (i : Fin n) :
    matrixCoordinateDerivative
      (fun y => matrixCoordinateDerivative (variableInverseHessian u F) i y) i x =
      (2 : ℝ) • (matrixCoordinateDerivative (coordinateHessian u) i x *
        matrixCoordinateDerivative (coordinateHessian u) i x) -
      matrixCoordinateDerivative (fun y => matrixCoordinateDerivative (coordinateHessian u) i y) i x := by
  let H := coordinateHessian u
  let K := variableInverseHessian u F
  let T := fun y => matrixCoordinateDerivative H i y
  have hK (a b : Fin n) : Differentiable ℝ (fun y => K y a b) :=
    (smooth_variableInverseHessian hu hF a b).differentiable (by simp)
  have hT (a b : Fin n) : Differentiable ℝ (fun y => T y a b) :=
    (smooth_coordinateThirdDerivative hu a b i).differentiable (by simp)
  have hKT := differentiable_matrix_mul_entries hK hT
  have he : (fun y => matrixCoordinateDerivative K i y) =ᶠ[𝓝 x]
      (fun y => -(K y * T y * K y)) := by
    filter_upwards [hMA.eventually_nhds] with y hy
    exact variable_inverse_first hu hF hy i
  have hd := matrixCoordinateDerivative_congr_nhds he i
  rw [matrixCoordinateDerivative_neg, matrixCoordinateDerivative_mul hKT hK,
    matrixCoordinateDerivative_mul hK hT] at hd
  have hKx : K x = 1 := by
    change variableInverseHessian u F x = 1
    rw [variableInverseHessian_eq_inverse hMA.self_of_nhds, hI]; simp
  have hKi : matrixCoordinateDerivative K i x = -T x := by
    have hh := variable_inverse_first hu hF hMA i
    change matrixCoordinateDerivative K i x = -(K x * T x * K x) at hh
    simpa only [hKx, Matrix.one_mul, Matrix.mul_one] using hh
  rw [hKx, hKi] at hd
  simp only [Matrix.one_mul, Matrix.mul_one] at hd
  rw [hd]
  change -((-T x * T x + matrixCoordinateDerivative T i x) + T x * -T x) = _
  simp only [Matrix.neg_mul, Matrix.mul_neg]
  module

/-- The mixed twice-differentiated determinant retains Fᵢⱼ explicitly. -/
theorem variable_inverse_second_trace {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y)) (i j : Fin n) :
    trace (variableInverseHessian u F x *
      matrixCoordinateDerivative (fun y => matrixCoordinateDerivative (coordinateHessian u) i y) j x) =
    trace (variableInverseHessian u F x * matrixCoordinateDerivative (coordinateHessian u) j x *
      variableInverseHessian u F x * matrixCoordinateDerivative (coordinateHessian u) i x) +
      coordinateHessian F x i j := by
  rw [variableInverseHessian_eq_inverse hMA.self_of_nhds, matrixCoordinateDerivative_hessian_exchange hu]
  exact variable_density_second_trace hu hF hMA i j

theorem variable_density_third_trace_at_identity {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y))
    (hI : coordinateHessian u x = 1) (i j k : Fin n) :
    let T := fun a => matrixCoordinateDerivative (coordinateHessian u) a x
    let Q := fun a b => matrixCoordinateDerivative
      (fun y => matrixCoordinateDerivative (coordinateHessian u) a y) b x
    trace (matrixCoordinateDerivative (fun z => matrixCoordinateDerivative
      (fun y => matrixCoordinateDerivative (coordinateHessian u) i y) j z) k x) =
      trace (T k * Q i j) + trace (Q j k * T i) + trace (T j * Q i k) -
        trace (T k * T j * T i) - trace (T j * T k * T i) + coordinateThirdDerivative F x i j k := by
  let H := coordinateHessian u
  let K := variableInverseHessian u F
  let T := fun a y => matrixCoordinateDerivative H a y
  let Q := fun a b y => matrixCoordinateDerivative (T a) b y
  have hK (a b : Fin n) : Differentiable ℝ (fun y => K y a b) :=
    (smooth_variableInverseHessian hu hF a b).differentiable (by simp)
  have hT (d a b : Fin n) : Differentiable ℝ (fun y => T d y a b) :=
    (smooth_coordinateThirdDerivative hu a b d).differentiable (by simp)
  have hQ (c d a b : Fin n) : Differentiable ℝ (fun y => Q c d y a b) :=
    (smooth_coordinateFourthDerivative hu a b c d).differentiable (by simp)
  have he : (fun y => trace (K y * Q i j y)) =ᶠ[𝓝 x]
      (fun y => trace (K y * T j y * K y * T i y) + coordinateHessian F y i j) := by
    filter_upwards [hMA.eventually_nhds] with y hy
    exact variable_inverse_second_trace hu hF hy i j
  have htr : Differentiable ℝ (fun y => trace (K y * T j y * K y * T i y)) := by
    unfold Matrix.trace Matrix.diag
    exact Differentiable.fun_sum (fun a _ => differentiable_matrix_mul_entries
      (differentiable_matrix_mul_entries (differentiable_matrix_mul_entries hK (hT j)) hK) (hT i) a a)
  have hd := coordinateDerivative_congr_nhds he k
  rw [coordinateDerivative_add htr ((smooth_coordinateHessian hF i j).differentiable (by simp))] at hd
  rw [coordinateDerivative_trace (differentiable_matrix_mul_entries hK (hQ i j)),
    coordinateDerivative_trace (differentiable_matrix_mul_entries
      (differentiable_matrix_mul_entries (differentiable_matrix_mul_entries hK (hT j)) hK) (hT i)),
    matrixCoordinateDerivative_mul hK (hQ i j),
    matrixCoordinateDerivative_mul
      (differentiable_matrix_mul_entries (differentiable_matrix_mul_entries hK (hT j)) hK) (hT i),
    matrixCoordinateDerivative_mul (differentiable_matrix_mul_entries hK (hT j)) hK,
    matrixCoordinateDerivative_mul hK (hT j), variable_inverse_first hu hF hMA k] at hd
  have hKx : K x = 1 := by
    change variableInverseHessian u F x = 1
    rw [variableInverseHessian_eq_inverse hMA.self_of_nhds, hI]; simp
  change trace ((-(K x * T k x * K x)) * Q i j x + K x * matrixCoordinateDerivative (Q i j) k x) =
    trace ((((-(K x * T k x * K x)) * T j x + K x * Q j k x) * K x +
      (K x * T j x) * (-(K x * T k x * K x))) * T i x +
      (K x * T j x * K x) * Q i k x) + coordinateThirdDerivative F x i j k at hd
  rw [hKx] at hd
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.add_mul, Matrix.trace_add, Matrix.trace_neg] at hd
  change trace (matrixCoordinateDerivative (Q i j) k x) = _
  dsimp only
  dsimp only [T, Q, H] at hd
  linarith

theorem variable_density_fourth_contraction {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y))
    (hI : coordinateHessian u x = 1) (i j : Fin n) :
    (∑ l, coordinateFourthDerivative u x i j l l) =
      (∑ a, ∑ b, coordinateThirdDerivative u x i a b * coordinateThirdDerivative u x j a b) + coordinateHessian F x i j := by
  have hh := variable_inverse_second_trace hu hF hMA i j
  rw [variableInverseHessian_eq_inverse hMA.self_of_nhds] at hh
  rw [matrixSecondDerivative_hessian_eq_fourth_first hu,
    matrixDerivative_hessian_eq_third_first hu, matrixDerivative_hessian_eq_third_first hu,
    hI] at hh
  simp only [inv_one, Matrix.one_mul, Matrix.mul_one] at hh
  change trace (fun a b => coordinateFourthDerivative u x i j a b) = _
  rw [hh]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [coordinateThirdDerivative_swap_last (contDiff_infty.mp hu 3) x i b a]
  ring

theorem variable_density_fifth_contraction {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y))
    (hI : coordinateHessian u x = 1) (i j k : Fin n) :
    (∑ l, coordinateFifthDerivative u x i j k l l) =
      (∑ a, ∑ b, (coordinateFourthDerivative u x i j a b * coordinateThirdDerivative u x k a b +
        coordinateFourthDerivative u x i k a b * coordinateThirdDerivative u x j a b +
        coordinateFourthDerivative u x j k a b * coordinateThirdDerivative u x i a b)) -
      2 * ∑ a, ∑ b, ∑ c, coordinateThirdDerivative u x i a b *
        coordinateThirdDerivative u x j b c * coordinateThirdDerivative u x k c a + coordinateThirdDerivative F x i j k := by
  let T : Fin n → Matrix (Fin n) (Fin n) ℝ := fun d a b => coordinateThirdDerivative u x d a b
  let Q : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ := fun c d a b => coordinateFourthDerivative u x c d a b
  have hTs (d : Fin n) : (T d).IsSymm := by
    ext a b
    exact coordinateThirdDerivative_swap_last (contDiff_infty.mp hu 3) x d b a
  have ht (c d e : Fin n) : trace (T c * Q d e) =
      ∑ a, ∑ b, coordinateFourthDerivative u x d e a b * coordinateThirdDerivative u x c a b := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, T, Q]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [coordinateFourthDerivative_swap34 hu x d e b a]
    ring
  have hh := variable_density_third_trace_at_identity hu hF hMA hI i j k
  dsimp only at hh
  rw [matrixThirdDerivative_hessian_trace hu] at hh
  rw [matrixSecondDerivative_hessian_eq_fourth_first hu x i j,
    matrixSecondDerivative_hessian_eq_fourth_first hu x j k,
    matrixSecondDerivative_hessian_eq_fourth_first hu x i k] at hh
  simp only [matrixDerivative_hessian_eq_third_first hu] at hh
  change _ = trace (T k * Q i j) + trace (Q j k * T i) + trace (T j * Q i k) -
    trace (T k * T j * T i) - trace (T j * T k * T i) + coordinateThirdDerivative F x i j k at hh
  rw [Matrix.trace_mul_comm (Q j k) (T i), ht, ht, ht,
    trace_triple_reverse (T k) (T j) (T i) (hTs k) (hTs j) (hTs i),
    Matrix.trace_mul_cycle (T j) (T k) (T i), trace_triple_expansion] at hh
  rw [hh]
  simp only [Finset.sum_add_distrib]
  dsimp only [T]
  ring

theorem coordinateHessian_variableCalabiEnergy_diagonal {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) (l : Fin n) (x : CoordinateSpace n) :
    let K := variableInverseHessian u F
    let K₁ := fun y => matrixCoordinateDerivative K l y
    let T := coordinateThirdDerivative u x
    let T₁ := fun a b c => coordinateFourthDerivative u x a b c l
    coordinateHessian (variableCalabiEnergy u F) x l l =
      3 * calabiContraction (matrixCoordinateDerivative K₁ l x) (K x) (K x) T T +
      6 * calabiContraction (K₁ x) (K₁ x) (K x) T T +
      12 * calabiContraction (K₁ x) (K x) (K x) T₁ T +
      2 * calabiContraction (K x) (K x) (K x)
        (fun a b c => coordinateFifthDerivative u x a b c l l) T +
      2 * calabiContraction (K x) (K x) (K x) T₁ T₁ := by
  have he : variableCalabiEnergy u F = fun y => calabiContraction
      (variableInverseHessian u F y) (variableInverseHessian u F y)
      (variableInverseHessian u F y) (coordinateThirdDerivative u y) (coordinateThirdDerivative u y) := by
    funext y
    exact (calabiContraction_diagonal_eq _ _).symm
  rw [he]
  exact second_coordinateDerivative_calabiContraction_diagonal
    (smooth_variableInverseHessian hu hF) (smooth_coordinateThirdDerivative hu)
    (variableInverseHessian_symm (F := F) hu) (calabiTensorSymm_actual hu) l x

/-- The actual normalized Laplacian expansion, retaining the fifth derivative
until the third differentiated determinant identity is substituted. -/
theorem linearized_variableCalabiEnergy_at_identity {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y))
    (hI : coordinateHessian u x = 1) :
    let T := coordinateThirdDerivative u x
    let Tl : Fin n → Matrix (Fin n) (Fin n) ℝ := fun l a b => coordinateThirdDerivative u x a b l
    let Ql := fun l a b c => coordinateFourthDerivative u x a b c l
    let Qll : Fin n → Matrix (Fin n) (Fin n) ℝ := fun l a b => coordinateFourthDerivative u x a b l l
    linearizedMA (1 : Matrix (Fin n) (Fin n) ℝ) (variableCalabiEnergy u F) x =
      ∑ l, (3 * calabiContraction ((2 : ℝ) • (Tl l * Tl l) - Qll l) 1 1 T T +
        6 * calabiContraction (-Tl l) (-Tl l) 1 T T +
        12 * calabiContraction (-Tl l) 1 1 (Ql l) T +
        2 * calabiContraction 1 1 1 (fun a b c => coordinateFifthDerivative u x a b c l l) T +
        2 * calabiContraction 1 1 1 (Ql l) (Ql l)) := by
  unfold linearizedMA
  rw [Matrix.one_mul]
  change (∑ l, coordinateHessian (variableCalabiEnergy u F) x l l) = _
  apply Finset.sum_congr rfl
  intro l _
  rw [coordinateHessian_variableCalabiEnergy_diagonal hu hF]
  dsimp only
  rw [variable_inverse_second_at_identity hu hF hMA hI,
    variable_inverse_first hu hF hMA]
  have hKx : variableInverseHessian u F x = 1 := by
    rw [variableInverseHessian_eq_inverse hMA.self_of_nhds, hI]; simp
  rw [hKx]
  simp only [Matrix.one_mul, Matrix.mul_one]
  rfl

end GaussianTilt.MomentMapRegularity
