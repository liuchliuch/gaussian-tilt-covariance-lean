import GaussianTilt.MomentMapRegularityConstantDensityCalabiContraction

/-! # Actual higher-derivative symmetries and normalized determinant contractions -/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateFourthDerivative_swap12 {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    (x : CoordinateSpace n) (a b c d : Fin n) :
    coordinateFourthDerivative u x a b c d = coordinateFourthDerivative u x b a c d := by
  exact congrArg (fun f => coordinateDerivative d f x)
    (funext (fun y => coordinateThirdDerivative_symm (contDiff_infty.mp hu 2) y a b c))

lemma coordinateFourthDerivative_swap23 {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    (x : CoordinateSpace n) (a b c d : Fin n) :
    coordinateFourthDerivative u x a b c d = coordinateFourthDerivative u x a c b d := by
  exact congrArg (fun f => coordinateDerivative d f x)
    (funext (fun y => coordinateThirdDerivative_swap_last (contDiff_infty.mp hu 3) y a b c))

lemma coordinateFourthDerivative_swap34 {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    (x : CoordinateSpace n) (a b c d : Fin n) :
    coordinateFourthDerivative u x a b c d = coordinateFourthDerivative u x a b d c :=
  congrFun (coordinateDerivative_commute (contDiff_infty.mp (smooth_coordinateHessian hu a b) 2) d c) x

lemma coordinateFourthDerivative_pair_swap {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    (x : CoordinateSpace n) (a b c d : Fin n) :
    coordinateFourthDerivative u x a b c d = coordinateFourthDerivative u x c d a b := by
  rw [coordinateFourthDerivative_swap23 hu x a b c d,
    coordinateFourthDerivative_swap12 hu x a c b d,
    coordinateFourthDerivative_swap34 hu x c a b d,
    coordinateFourthDerivative_swap23 hu x c a d b]

lemma coordinateFifthDerivative_swap12 {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    (x : CoordinateSpace n) (a b c d e : Fin n) :
    coordinateFifthDerivative u x a b c d e = coordinateFifthDerivative u x b a c d e :=
  congrArg (fun f => coordinateDerivative e f x)
    (funext (fun y => coordinateFourthDerivative_swap12 hu y a b c d))

lemma coordinateFifthDerivative_swap23 {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    (x : CoordinateSpace n) (a b c d e : Fin n) :
    coordinateFifthDerivative u x a b c d e = coordinateFifthDerivative u x a c b d e :=
  congrArg (fun f => coordinateDerivative e f x)
    (funext (fun y => coordinateFourthDerivative_swap23 hu y a b c d))

lemma coordinateFifthDerivative_swap34 {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    (x : CoordinateSpace n) (a b c d e : Fin n) :
    coordinateFifthDerivative u x a b c d e = coordinateFifthDerivative u x a b d c e :=
  congrArg (fun f => coordinateDerivative e f x)
    (funext (fun y => coordinateFourthDerivative_swap34 hu y a b c d))

lemma coordinateFifthDerivative_swap45 {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    (x : CoordinateSpace n) (a b c d e : Fin n) :
    coordinateFifthDerivative u x a b c d e = coordinateFifthDerivative u x a b c e d :=
  congrFun (coordinateDerivative_commute (contDiff_infty.mp (smooth_coordinateThirdDerivative hu a b c) 2) e d) x

lemma coordinateFifthDerivative_pair_cycle {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    (x : CoordinateSpace n) (a b c d e : Fin n) :
    coordinateFifthDerivative u x a b c d e = coordinateFifthDerivative u x c d e a b := by
  rw [coordinateFifthDerivative_swap23 hu x a b c d e,
    coordinateFifthDerivative_swap12 hu x a c b d e,
    coordinateFifthDerivative_swap34 hu x c a b d e,
    coordinateFifthDerivative_swap23 hu x c a d b e,
    coordinateFifthDerivative_swap45 hu x c d a b e,
    coordinateFifthDerivative_swap34 hu x c d a e b]

lemma matrixDerivative_hessian_eq_third_first {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : CoordinateSpace n) (i : Fin n) :
    matrixCoordinateDerivative (coordinateHessian u) i x =
      (fun a b => coordinateThirdDerivative u x i a b) := by
  ext a b
  change coordinateThirdDerivative u x a b i = coordinateThirdDerivative u x i a b
  exact (coordinateThirdDerivative_cycle (contDiff_infty.mp hu 3) x a b i).trans
    (coordinateThirdDerivative_cycle (contDiff_infty.mp hu 3) x b i a)

lemma matrixSecondDerivative_hessian_eq_fourth_first {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : CoordinateSpace n) (i j : Fin n) :
    matrixCoordinateDerivative (fun y => matrixCoordinateDerivative (coordinateHessian u) i y) j x =
      (fun a b => coordinateFourthDerivative u x i j a b) := by
  ext a b
  exact coordinateFourthDerivative_pair_swap hu x a b i j

lemma matrixThirdDerivative_hessian_trace {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : CoordinateSpace n) (i j k : Fin n) :
    trace (matrixCoordinateDerivative (fun z => matrixCoordinateDerivative
      (fun y => matrixCoordinateDerivative (coordinateHessian u) i y) j z) k x) =
      ∑ l, coordinateFifthDerivative u x i j k l l := by
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro l _
  exact coordinateFifthDerivative_pair_cycle hu x l l i j k

/-- The twice differentiated determinant equation in normalized scalar tensor
indices, with the contraction of fourth derivatives on the left. -/
theorem constant_density_fourth_contraction {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1)
    (hI : coordinateHessian u x = 1) (i j : Fin n) :
    (∑ l, coordinateFourthDerivative u x i j l l) =
      ∑ a, ∑ b, coordinateThirdDerivative u x i a b * coordinateThirdDerivative u x j a b := by
  have hh := constant_density_adjugate_second_trace hu hMA i j
  rw [matrixSecondDerivative_hessian_eq_fourth_first hu,
    matrixDerivative_hessian_eq_third_first hu, matrixDerivative_hessian_eq_third_first hu,
    hI] at hh
  simp only [Matrix.adjugate_one, Matrix.one_mul, Matrix.mul_one] at hh
  change trace (fun a b => coordinateFourthDerivative u x i j a b) = _
  rw [hh]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [coordinateThirdDerivative_swap_last (contDiff_infty.mp hu 3) x i b a]
  ring

lemma trace_triple_reverse (A B C : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hB : B.IsSymm) (hC : C.IsSymm) :
    trace (A * B * C) = trace (C * B * A) := by
  calc
    _ = trace (A * B * C)ᵀ := (Matrix.trace_transpose _).symm
    _ = _ := by rw [Matrix.transpose_mul, Matrix.transpose_mul, hA.eq, hB.eq, hC.eq, Matrix.mul_assoc]

lemma trace_triple_expansion (A B C : Matrix (Fin n) (Fin n) ℝ) :
    trace (A * B * C) = ∑ a, ∑ b, ∑ c, A a b * B b c * C c a := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

/-- The fifth-derivative contraction is derived from three differentiations
of the genuine constant determinant equation. -/
theorem constant_density_fifth_contraction {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1)
    (hI : coordinateHessian u x = 1) (i j k : Fin n) :
    (∑ l, coordinateFifthDerivative u x i j k l l) =
      (∑ a, ∑ b, (coordinateFourthDerivative u x i j a b * coordinateThirdDerivative u x k a b +
        coordinateFourthDerivative u x i k a b * coordinateThirdDerivative u x j a b +
        coordinateFourthDerivative u x j k a b * coordinateThirdDerivative u x i a b)) -
      2 * ∑ a, ∑ b, ∑ c, coordinateThirdDerivative u x i a b *
        coordinateThirdDerivative u x j b c * coordinateThirdDerivative u x k c a := by
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
  have hh := constant_density_third_trace_at_identity hu hMA hI i j k
  dsimp only at hh
  rw [matrixThirdDerivative_hessian_trace hu] at hh
  rw [matrixSecondDerivative_hessian_eq_fourth_first hu x i j,
    matrixSecondDerivative_hessian_eq_fourth_first hu x j k,
    matrixSecondDerivative_hessian_eq_fourth_first hu x i k] at hh
  simp only [matrixDerivative_hessian_eq_third_first hu] at hh
  change _ = trace (T k * Q i j) + trace (Q j k * T i) + trace (T j * Q i k) -
    trace (T k * T j * T i) - trace (T j * T k * T i) at hh
  rw [Matrix.trace_mul_comm (Q j k) (T i), ht, ht, ht,
    trace_triple_reverse (T k) (T j) (T i) (hTs k) (hTs j) (hTs i),
    Matrix.trace_mul_cycle (T j) (T k) (T i), trace_triple_expansion] at hh
  rw [hh]
  simp only [Finset.sum_add_distrib]
  dsimp only [T]
  ring

end GaussianTilt.MomentMapRegularity
