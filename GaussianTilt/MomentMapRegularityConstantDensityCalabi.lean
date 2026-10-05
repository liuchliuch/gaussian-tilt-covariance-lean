import GaussianTilt.MomentMapRegularityConstantDensityEquation
import GaussianTilt.MomentMapCalabiTensor

/-!
# Actual derivative calculus for the Calabi cubic energy

The energy is defined from the actual inverse Hessian and actual third
coordinate derivatives. On a unit-density neighborhood the adjugate is the
inverse, allowing differentiation without any condition outside the domain.
-/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The literal cubic derivative energy in the inverse Hessian metric. -/
def calabiEnergy (u : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ i, ∑ j, ∑ k,
    (coordinateHessian u x)⁻¹ a i * (coordinateHessian u x)⁻¹ b j *
      (coordinateHessian u x)⁻¹ c k * coordinateThirdDerivative u x a b c *
      coordinateThirdDerivative u x i j k

/-- Fourth derivatives, with the final index recording the last differentiation. -/
def coordinateFourthDerivative (u : CoordinateSpace n → ℝ) (x : CoordinateSpace n)
    (a b c d : Fin n) : ℝ := coordinateDerivative d (fun y => coordinateThirdDerivative u y a b c) x

def coordinateFifthDerivative (u : CoordinateSpace n → ℝ) (x : CoordinateSpace n)
    (a b c d e : Fin n) : ℝ := coordinateDerivative e (fun y => coordinateFourthDerivative u y a b c d) x

lemma smooth_coordinateThirdDerivative {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (a b c : Fin n) :
    ContDiff ℝ ∞ (fun x => coordinateThirdDerivative u x a b c) :=
  smooth_coordinateDerivative (smooth_coordinateHessian hu a b) c

lemma smooth_coordinateFourthDerivative {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (a b c d : Fin n) :
    ContDiff ℝ ∞ (fun x => coordinateFourthDerivative u x a b c d) :=
  smooth_coordinateDerivative (smooth_coordinateThirdDerivative hu a b c) d

lemma smooth_hessian_adjugate {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (a b : Fin n) :
    ContDiff ℝ ∞ (fun x => (coordinateHessian u x).adjugate a b) :=
  contDiff_matrix_adjugate (smooth_coordinateHessian hu) a b

/-- First differentiation of the actual inverse Hessian, using its adjugate
on the genuine constant determinant neighborhood. -/
theorem constant_density_adjugate_first {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1) (i : Fin n) :
    matrixCoordinateDerivative (fun y => (coordinateHessian u y).adjugate) i x =
      -((coordinateHessian u x).adjugate * matrixCoordinateDerivative (coordinateHessian u) i x *
        (coordinateHessian u x).adjugate) := by
  let H := coordinateHessian u
  let K := fun y => (H y).adjugate
  have hH (a b : Fin n) : Differentiable ℝ (fun y => H y a b) :=
    (smooth_coordinateHessian hu a b).differentiable (by simp)
  have hK (a b : Fin n) : Differentiable ℝ (fun y => K y a b) :=
    (smooth_hessian_adjugate hu a b).differentiable (by simp)
  have hHK : H x * K x = 1 := by
    dsimp [K]
    rw [Matrix.mul_adjugate, hMA.self_of_nhds]
    simp
  have he : (fun y => K y * H y) =ᶠ[𝓝 x] (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    filter_upwards [hMA] with y hy
    dsimp [K, H]
    rw [Matrix.adjugate_mul, hy]
    simp
  have hz : matrixCoordinateDerivative (fun y => K y * H y) i x = 0 := by
    ext a b
    have hij := he.mono (fun y hy => congrFun (congrFun hy a) b)
    change coordinateDerivative i (fun y => (K y * H y) a b) x = 0
    rw [coordinateDerivative_congr_nhds hij i]
    simp [coordinateDerivative]
  rw [matrixCoordinateDerivative_mul hK hH] at hz
  have hh := congrArg (fun M => M * K x) hz
  dsimp only at hh
  rw [Matrix.add_mul, Matrix.mul_assoc, hHK, Matrix.mul_one, Matrix.zero_mul] at hh
  exact eq_neg_of_add_eq_zero_left hh

lemma matrixCoordinateDerivative_congr_nhds
    {F G : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {x : CoordinateSpace n}
    (h : F =ᶠ[𝓝 x] G) (i : Fin n) : matrixCoordinateDerivative F i x = matrixCoordinateDerivative G i x := by
  ext a b
  exact coordinateDerivative_congr_nhds (h.mono (fun y hy => congrFun (congrFun hy a) b)) i

lemma matrixCoordinateDerivative_neg (F : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (x : CoordinateSpace n) :
    matrixCoordinateDerivative (fun y => -F y) i x = -matrixCoordinateDerivative F i x := by
  ext a b
  exact coordinateDerivative_neg (fun y => F y a b) i x

/-- At a Hessian-normalized point, the second inverse derivative is the
actual quadratic third-derivative term minus the actual fourth derivative. -/
theorem constant_density_adjugate_second_at_identity {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1)
    (hI : coordinateHessian u x = 1) (i : Fin n) :
    matrixCoordinateDerivative
      (fun y => matrixCoordinateDerivative (fun z => (coordinateHessian u z).adjugate) i y) i x =
      (2 : ℝ) • (matrixCoordinateDerivative (coordinateHessian u) i x *
        matrixCoordinateDerivative (coordinateHessian u) i x) -
      matrixCoordinateDerivative (fun y => matrixCoordinateDerivative (coordinateHessian u) i y) i x := by
  let H := coordinateHessian u
  let K := fun y => (H y).adjugate
  let T := fun y => matrixCoordinateDerivative H i y
  have hK (a b : Fin n) : Differentiable ℝ (fun y => K y a b) :=
    (smooth_hessian_adjugate hu a b).differentiable (by simp)
  have hT (a b : Fin n) : Differentiable ℝ (fun y => T y a b) :=
    (smooth_coordinateThirdDerivative hu a b i).differentiable (by simp)
  have hKT (a b : Fin n) : Differentiable ℝ (fun y => (K y * T y) a b) := by
    simp only [Matrix.mul_apply]
    exact Differentiable.fun_sum (fun c _ => (hK a c).mul (hT c b))
  have he : (fun y => matrixCoordinateDerivative K i y) =ᶠ[𝓝 x]
      (fun y => -(K y * T y * K y)) := by
    filter_upwards [hMA.eventually_nhds] with y hy
    exact constant_density_adjugate_first hu hy i
  have hd := matrixCoordinateDerivative_congr_nhds he i
  rw [matrixCoordinateDerivative_neg, matrixCoordinateDerivative_mul hKT hK,
    matrixCoordinateDerivative_mul hK hT] at hd
  have hKx : K x = 1 := by dsimp [K, H]; rw [hI]; simp
  have hKi : matrixCoordinateDerivative K i x = -T x := by
    have hh := constant_density_adjugate_first hu hMA i
    change matrixCoordinateDerivative K i x = -(K x * T x * K x) at hh
    simpa only [hKx, Matrix.one_mul, Matrix.mul_one] using hh
  rw [hKx, hKi] at hd
  simp only [Matrix.one_mul, Matrix.mul_one] at hd
  rw [hd]
  change -((-T x * T x + matrixCoordinateDerivative T i x) + T x * -T x) = _
  simp only [Matrix.neg_mul, Matrix.mul_neg]
  module

lemma differentiable_matrix_mul_entries
    {A B : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ a b, Differentiable ℝ (fun y => A y a b))
    (hB : ∀ a b, Differentiable ℝ (fun y => B y a b)) :
    ∀ a b, Differentiable ℝ (fun y => (A y * B y) a b) := by
  intro a b
  simp only [Matrix.mul_apply]
  exact Differentiable.fun_sum (fun c _ => (hA a c).mul (hB c b))

/-- The actual mixed twice-differentiated determinant identity in matrix
coordinates, before commuting its fourth derivatives. -/
theorem constant_density_adjugate_second_trace {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1) (i j : Fin n) :
    trace ((coordinateHessian u x).adjugate *
      matrixCoordinateDerivative (fun y => matrixCoordinateDerivative (coordinateHessian u) i y) j x) =
    trace ((coordinateHessian u x).adjugate * matrixCoordinateDerivative (coordinateHessian u) j x *
      (coordinateHessian u x).adjugate * matrixCoordinateDerivative (coordinateHessian u) i x) := by
  let H := coordinateHessian u
  let K := fun y => (H y).adjugate
  let T := fun y => matrixCoordinateDerivative H i y
  have hK (a b : Fin n) : Differentiable ℝ (fun y => K y a b) :=
    (smooth_hessian_adjugate hu a b).differentiable (by simp)
  have hT (a b : Fin n) : Differentiable ℝ (fun y => T y a b) :=
    (smooth_coordinateThirdDerivative hu a b i).differentiable (by simp)
  have he : (fun y => trace (K y * T y)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hMA.eventually_nhds] with y hy
    have hh := constant_density_first_trace hu hy i
    rwa [matrix_inv_eq_adjugate_of_det_one hy.self_of_nhds] at hh
  have hd := coordinateDerivative_congr_nhds he j
  rw [coordinateDerivative_trace (differentiable_matrix_mul_entries hK hT),
    matrixCoordinateDerivative_mul hK hT, constant_density_adjugate_first hu hMA j] at hd
  simp only [Matrix.neg_mul, Matrix.trace_add, Matrix.trace_neg] at hd
  have hc : coordinateDerivative j (fun _ : CoordinateSpace n => (0 : ℝ)) x = 0 := by
    simp [coordinateDerivative]
  rw [hc] at hd
  change -_ + trace ((coordinateHessian u x).adjugate *
      matrixCoordinateDerivative (fun y => matrixCoordinateDerivative (coordinateHessian u) i y) j x) = 0 at hd
  dsimp only [K, T, H] at hd
  linarith

/-- The third differentiated constant determinant identity at a normalized
point. Every matrix on the right is an actual third or fourth derivative. -/
theorem constant_density_third_trace_at_identity {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1)
    (hI : coordinateHessian u x = 1) (i j k : Fin n) :
    let T := fun a => matrixCoordinateDerivative (coordinateHessian u) a x
    let Q := fun a b => matrixCoordinateDerivative
      (fun y => matrixCoordinateDerivative (coordinateHessian u) a y) b x
    trace (matrixCoordinateDerivative (fun z => matrixCoordinateDerivative
      (fun y => matrixCoordinateDerivative (coordinateHessian u) i y) j z) k x) =
      trace (T k * Q i j) + trace (Q j k * T i) + trace (T j * Q i k) -
        trace (T k * T j * T i) - trace (T j * T k * T i) := by
  let H := coordinateHessian u
  let K := fun y => (H y).adjugate
  let T := fun a y => matrixCoordinateDerivative H a y
  let Q := fun a b y => matrixCoordinateDerivative (T a) b y
  have hK (a b : Fin n) : Differentiable ℝ (fun y => K y a b) :=
    (smooth_hessian_adjugate hu a b).differentiable (by simp)
  have hT (d a b : Fin n) : Differentiable ℝ (fun y => T d y a b) :=
    (smooth_coordinateThirdDerivative hu a b d).differentiable (by simp)
  have hQ (c d a b : Fin n) : Differentiable ℝ (fun y => Q c d y a b) :=
    (smooth_coordinateFourthDerivative hu a b c d).differentiable (by simp)
  have he : (fun y => trace (K y * Q i j y)) =ᶠ[𝓝 x]
      (fun y => trace (K y * T j y * K y * T i y)) := by
    filter_upwards [hMA.eventually_nhds] with y hy
    exact constant_density_adjugate_second_trace hu hy i j
  have hd := coordinateDerivative_congr_nhds he k
  rw [coordinateDerivative_trace (differentiable_matrix_mul_entries hK (hQ i j)),
    coordinateDerivative_trace (differentiable_matrix_mul_entries
      (differentiable_matrix_mul_entries (differentiable_matrix_mul_entries hK (hT j)) hK) (hT i)),
    matrixCoordinateDerivative_mul hK (hQ i j),
    matrixCoordinateDerivative_mul
      (differentiable_matrix_mul_entries (differentiable_matrix_mul_entries hK (hT j)) hK) (hT i),
    matrixCoordinateDerivative_mul (differentiable_matrix_mul_entries hK (hT j)) hK,
    matrixCoordinateDerivative_mul hK (hT j), constant_density_adjugate_first hu hMA k] at hd
  have hKx : K x = 1 := by dsimp [K, H]; rw [hI]; simp
  change trace ((-(K x * T k x * K x)) * Q i j x + K x * matrixCoordinateDerivative (Q i j) k x) =
    trace ((((-(K x * T k x * K x)) * T j x + K x * Q j k x) * K x +
      (K x * T j x) * (-(K x * T k x * K x))) * T i x +
      (K x * T j x * K x) * Q i k x) at hd
  rw [hKx] at hd
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.add_mul, Matrix.trace_add, Matrix.trace_neg] at hd
  change trace (matrixCoordinateDerivative (Q i j) k x) = _
  dsimp only
  dsimp only [T, Q, H] at hd
  linarith

end GaussianTilt.MomentMapRegularity
