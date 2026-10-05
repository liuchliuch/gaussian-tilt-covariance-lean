import GaussianTilt.Reference.PaperStatements

/-! # Independent observables used by the numbered paper statements

Only Mathlib and the independent PaperStatements specification are imported.
These are definitions, not assertions of any result in the paper. In
particular the Dini derivative uses the extended-real limsup so that an
unbounded difference quotient is not silently assigned a finite supremum.
-/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.L2Operator
namespace GaussianTilt.Reference

/-- The literal uncentered second-moment matrix. -/
def secondMoment {n : ℕ} (μ : Measure (Space n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j=>∫ x,x i*x j∂μ

/-- The paper's Hilbert--Schmidt convention on symmetric matrices. -/
def hilbertSchmidt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (Matrix.trace (A*A))

def momentAlong {n : ℕ} (μ : Measure (Space n)) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  secondMoment (gaussianTilt μ t)

def hilbertSchmidtAlong {n : ℕ} (μ : Measure (Space n)) (t : ℝ) : ℝ :=
  hilbertSchmidt (momentAlong μ t)

def entropyAlong {n : ℕ} (μ : Measure (Space n)) (t : ℝ) : ℝ :=
  entropy (gaussianTilt μ t) μ

/-- The actual upper-right Dini derivative; the change of variables z=t+h
is only notational and the value is allowed to be infinite. -/
def upperRightDini (f : ℝ→ℝ) (t : ℝ) : EReal :=
  Filter.limsup (fun z : ℝ=>(((z-t)⁻¹*(f z-f t) : ℝ) : EReal)) (𝓝[>] t)

/-- Every orthogonal projection is represented by its real symmetric,
idempotent matrix in the fixed Euclidean basis. -/
def orthogonalProjectionMatrix {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P.IsHermitian ∧ P*P=P

/-- Literal Euclidean quadratic form. -/
def quadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  x.ofLp ⬝ᵥ (A *ᵥ x.ofLp)

end GaussianTilt.Reference
