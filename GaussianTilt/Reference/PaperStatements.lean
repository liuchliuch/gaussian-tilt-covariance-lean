import Mathlib

/-!
# Independent statement specification for the main paper claims

This module imports no solution module. Its declarations are definitions of
propositions, not proofs of those propositions. In particular no theorem or
axiom is introduced for the paper's main bound.

Logconcavity is specified by a nonnegative Lebesgue density satisfying the
standard multiplicative concavity inequality. Isotropy rules out support in a
proper affine subspace. Covariance uses the actual integrals, and its norm is
explicitly the Euclidean operator norm.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Matrix.Norms.L2Operator

namespace GaussianTilt.Reference

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def compactlySupported {n : ℕ} (μ : Measure (Space n)) : Prop :=
  ∃ K : Set (Space n), IsCompact K ∧ μ Kᶜ = 0

def logconcaveDensity {n : ℕ} (f : Space n → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ Measurable f ∧
    ∀ x y : Space n, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      (f x) ^ a * (f y) ^ b ≤ f (a • x + b • y)

def logconcave {n : ℕ} (μ : Measure (Space n)) : Prop :=
  ∃ f : Space n → ℝ, logconcaveDensity f ∧
    μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x))

def mean {n : ℕ} (μ : Measure (Space n)) : Space n := ∫ x, x ∂μ

def covariance {n : ℕ} (μ : Measure (Space n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (∫ x, x i * x j ∂μ) - (∫ x, x i ∂μ) * (∫ x, x j ∂μ)

def isotropic {n : ℕ} (μ : Measure (Space n)) : Prop :=
  mean μ = 0 ∧ covariance μ = 1

def partition {n : ℕ} (μ : Measure (Space n)) (t : ℝ) : ℝ :=
  ∫ x, Real.exp (-t * ‖x‖ ^ 2) ∂μ

def gaussianTilt {n : ℕ} (μ : Measure (Space n)) (t : ℝ) : Measure (Space n) :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-t * ‖x‖ ^ 2) / partition μ t))

def logPartition {n : ℕ} (μ : Measure (Space n)) (t : ℝ) : ℝ :=
  Real.log (partition μ t)

def observableCovariance {n : ℕ} (μ : Measure (Space n)) (f g : Space n → ℝ) : ℝ :=
  (∫ x, f x * g x ∂μ) - (∫ x, f x ∂μ) * (∫ x, g x ∂μ)

def observableVariance {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  observableCovariance μ f f

def renyi {n : ℕ} (r : ℝ) (ν μ : Measure (Space n)) : ℝ :=
  Real.log (∫ x, (ν.rnDeriv μ x).toReal ^ r ∂μ) / (r - 1)

def entropy {n : ℕ} (ν μ : Measure (Space n)) : ℝ :=
  ∫ x, Real.log ((ν.rnDeriv μ x).toReal) ∂ν

def uniform {n : ℕ} (K : Set (Space n)) : Measure (Space n) :=
  (volume K)⁻¹ • volume.restrict K

def convexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

def unconditional {n : ℕ} (K : Set (Space n)) : Prop :=
  ∀ x ∈ K, ∀ ε : Fin n → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) →
    (WithLp.toLp 2 (fun i ↦ ε i * x i) : Space n) ∈ K

/-- Theorem 1.1(i), equivalently Theorem 3.1. -/
def UpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ μ : Measure (Space n),
    IsProbabilityMeasure μ → compactlySupported μ → isotropic μ → logconcave μ →
    ∀ t : ℝ, 0 ≤ t → ‖covariance (gaussianTilt μ t)‖ ≤ C * (n : ℝ) ^ (2 / 5 : ℝ)

/-- Theorem 1.1(ii), equivalently Theorem 4.1. -/
def LowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ K : Set (Space n), ∃ t : ℝ,
      convexBody K ∧ unconditional K ∧ isotropic (uniform K) ∧ 0 < t ∧
      c * (n : ℝ) ^ (2 / 5 : ℝ) ≤ ‖covariance (gaussianTilt (uniform K) t)‖

/-- Equation (2): the supremum over all isotropic convex bodies and positive tilts. -/
def inflationSupremum (n : ℕ) : ℝ :=
  sSup {v : ℝ | ∃ K : Set (Space n), ∃ t : ℝ,
    convexBody K ∧ isotropic (uniform K) ∧ 0 < t ∧
      v = ‖covariance (gaussianTilt (uniform K) t)‖}

/-- The asymptotic conclusion in Theorem 1.1. -/
def SharpScale : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    c * (n : ℝ) ^ (2 / 5 : ℝ) ≤ inflationSupremum n ∧
      inflationSupremum n ≤ C * (n : ℝ) ^ (2 / 5 : ℝ)

end GaussianTilt.Reference
