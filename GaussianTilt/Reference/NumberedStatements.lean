import GaussianTilt.Reference.Section2Statements
import GaussianTilt.Reference.Section3Statements
import GaussianTilt.Reference.Section4Statements

/-! # Independent specification of all 27 active numbered paper results

The transitive imports are Mathlib and independent Reference definitions
only. No implementation or proof of a numbered result is imported. The
commented annealing material and the nonexistent appendix are excluded.
`NumberedTarget` retains the literal printed Corollary 4.10; the separately
named erratum catalog changes only that target and keeps its scope separate. Compilation of this index is not proof coverage.
-/
noncomputable section
open MeasureTheory Set
open scoped Matrix.Norms.L2Operator
universe u
namespace GaussianTilt.Reference

/-- Theorem 1.1, pinned source lines 282–309. The constants c and C are
chosen before the dimension and the measure; the lower threshold precedes
its dimension. The actual supremum asymptotic conclusion is retained. -/
def Theorem1_1 : Prop := ∃ c C : ℝ,0<c ∧ 0<C ∧
  (∀ n : ℕ,∀ μ : Measure (Space n),IsProbabilityMeasure μ → compactlySupported μ →
    isotropic μ → logconcave μ → ∀ t : ℝ,0≤t →
      ‖covariance (gaussianTilt μ t)‖≤C*(n:ℝ)^(2/5:ℝ)) ∧
  (∃ n₀ : ℕ,∀ n≥n₀,∃ K : Set (Space n),∃ t : ℝ,
    convexBody K ∧ unconditional K ∧ isotropic (uniform K) ∧ 0<t ∧
      c*(n:ℝ)^(2/5:ℝ)≤‖covariance (gaussianTilt (uniform K) t)‖) ∧
  SharpScale

/-- Exactly the active numbered results, in paper order. -/
inductive NumberedResult
  | theorem1_1
  | lemma2_1 | theorem2_2 | theorem2_3 | theorem2_4 | theorem2_5 | lemma2_6
  | theorem3_1 | lemma3_2 | corollary3_3 | lemma3_4 | lemma3_5 | corollary3_6
  | lemma3_7 | lemma3_8 | lemma3_9 | proposition3_10
  | theorem4_1 | lemma4_2 | theorem4_3 | lemma4_4 | lemma4_5 | lemma4_6 | lemma4_7
  | corollary4_8 | lemma4_9 | corollary4_10
  deriving DecidableEq, Fintype

/-- The literal independent proposition for each numbered result. -/
def NumberedTarget : NumberedResult→Prop
  | .theorem1_1=>Theorem1_1
  | .lemma2_1=>Lemma2_1
  | .theorem2_2=>Theorem2_2
  | .theorem2_3=>Theorem2_3
  | .theorem2_4=>Theorem2_4
  | .theorem2_5=>Theorem2_5
  | .lemma2_6=>Lemma2_6
  | .theorem3_1=>Theorem3_1
  | .lemma3_2=>Lemma3_2
  | .corollary3_3=>Corollary3_3
  | .lemma3_4=>Lemma3_4
  | .lemma3_5=>Lemma3_5
  | .corollary3_6=>Corollary3_6
  | .lemma3_7=>Lemma3_7
  | .lemma3_8=>Lemma3_8
  | .lemma3_9=>Lemma3_9
  | .proposition3_10=>Proposition3_10
  | .theorem4_1=>Theorem4_1
  | .lemma4_2=>Lemma4_2
  | .theorem4_3=>Theorem4_3.{u}
  | .lemma4_4=>Lemma4_4
  | .lemma4_5=>Lemma4_5
  | .lemma4_6=>Lemma4_6
  | .lemma4_7=>Lemma4_7
  | .corollary4_8=>Corollary4_8
  | .lemma4_9=>Lemma4_9
  | .corollary4_10=>Corollary4_10

/-- This optional catalog changes only the explicitly disclosed 4.10
constant/scope erratum. It is not the literal-source catalog. -/
def NumberedTargetWith410Erratum (i : NumberedResult) : Prop :=
  if i=.corollary4_10 then Corrected410 else NumberedTarget.{u} i

def AllLiteralNumberedStatements : Prop := ∀ i,NumberedTarget.{u} i

def AllNumberedStatementsWith410Erratum : Prop := ∀ i,NumberedTargetWith410Erratum.{u} i

/-- This checks the inventory size only, not any numbered mathematical claim. -/
theorem numberedResult_count : Fintype.card NumberedResult=27 := by decide

end GaussianTilt.Reference
