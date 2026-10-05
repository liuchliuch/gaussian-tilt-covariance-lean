import GaussianTilt.UpperNumberedProofs
import GaussianTilt.Section4StatementBridges
import GaussianTilt.Corollary410SourceAudit

/-! # Final proofs against the independent numbered specifications

Twenty-six literal printed targets are proved. The literal same-constant
Corollary 4.10 is refuted separately; its explicitly named constant-renaming
version is proved. No equivalence between the literal and corrected catalogs
is claimed, and the corrected catalog retains an explicit erratum.
-/
noncomputable section
universe u
namespace GaussianTilt.Reference

theorem numbered_target_proved (i : NumberedResult) (hi : i ≠ .corollary4_10) :
    NumberedTarget.{u} i := by
  cases i with
  | theorem1_1 => exact theorem1_1_proved
  | lemma2_1 => exact lemma2_1_proved
  | theorem2_2 => exact theorem2_2_proved
  | theorem2_3 => exact theorem2_3_proved
  | theorem2_4 => exact theorem2_4_proved
  | theorem2_5 => exact theorem2_5_proved
  | lemma2_6 => exact lemma2_6_proved
  | theorem3_1 => exact theorem3_1_proved
  | lemma3_2 => exact lemma3_2_proved
  | corollary3_3 => exact corollary3_3_proved
  | lemma3_4 => exact lemma3_4
  | lemma3_5 => exact lemma3_5
  | corollary3_6 => exact corollary3_6
  | lemma3_7 => exact lemma3_7_proved
  | lemma3_8 => exact lemma3_8_proved
  | lemma3_9 => exact lemma3_9_proved
  | proposition3_10 => exact proposition3_10_proved
  | theorem4_1 => exact theorem4_1
  | lemma4_2 => exact lemma4_2
  | theorem4_3 => exact theorem4_3
  | lemma4_4 => exact lemma4_4
  | lemma4_5 => exact lemma4_5
  | lemma4_6 => exact lemma4_6
  | lemma4_7 => exact lemma4_7
  | corollary4_8 => exact corollary4_8
  | lemma4_9 => exact lemma4_9
  | corollary4_10 => exact (hi rfl).elim

/-- Every target in the explicitly corrected catalog has an unconditional
proof. The sole changed target is visible in the catalog definition. -/
theorem all_numbered_statements_with_410_erratum : AllNumberedStatementsWith410Erratum.{u} := by
  intro i
  by_cases hi : i = .corollary4_10
  · subst i
    simpa only [NumberedTargetWith410Erratum,if_pos rfl] using corrected4_10
  · simpa only [NumberedTargetWith410Erratum,if_neg hi] using numbered_target_proved i hi

/-- The literal printed catalog is impossible because its 4.10 chain is
arithmetically false. This records the obstruction rather than concealing it. -/
theorem not_all_literal_numbered_statements : ¬ AllLiteralNumberedStatements.{u} := by
  intro h
  exact not_Literal410 (h .corollary4_10)

end GaussianTilt.Reference
