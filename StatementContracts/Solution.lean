import GaussianTilt

universe u
namespace GaussianTiltContracts
open GaussianTilt.Reference

theorem paper_theorem1_1 : Theorem1_1 := by
  exact numbered_target_proved .theorem1_1 (by decide)

theorem paper_lemma2_1 : Lemma2_1 := by
  exact numbered_target_proved .lemma2_1 (by decide)

theorem paper_theorem2_2 : Theorem2_2 := by
  exact numbered_target_proved .theorem2_2 (by decide)

theorem paper_theorem2_3 : Theorem2_3 := by
  exact numbered_target_proved .theorem2_3 (by decide)

theorem paper_theorem2_4 : Theorem2_4 := by
  exact numbered_target_proved .theorem2_4 (by decide)

theorem paper_theorem2_5 : Theorem2_5 := by
  exact numbered_target_proved .theorem2_5 (by decide)

theorem paper_lemma2_6 : Lemma2_6 := by
  exact numbered_target_proved .lemma2_6 (by decide)

theorem paper_theorem3_1 : Theorem3_1 := by
  exact numbered_target_proved .theorem3_1 (by decide)

theorem paper_lemma3_2 : Lemma3_2 := by
  exact numbered_target_proved .lemma3_2 (by decide)

theorem paper_corollary3_3 : Corollary3_3 := by
  exact numbered_target_proved .corollary3_3 (by decide)

theorem paper_lemma3_4 : Lemma3_4 := by
  exact numbered_target_proved .lemma3_4 (by decide)

theorem paper_lemma3_5 : Lemma3_5 := by
  exact numbered_target_proved .lemma3_5 (by decide)

theorem paper_corollary3_6 : Corollary3_6 := by
  exact numbered_target_proved .corollary3_6 (by decide)

theorem paper_lemma3_7 : Lemma3_7 := by
  exact numbered_target_proved .lemma3_7 (by decide)

theorem paper_lemma3_8 : Lemma3_8 := by
  exact numbered_target_proved .lemma3_8 (by decide)

theorem paper_lemma3_9 : Lemma3_9 := by
  exact numbered_target_proved .lemma3_9 (by decide)

theorem paper_proposition3_10 : Proposition3_10 := by
  exact numbered_target_proved .proposition3_10 (by decide)

theorem paper_theorem4_1 : Theorem4_1 := by
  exact numbered_target_proved .theorem4_1 (by decide)

theorem paper_lemma4_2 : Lemma4_2 := by
  exact numbered_target_proved .lemma4_2 (by decide)

theorem paper_theorem4_3 : Theorem4_3.{u} := by
  exact numbered_target_proved .theorem4_3 (by decide)

theorem paper_lemma4_4 : Lemma4_4 := by
  exact numbered_target_proved .lemma4_4 (by decide)

theorem paper_lemma4_5 : Lemma4_5 := by
  exact numbered_target_proved .lemma4_5 (by decide)

theorem paper_lemma4_6 : Lemma4_6 := by
  exact numbered_target_proved .lemma4_6 (by decide)

theorem paper_lemma4_7 : Lemma4_7 := by
  exact numbered_target_proved .lemma4_7 (by decide)

theorem paper_corollary4_8 : Corollary4_8 := by
  exact numbered_target_proved .corollary4_8 (by decide)

theorem paper_lemma4_9 : Lemma4_9 := by
  exact numbered_target_proved .lemma4_9 (by decide)

theorem corollary4_10_corrected : Corrected410 := corrected4_10

theorem literal4_10_false : ¬ Literal410 := not_Literal410

theorem corrected_catalog : AllNumberedStatementsWith410Erratum.{u} := all_numbered_statements_with_410_erratum

end GaussianTiltContracts
