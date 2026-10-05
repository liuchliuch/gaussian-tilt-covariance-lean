import GaussianTilt.Reference.NumberedStatements
import GaussianTilt.OriginalAnalyticClosure
import GaussianTilt.Section2StatementBridges
import GaussianTilt.Section3StatementBridges

/-! # Unconditional proofs of the independent main, analytic and upper targets

Every target is imported from the independent Reference tree. All former
analytic callbacks are instantiated by the constructed classical/source
chain, and none appears as a hypothesis below.
-/
noncomputable section
namespace GaussianTilt.Reference

theorem theorem1_1_proved : Theorem1_1 := by
  obtain ⟨C,hC,hupper⟩ := proved_original_upper_bound
  obtain ⟨c,hc,n₀,hlower⟩ := GaussianTilt.original4_1
  exact ⟨c,C,hc,hC,hupper,⟨n₀,hlower⟩,proved_original_sharp_scale⟩

theorem theorem2_2_proved : Theorem2_2 :=
  theorem2_2_of_isotropic_bound proved_isotropicQuadraticVarianceBound

theorem lemma2_6_proved : Lemma2_6 :=
  lemma2_6_of_isotropic_bound proved_isotropicQuadraticVarianceBound

theorem theorem3_1_proved : Theorem3_1 :=
  theorem3_1_of_isotropic_bound proved_isotropicQuadraticVarianceBound

theorem lemma3_2_proved : Lemma3_2 :=
  lemma3_2_of_isotropic_bound proved_isotropicQuadraticVarianceBound

theorem corollary3_3_proved : Corollary3_3 :=
  corollary3_3_of_isotropic_bound proved_isotropicQuadraticVarianceBound

theorem lemma3_7_proved : Lemma3_7 :=
  lemma3_7_of_isotropic_bound proved_isotropicQuadraticVarianceBound

theorem lemma3_8_proved : Lemma3_8 :=
  lemma3_8_of_isotropic_bound proved_isotropicQuadraticVarianceBound

theorem lemma3_9_proved : Lemma3_9 :=
  lemma3_9_of_isotropic_bound proved_isotropicQuadraticVarianceBound

theorem proposition3_10_proved : Proposition3_10 :=
  proposition3_10_of_isotropic_bound proved_isotropicQuadraticVarianceBound

end GaussianTilt.Reference
