import GaussianTilt.Reference.Section3Statements
import GaussianTilt.UpperOriginalResults
import GaussianTilt.PaourisTiltedSpectral

/-! # Machine-checked bridges to the independent Section 3 targets

This is deliberately outside the Reference import tree. The targets are
unchanged pure propositions. The dependence on the isotropic quadratic
variance theorem is explicit until the analytic construction discharges
it; no definition or conditional implication is counted as an unconditional
paper theorem.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.L2Operator
namespace GaussianTilt.Reference

lemma momentAlong_eq_tiltedSecondMoment {n : ℕ} (μ : Measure (Space n)) (t : ℝ) :
    momentAlong μ t=tiltedSecondMoment μ t := rfl

lemma hilbertSchmidtAlong_eq_tiltedMomentHS {n : ℕ} (μ : Measure (Space n)) (t : ℝ) :
    hilbertSchmidtAlong μ t=tiltedMomentHS μ t := by
  simp only [hilbertSchmidtAlong,hilbertSchmidt,tiltedMomentHS,pow_two,momentAlong_eq_tiltedSecondMoment]

theorem theorem3_1_of_isotropic_bound (hL : IsotropicQuadraticVarianceBound) : Theorem3_1 :=
  upperBound_of_isotropic_bound hL

theorem lemma3_2_of_isotropic_bound (hL : IsotropicQuadraticVarianceBound) : Lemma3_2 := by
  intro n hn μ hμ hc hi hl t ht
  letI := hμ
  have h := original3_2_of_isotropic_bound hL hn μ hc hl hi ht
  have hd : DifferentiableAt ℝ (fun s => Real.log (hilbertSchmidtAlong μ s)) t := by
    obtain ⟨P,rfl⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported μ hc
    simpa only [hilbertSchmidtAlong_eq_tiltedMomentHS,tiltedMomentHS_compact] using
      (P.log_momentHS_hasDerivAt hi hn t).differentiableAt
  refine ⟨?_,hd,?_,?_⟩
  · simpa only [hilbertSchmidtAlong_eq_tiltedMomentHS] using h.1
  · simpa only [hilbertSchmidtAlong_eq_tiltedMomentHS,momentAlong_eq_tiltedSecondMoment] using h.2.1
  · simpa only [upperRightDini,GaussianTilt.UpperDynamics.UpperRightDiniLE,
      hilbertSchmidtAlong_eq_tiltedMomentHS,momentAlong_eq_tiltedSecondMoment] using h.2.2

theorem corollary3_3_of_isotropic_bound (hL : IsotropicQuadraticVarianceBound) : Corollary3_3 := by
  intro n hn μ hμ hc hi hl a b ha hab
  letI := hμ
  simpa only [hilbertSchmidtAlong_eq_tiltedMomentHS,momentAlong_eq_tiltedSecondMoment] using
    original3_3_of_isotropic_bound hL hn μ hc hl hi ha hab.le

/-- The independent exact Rényi comparison is unconditional. -/
theorem lemma3_4 : Lemma3_4 := by
  intro n μ hμ hc _hi _hl T q hT hq
  letI := hμ
  obtain ⟨he,hle⟩ := renyi_comparison_conjugate μ hc hT hq
  exact ⟨he,he ▸ hle⟩

/-- The independent projected trace/expectation statement is unconditional. -/
theorem lemma3_5 : Lemma3_5 := by
  refine ⟨GaussianTilt.Paouris.projectedTiltConstant,GaussianTilt.Paouris.projectedTiltConstant_pos,?_⟩
  intro n μ hμ hc hi hl T q hT hq P hP
  letI := hμ
  have hq2 : 2 ≤ q := (le_max_left _ _).trans hq
  have hHq : entropy (gaussianTilt μ T) μ ≤ q := (le_max_right _ _).trans hq
  obtain ⟨he,hle⟩ := projected_second_moment_estimate μ hc hl hi hT hq2 hHq P hP.1 hP.2
  exact ⟨he,he ▸ hle⟩

/-- One universal constant controls all three independent spectral conclusions. -/
theorem corollary3_6 : Corollary3_6 := by
  refine ⟨GaussianTilt.Paouris.spectralTiltConstant,GaussianTilt.Paouris.spectralTiltConstant_pos,?_⟩
  intro n μ hμ hc hi hl T q hT hq
  letI := hμ
  have hq2 : 2 ≤ q := (le_max_left _ _).trans hq
  have hHq : entropy (gaussianTilt μ T) μ ≤ q := (le_max_right _ _).trans hq
  obtain ⟨hA,he,hOp,hHS⟩ := earlier_time_spectral_profile μ hc hl hi hT hq2 hHq
  refine ⟨hA,?_,hOp,?_⟩
  · intro i
    apply (he i).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hp := GaussianTilt.Paouris.projectedTiltConstant_pos
    dsimp only [GaussianTilt.Paouris.spectralTiltConstant]
    linarith
  · simpa only [hilbertSchmidtAlong,hilbertSchmidt,momentAlong,secondMoment,pow_two,
      GaussianTilt.secondMomentMatrix] using hHS

theorem lemma3_7_of_isotropic_bound (hL : IsotropicQuadraticVarianceBound) : Lemma3_7 := by
  intro n hn μ hμ hc hi hl a b α β ha hab hα hβ hMa hSa hαtime hβtime s hs
  letI := hμ
  have h := original3_7_of_isotropic_bound hL hn μ hc hl hi ha hab.le hα hβ hMa
    (by simpa only [hilbertSchmidtAlong_eq_tiltedMomentHS] using hSa) hαtime hβtime s hs
  simpa only [momentAlong_eq_tiltedSecondMoment,hilbertSchmidtAlong_eq_tiltedMomentHS] using h

theorem lemma3_8_of_isotropic_bound (hL : IsotropicQuadraticVarianceBound) : Lemma3_8 := by
  obtain ⟨ε,Cstar,Csp,hε,hCstar,hCsp,h⟩ := original3_8_of_isotropic_bound hL
  refine ⟨ε,Cstar,Csp,hε,hCstar,hCsp,?_⟩
  intro n μ hμ hc hi hl T q hT hq hqn hTq
  simpa only [momentAlong_eq_tiltedSecondMoment,hilbertSchmidtAlong_eq_tiltedMomentHS] using
    h n μ hμ hc hl hi T q hT hq hqn hTq

theorem lemma3_9_of_isotropic_bound (hL : IsotropicQuadraticVarianceBound) : Lemma3_9 := by
  obtain ⟨c,C,κ,hc,hC,hκ,h⟩ := original3_9_and_3_10_of_isotropic_bound hL
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  refine ⟨c,κ,hc,hκ,N,?_⟩
  intro n hn μ hμ hcomp hi hl t ht
  exact (hN n hn μ hμ hcomp hl hi t ht).1

theorem proposition3_10_of_isotropic_bound (hL : IsotropicQuadraticVarianceBound) : Proposition3_10 := by
  obtain ⟨c,C,κ,hc,hC,hκ,h⟩ := original3_9_and_3_10_of_isotropic_bound hL
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  refine ⟨c,C,hc,by linarith,N,?_⟩
  intro n hn μ hμ hcomp hi hl t ht
  simpa only [momentAlong_eq_tiltedSecondMoment] using (hN n hn μ hμ hcomp hl hi t ht).2

/-- Exact simultaneous implication to all ten independent targets.
Only the displayed analytic premise remains; the proposition definitions
are not credited as proofs. -/
theorem section3_targets_of_isotropic_bound (hL : IsotropicQuadraticVarianceBound) :
    Theorem3_1 ∧ Lemma3_2 ∧ Corollary3_3 ∧ Lemma3_4 ∧ Lemma3_5 ∧
      Corollary3_6 ∧ Lemma3_7 ∧ Lemma3_8 ∧ Lemma3_9 ∧ Proposition3_10 :=
  ⟨theorem3_1_of_isotropic_bound hL,lemma3_2_of_isotropic_bound hL,
    corollary3_3_of_isotropic_bound hL,lemma3_4,lemma3_5,corollary3_6,
    lemma3_7_of_isotropic_bound hL,lemma3_8_of_isotropic_bound hL,
    lemma3_9_of_isotropic_bound hL,proposition3_10_of_isotropic_bound hL⟩

end GaussianTilt.Reference
