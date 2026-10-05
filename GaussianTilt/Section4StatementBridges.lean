import GaussianTilt.Reference.Section4Statements
import GaussianTilt.Section4DefinitionBridges

/-! # Proofs of the independent lower targets and the separated corrected 4.10

The pinned source and Literal410 are unchanged. The final theorem here
proves Corrected410 only, with c₁ and c₂ explicitly distinct and with every
fixed A above the universal threshold retained.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator
universe u
namespace GaussianTilt.Reference
open Lower

theorem theorem4_1 : Theorem4_1 := GaussianTilt.original4_1

theorem lemma4_2 : Lemma4_2 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp GaussianTilt.original4_2
  refine ⟨N,?_⟩
  intro d hd
  obtain ⟨hco,hcv,hin,hun,hprob,hm,hcov⟩ := hN d hd
  refine ⟨hco,hcv,hin,?_,hprob,hm,hcov⟩
  intro ε η p
  exact hun p ε η

theorem theorem4_3 : Theorem4_3.{u} := by
  intro Ω _m μ hμ Y hY hInd hIdent hmean σ hσ hvar hC v hv0 hv
  letI := hμ
  simpa only [one_sub_standardNormalCDF_eq] using
    GaussianTilt.CramerUniform.original4_3 Y hY hInd hIdent hmean hσ hvar hC hv0 hv

lemma Lower.rate_eq_rpow {d : ℕ} (hd : 0 < d) : Lower.rate d=(d:ℝ)^(1/5:ℝ) :=
  GaussianTilt.deviationScale_sq_div hd

lemma Lower.rate_neg_half_eq {d : ℕ} (hd : 0 < d) :
    (Lower.rate d)^(-1/2:ℝ)=(d:ℝ)^(-(1/10:ℝ)) := by
  rw [Lower.rate_eq_rpow hd,← Real.rpow_mul (Nat.cast_nonneg d)]
  norm_num

lemma Lower.rate_neg_two_eq {d : ℕ} (hd : 0 < d) :
    (Lower.rate d)^(-2:ℝ)=(d:ℝ)^(-2/5:ℝ) := by
  rw [Lower.rate_eq_rpow hd,← Real.rpow_mul (Nat.cast_nonneg d)]
  norm_num

theorem lemma4_4 : Lemma4_4 := by
  intro s₀ hs₀
  obtain ⟨c,C,hc,hC,h⟩ := GaussianTilt.UniformModerate.original4_4 hs₀
  obtain ⟨N,hN⟩ := eventually_atTop.mp (h.and (eventually_gt_atTop (0:ℕ)))
  refine ⟨c,C,hc,hC,N,?_⟩
  intro d hd s hs
  have hp := (hN d hd).2
  have hh := (hN d hd).1 s hs
  rw [Lower.rate_neg_half_eq hp,Lower.rate_eq_rpow hp]
  simpa only [Lower.squareVariance,show (2:ℝ)/(4/5)=5/2 by norm_num,
    sliceMass_eq_implementation] using hh

theorem lemma4_5 : Lemma4_5 := by
  intro d hd s hs
  simpa only [Lower.rate_eq_rpow hd,sliceMass_eq_implementation] using GaussianTilt.original4_5 hd hs

/-- One minimum/maximum choice makes both moment orders share the same
constants and the same dimensional threshold. -/
theorem lemma4_6 : Lemma4_6 := by
  obtain ⟨c0,C0,hc0,hC0,h0⟩ := GaussianTilt.original4_6 0
  obtain ⟨c2,C2,hc2,hC2,h2⟩ := GaussianTilt.original4_6 2
  obtain ⟨N,hN⟩ := eventually_atTop.mp (h0.and h2)
  refine ⟨min c0 c2,max C0 C2,lt_min hc0 hc2,hC0.trans_le (le_max_left _ _),N,?_⟩
  intro d hd ℓ hℓ
  have hmass : 0 ≤ Lower.sliceMass d 0 := measureReal_nonneg
  have hrate : 0 ≤ Lower.rate d := by unfold Lower.rate; positivity
  have weaken (c C : ℝ) (hcl : min c0 c2 ≤ c) (hCu : C ≤ max C0 C2)
      (hh : c*Lower.sliceMass d 0/(Lower.rate d)^(ℓ+1) ≤ Lower.sliceMoment d ℓ ∧
        Lower.sliceMoment d ℓ ≤ C*Lower.sliceMass d 0/(Lower.rate d)^(ℓ+1)) :
      min c0 c2*Lower.sliceMass d 0/(Lower.rate d)^(ℓ+1) ≤ Lower.sliceMoment d ℓ ∧
        Lower.sliceMoment d ℓ ≤ max C0 C2*Lower.sliceMass d 0/(Lower.rate d)^(ℓ+1) := by
    exact ⟨(div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcl hmass) (pow_nonneg hrate _)).trans hh.1,
      hh.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCu hmass) (pow_nonneg hrate _))⟩
  rcases hℓ with rfl | rfl
  · exact weaken c0 C0 (min_le_left _ _) (le_max_left _ _) (hN d hd).1
  · exact weaken c2 C2 (min_le_right _ _) (le_max_right _ _) (hN d hd).2

theorem lemma4_7 : Lemma4_7 := by
  obtain ⟨c,C,hc,hC,h⟩ := GaussianTilt.original4_7
  obtain ⟨N,hN⟩ := eventually_atTop.mp (h.and (eventually_gt_atTop (0:ℕ)))
  refine ⟨c,C,hc,hC,N,?_⟩
  intro d hd
  obtain ⟨ht,he,hlo,hup⟩ := (hN d hd).1
  have hd0 := (hN d hd).2
  have hscale : (Lower.rate d)^(-2:ℝ)=((d:ℝ)^(2/5:ℝ))⁻¹ := by
    rw [Lower.rate_neg_two_eq hd0,show (-2/5:ℝ)=-(2/5:ℝ) by ring,Real.rpow_neg (Nat.cast_nonneg d)]
  refine ⟨?_,?_,?_,?_,Lower.rate_neg_two_eq hd0⟩
  · simpa only [transverseVariance_eq_implementation] using ht
  · simpa only [axialVariance_eq_implementation,sliceMoment_eq_implementation,pow_zero,one_mul] using he
  · simpa only [axialVariance_eq_implementation,hscale,div_eq_mul_inv] using hlo
  · simpa only [axialVariance_eq_implementation,hscale,div_eq_mul_inv] using hup

theorem corollary4_8 : Corollary4_8 := by
  obtain ⟨c,C,hc,hC,h⟩ := GaussianTilt.original4_8
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (h.and (GaussianTilt.eventually_rawBody_parameters.and (eventually_gt_atTop (0:ℕ))))
  refine ⟨c,C,hc,hC,N,?_⟩
  intro d hd i
  obtain ⟨hbody,hunc,hiso,hlo,hup,hinv⟩ := (hN d hd).1 i
  have hpar := (hN d hd).2.1
  have hd0 := (hN d hd).2.2
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [isotropicBody_eq_implementation] using hbody
  · simpa only [isotropicBody_eq_implementation] using hunc
  · simpa only [isotropicBody_eq_implementation] using hiso
  · simpa only [axialVariance_eq_implementation,Lower.rate_eq_rpow hd0] using hlo
  · simpa only [axialVariance_eq_implementation,Lower.rate_eq_rpow hd0] using hup
  · simpa only [inverseIsotropization_eq_implementation,isotropization_eq_implementation] using hinv
  · intro p
    rw [isotropization_eq_implementation,inverseIsotropization_eq_implementation,
      GaussianTilt.diagonalScale_comp,
      inv_mul_cancel₀ (Real.sqrt_pos.mpr (GaussianTilt.rawTransverseVariance_pos hpar.1 hpar.2 i)).ne',
      inv_mul_cancel₀ (Real.sqrt_pos.mpr (GaussianTilt.rawAxialVariance_pos hpar.1 hpar.2)).ne',
      GaussianTilt.diagonalScale_one]

/-- The exact infimum form follows from the pointwise all-window theorem;
the window is genuinely nonempty (it contains zero). -/
theorem lemma4_9 : Lemma4_9 := by
  obtain ⟨A₀,hA₀,hacc⟩ := GaussianTilt.original4_9
  refine ⟨A₀,hA₀,?_⟩
  intro A hA
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hacc A ((le_max_right _ _).trans hA))
  refine ⟨N,?_⟩
  intro d hd i
  have hexp : Real.exp (-2*Lower.rate d/9)=
      Real.exp (-2*GaussianTilt.deviationScale d^2/(9*(d:ℝ))) := by
    congr 1
    unfold Lower.rate
    change -2*(GaussianTilt.deviationScale d^2/(d:ℝ))/9=_
    ring
  have hzero : |(0:ℝ)|≤(Real.sqrt (Lower.precision d A))⁻¹ := by simpa only [abs_zero] using inv_nonneg.mpr (Real.sqrt_nonneg (Lower.precision d A))
  have hz := hN d hd i 0 hzero
  refine ⟨?_,?_⟩
  · apply le_csInf ⟨Lower.acceptance i A 0,mem_image_of_mem _ hzero⟩
    rintro z ⟨y,hy,rfl⟩
    rw [hexp,acceptance_eq_implementation]
    exact (hN d hd i y hy).1
  · rw [hexp]
    exact hz.2

/-- All fixed sufficiently large A, with the explicit c₂=c₁/A conversion.
This theorem does not assert the incompatible literal same-c chain. -/
theorem corrected4_10 : Corrected410 := by
  obtain ⟨A₀,hA₀,h⟩ := GaussianTilt.every_fixed_precision_axial_variance
  refine ⟨A₀,hA₀,?_⟩
  intro A hA
  obtain ⟨hc₂,hevent⟩ := h A ((le_max_right _ _).trans hA)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  refine ⟨GaussianTilt.LowerMarginal.windowConstant,GaussianTilt.LowerMarginal.windowConstant/A,
    GaussianTilt.LowerMarginal.windowConstant_pos,hc₂,N,?_⟩
  intro d hd i
  obtain ⟨_ht,hm,hv,he⟩ := hN d hd i
  refine ⟨?_,?_,?_⟩
  · simpa only [isotropicBody_eq_implementation,precision_eq_implementation,axialMarginal_eq_implementation] using hm
  · simpa only [precision_eq_implementation,axialTiltVariance_eq_implementation] using hv
  · exact he.symm.le

/-- All nine uncontroversial literal Section 4 targets, proved against
independent definitions rather than implementation aliases. -/
theorem section4_literal_targets_through_4_9 :
    Theorem4_1 ∧ Lemma4_2 ∧ Theorem4_3.{u} ∧ Lemma4_4 ∧ Lemma4_5 ∧
      Lemma4_6 ∧ Lemma4_7 ∧ Corollary4_8 ∧ Lemma4_9 :=
  ⟨theorem4_1,lemma4_2,theorem4_3,lemma4_4,lemma4_5,lemma4_6,lemma4_7,corollary4_8,lemma4_9⟩

/-- The corrected lower package is deliberately distinct from the literal
Corollary4_10 target. -/
theorem section4_targets_with_separate_correction :
    Theorem4_1 ∧ Lemma4_2 ∧ Theorem4_3.{u} ∧ Lemma4_4 ∧ Lemma4_5 ∧
      Lemma4_6 ∧ Lemma4_7 ∧ Corollary4_8 ∧ Lemma4_9 ∧ Corrected410 :=
  ⟨theorem4_1,lemma4_2,theorem4_3,lemma4_4,lemma4_5,lemma4_6,lemma4_7,corollary4_8,lemma4_9,corrected4_10⟩

end GaussianTilt.Reference
