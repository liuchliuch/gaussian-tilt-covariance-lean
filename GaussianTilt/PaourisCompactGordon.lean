import GaussianTilt.PaourisFiniteGordon

/-!
# Rectangular and compact-index Gaussian comparison

Finite rectangular processes are realized as actual continuous linear images
of the radial Gaussian law. This connects the finite row-partition comparison
to the min/max indexing used in Gordon's theorem.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris

variable {d r c : ℕ}

def rectangleRow (j : Fin (r * c)) : Fin r := (finProdFinEquiv.symm j).1

lemma rectangleRow_surjective [NeZero c] : Function.Surjective (rectangleRow (r := r) (c := c)) := by
  intro i
  exact ⟨finProdFinEquiv (i, ⟨0, NeZero.pos c⟩), by simp [rectangleRow]⟩

/-- Linear image whose coordinates are the specified finite Gaussian process. -/
def rectangleProcessMap (a : Fin r → Fin c → Reference.Space d) :
    Reference.Space d →L[ℝ] Reference.Space (r * c) :=
  (EuclideanSpace.equiv (Fin (r * c)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j ↦ innerSL ℝ (a (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2))

@[simp] lemma rectangleProcessMap_apply (a : Fin r → Fin c → Reference.Space d)
    (x : Reference.Space d) (j : Fin (r * c)) :
    rectangleProcessMap a x j = ⟪a (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2, x⟫_ℝ := rfl

lemma rectangle_rowMaximum [NeZero c] (a : Fin r → Fin c → Reference.Space d)
    (x : Reference.Space d) (i : Fin r) :
    rowMaximum rectangleRow rectangleRow_surjective (rectangleProcessMap a x) i =
      ⨆ j : Fin c, ⟪a i j, x⟫_ℝ := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro j hj
    have hji := (Finset.mem_filter.mp hj).2
    change (finProdFinEquiv.symm j).1 = i at hji
    rw [rectangleProcessMap_apply, hji]
    exact le_ciSup (Finite.bddAbove_range (fun l : Fin c ↦ ⟪a i l, x⟫_ℝ)) (finProdFinEquiv.symm j).2
  · apply ciSup_le
    intro j
    have h := coordinate_le_rowMaximum rectangleRow rectangleRow_surjective
      (rectangleProcessMap a x) (finProdFinEquiv (i, j))
    simpa [rectangleRow] using h

lemma rectangle_finiteMinMax [NeZero r] [NeZero c]
    (a : Fin r → Fin c → Reference.Space d) (x : Reference.Space d) :
    finiteMinMax rectangleRow rectangleRow_surjective (rectangleProcessMap a x) =
      ⨅ i : Fin r, ⨆ j : Fin c, ⟪a i j, x⟫_ℝ := by
  unfold finiteMinMax
  simp_rw [rectangle_rowMaximum]
  exact Finset.inf'_univ_eq_ciInf _

lemma rectangle_incrementVariance (a : Fin r → Fin c → Reference.Space d)
    (i j : Fin (r * c)) :
    incrementVariance (rectangleProcessMap a) i j =
      ‖a (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 -
        a (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2‖ ^ 2 := by
  simp only [incrementVariance, rectangleProcessMap_apply, coordinateVector,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right,
    RCLike.star_def, RCLike.conj_to_real, one_mul, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs, PiLp.sub_apply, sq_abs]

/-- Finite rectangular Gordon comparison, now stated directly in the usual
minimum/maximum process notation with deterministic covariance-distance
conditions on its coefficient vectors. -/
theorem finite_rectangular_gordon [NeZero r] [NeZero c]
    (a b : Fin r → Fin c → Reference.Space d)
    (hsep : ∀ l : Fin d, (∀ i j, a i j l = 0) ∨ (∀ i j, b i j l = 0))
    (hwithin : ∀ i j j', ‖a i j - a i j'‖ ^ 2 ≤ ‖b i j - b i j'‖ ^ 2)
    (hcross : ∀ i i', i ≠ i' → ∀ j j', ‖b i j - b i' j'‖ ^ 2 ≤ ‖a i j - a i' j'‖ ^ 2) :
    (∫ x, ⨅ i : Fin r, ⨆ j : Fin c, ⟪a i j, x⟫_ℝ ∂standardGaussian d) ≤
      ∫ x, ⨅ i : Fin r, ⨆ j : Fin c, ⟪b i j, x⟫_ℝ ∂standardGaussian d := by
  have h := finite_gordon_comparison rectangleRow rectangleRow_surjective
    (rectangleProcessMap a) (rectangleProcessMap b) ?_ ?_ ?_
  · simpa only [gaussianExpectation, rectangle_finiteMinMax] using h
  · intro l
    rcases hsep l with ha | hb
    · left
      ext j
      simpa [coordinateVector, EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_right] using ha (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
    · right
      ext j
      simpa [coordinateVector, EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_right] using hb (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  · intro i j hij
    change (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1 at hij
    simp only [rectangle_incrementVariance, hij]
    exact hwithin _ _ _
  · intro i j hij
    change (finProdFinEquiv.symm i).1 ≠ (finProdFinEquiv.symm j).1 at hij
    simp only [rectangle_incrementVariance]
    exact hcross _ _ hij _ _

section GeneralIndices

variable {U V : Type*} [Nonempty U] [Nonempty V]

/-- The min/max observable for an indexed family of Gaussian coefficients. -/
def processMinMax (a : U → V → Reference.Space d) (x : Reference.Space d) : ℝ :=
  ⨅ u : U, ⨆ v : V, ⟪a u v, x⟫_ℝ

lemma process_inner_abs_le (a : U → V → Reference.Space d) {M : ℝ}
    (hM : ∀ u v, ‖a u v‖ ≤ M) (x : Reference.Space d) (u : U) (v : V) :
    |⟪a u v, x⟫_ℝ| ≤ M * ‖x‖ :=
  (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM u v) (norm_nonneg _))

lemma process_row_bddAbove (a : U → V → Reference.Space d) {M : ℝ}
    (hM : ∀ u v, ‖a u v‖ ≤ M) (x : Reference.Space d) (u : U) :
    BddAbove (range (fun v ↦ ⟪a u v, x⟫_ℝ)) := by
  refine ⟨M * ‖x‖, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact (le_abs_self _).trans (process_inner_abs_le a hM x u v)

lemma process_row_bounds (a : U → V → Reference.Space d) {M : ℝ}
    (hM : ∀ u v, ‖a u v‖ ≤ M) (x : Reference.Space d) (u : U) :
    -(M * ‖x‖) ≤ (⨆ v : V, ⟪a u v, x⟫_ℝ) ∧
      (⨆ v : V, ⟪a u v, x⟫_ℝ) ≤ M * ‖x‖ := by
  refine ⟨?_, ciSup_le (fun v ↦ (le_abs_self _).trans (process_inner_abs_le a hM x u v))⟩
  let v : V := Classical.arbitrary V
  apply le_ciSup_of_le (process_row_bddAbove a hM x u) v
  have h := (abs_le.mp (process_inner_abs_le a hM x u v)).1
  exact h

lemma process_rows_bddBelow (a : U → V → Reference.Space d) {M : ℝ}
    (hM : ∀ u v, ‖a u v‖ ≤ M) (x : Reference.Space d) :
    BddBelow (range (fun u ↦ ⨆ v : V, ⟪a u v, x⟫_ℝ)) := by
  refine ⟨-(M * ‖x‖), ?_⟩
  rintro _ ⟨u, rfl⟩
  exact (process_row_bounds a hM x u).1

lemma processMinMax_bounds (a : U → V → Reference.Space d) {M : ℝ}
    (hM : ∀ u v, ‖a u v‖ ≤ M) (x : Reference.Space d) :
    -(M * ‖x‖) ≤ processMinMax a x ∧ processMinMax a x ≤ M * ‖x‖ := by
  refine ⟨le_ciInf fun u ↦ (process_row_bounds a hM x u).1, ?_⟩
  exact ciInf_le_of_le (process_rows_bddBelow a hM x) (Classical.arbitrary U)
    (process_row_bounds a hM x _).2

lemma processMinMax_le_add (a : U → V → Reference.Space d) {M : ℝ}
    (hM : ∀ u v, ‖a u v‖ ≤ M) (x y : Reference.Space d) {ε : ℝ}
    (hxy : ∀ u v, ⟪a u v, x⟫_ℝ ≤ ⟪a u v, y⟫_ℝ + ε) :
    processMinMax a x ≤ processMinMax a y + ε := by
  unfold processMinMax
  rw [ciInf_add (process_rows_bddBelow a hM y)]
  apply le_ciInf
  intro u
  apply (ciInf_le (process_rows_bddBelow a hM x) u).trans
  apply ciSup_le
  intro v
  exact (hxy u v).trans (add_le_add_right
    (le_ciSup (process_row_bddAbove a hM y u) v) ε)

/-- Bounded coefficient families define Lipschitz min/max observables,
including when their index sets are infinite. -/
theorem processMinMax_lipschitz (a : U → V → Reference.Space d) {M : ℝ≥0}
    (hM : ∀ u v, ‖a u v‖ ≤ M) : LipschitzWith M (processMinMax a) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  rw [Real.norm_eq_abs]
  have hxy : processMinMax a x ≤ processMinMax a y + (M : ℝ) * ‖x - y‖ := by
    apply processMinMax_le_add a hM x y
    intro u v
    have h := process_inner_abs_le a hM (x - y) u v
    rw [inner_sub_right] at h
    have hh := le_abs_self (⟪a u v, x⟫_ℝ - ⟪a u v, y⟫_ℝ)
    linarith
  have hyx : processMinMax a y ≤ processMinMax a x + (M : ℝ) * ‖x - y‖ := by
    apply processMinMax_le_add a hM y x
    intro u v
    have h := process_inner_abs_le a hM (x - y) u v
    rw [inner_sub_right] at h
    have hh := neg_le_abs (⟪a u v, x⟫_ℝ - ⟪a u v, y⟫_ℝ)
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma processMinMax_gaussian_integrable (a : U → V → Reference.Space d) {M : ℝ≥0}
    (hM : ∀ u v, ‖a u v‖ ≤ M) : Integrable (processMinMax a) (standardGaussian d) := by
  simpa using gaussian_linear_image_integrable (processMinMax_lipschitz a hM)
    (ContinuousLinearMap.id ℝ (Reference.Space d))

/-- A finite column net approximates the full supremum for any retained row. -/
lemma processMinMax_le_sample_add [NeZero r] [NeZero c]
    (a : U → V → Reference.Space d) {M ε : ℝ}
    (hM : ∀ u v, ‖a u v‖ ≤ M) (I : Fin r → U) (J : Fin c → V)
    (hJ : ∀ v, ∃ j, ∀ u, ‖a u v - a u (J j)‖ ≤ ε) (x : Reference.Space d) :
    processMinMax a x ≤ processMinMax (fun i j ↦ a (I i) (J j)) x + ε * ‖x‖ := by
  unfold processMinMax
  rw [ciInf_add (process_rows_bddBelow (fun i j ↦ a (I i) (J j)) (fun i j ↦ hM _ _) x)]
  apply le_ciInf
  intro i
  apply (ciInf_le (process_rows_bddBelow a hM x) (I i)).trans
  apply ciSup_le
  intro v
  obtain ⟨j, hj⟩ := hJ v
  have hinner : ⟪a (I i) v, x⟫_ℝ ≤ ⟪a (I i) (J j), x⟫_ℝ + ε * ‖x‖ := by
    have h := (abs_real_inner_le_norm (a (I i) v - a (I i) (J j)) x).trans
      (mul_le_mul_of_nonneg_right (hj (I i)) (norm_nonneg _))
    rw [inner_sub_left] at h
    have hh := le_abs_self (⟪a (I i) v, x⟫_ℝ - ⟪a (I i) (J j), x⟫_ℝ)
    linarith
  exact hinner.trans (add_le_add_right
    (le_ciSup (Finite.bddAbove_range (fun j : Fin c ↦ ⟪a (I i) (J j), x⟫_ℝ)) j) _)

/-- A finite row net approximates the full infimum; sampled columns only
make each retained supremum smaller. -/
lemma sample_processMinMax_le_add [NeZero r] [NeZero c]
    (a : U → V → Reference.Space d) {M ε : ℝ}
    (hM : ∀ u v, ‖a u v‖ ≤ M) (I : Fin r → U) (J : Fin c → V)
    (hI : ∀ u, ∃ i, ∀ v, ‖a u v - a (I i) v‖ ≤ ε) (x : Reference.Space d) :
    processMinMax (fun i j ↦ a (I i) (J j)) x ≤ processMinMax a x + ε * ‖x‖ := by
  unfold processMinMax
  rw [ciInf_add (process_rows_bddBelow a hM x)]
  apply le_ciInf
  intro u
  obtain ⟨i, hi⟩ := hI u
  apply (ciInf_le (process_rows_bddBelow (fun i j ↦ a (I i) (J j)) (fun i j ↦ hM _ _) x) i).trans
  apply ciSup_le
  intro j
  have hinner : ⟪a (I i) (J j), x⟫_ℝ ≤ ⟪a u (J j), x⟫_ℝ + ε * ‖x‖ := by
    have h := (abs_real_inner_le_norm (a u (J j) - a (I i) (J j)) x).trans
      (mul_le_mul_of_nonneg_right (hi (J j)) (norm_nonneg _))
    rw [inner_sub_left] at h
    have hh := neg_le_abs (⟪a u (J j), x⟫_ℝ - ⟪a (I i) (J j), x⟫_ℝ)
    linarith
  exact hinner.trans (add_le_add_right (le_ciSup (process_row_bddAbove a hM x u) (J j)) _)

end GeneralIndices

section CompactIndices

variable {U V : Type*} [PseudoMetricSpace U] [PseudoMetricSpace V]
  [CompactSpace U] [CompactSpace V] [Nonempty U] [Nonempty V]

lemma compact_coefficients_bounded (a : U → V → Reference.Space d)
    (ha : Continuous (Function.uncurry a)) :
    ∃ M : ℝ≥0, ∀ u v, ‖a u v‖ ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuousOn
  refine ⟨⟨max C 0, le_max_right _ _⟩, fun u v ↦ ?_⟩
  exact (hC (u, v) (mem_univ _)).trans (le_max_left _ _)

/-- Compact metric index sets admit nonempty finite nets enumerated without
repetitions. Injectivity preserves the distinct-row hypothesis in Gordon. -/
lemma exists_injective_finite_net (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧ ∃ I : Fin r → U,
      Function.Injective I ∧ ∀ u : U, ∃ i, dist u (I i) < ε := by
  obtain ⟨S, _, hSfin, hcover⟩ := (isCompact_univ : IsCompact (univ : Set U)).finite_cover_balls hε
  have hSne : S.Nonempty := by
    let u : U := Classical.arbitrary U
    obtain ⟨v, hv⟩ := mem_iUnion.mp (hcover (mem_univ u))
    obtain ⟨hvS, _⟩ := mem_iUnion.mp hv
    exact ⟨v, hvS⟩
  letI : Fintype S := hSfin.fintype
  letI : Nonempty S := hSne.to_subtype
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, Fintype.card_pos, fun i ↦ (e.symm i).val, ?_, ?_⟩
  · intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  · intro u
    obtain ⟨v, hv⟩ := mem_iUnion.mp (hcover (mem_univ u))
    obtain ⟨hvS, huv⟩ := mem_iUnion.mp hv
    refine ⟨e ⟨v, hvS⟩, ?_⟩
    simpa only [Equiv.symm_apply_apply, Metric.mem_ball] using huv

/-- Gordon's Gaussian min/max comparison on arbitrary nonempty compact metric
index spaces with continuous coefficient vectors. Finite nets, uniform
continuity, integrable Gaussian approximation error, and the limiting
argument are all proved here. -/
theorem compact_gordon_comparison
    (a b : U → V → Reference.Space d)
    (ha : Continuous (Function.uncurry a)) (hb : Continuous (Function.uncurry b))
    (hsep : ∀ l : Fin d, (∀ u v, a u v l = 0) ∨ (∀ u v, b u v l = 0))
    (hwithin : ∀ u v v', ‖a u v - a u v'‖ ^ 2 ≤ ‖b u v - b u v'‖ ^ 2)
    (hcross : ∀ u u', u ≠ u' → ∀ v v', ‖b u v - b u' v'‖ ^ 2 ≤ ‖a u v - a u' v'‖ ^ 2) :
    (∫ x, processMinMax a x ∂standardGaussian d) ≤
      ∫ x, processMinMax b x ∂standardGaussian d := by
  obtain ⟨Ma, hMa⟩ := compact_coefficients_bounded a ha
  obtain ⟨Mb, hMb⟩ := compact_coefficients_bounded b hb
  have hia := processMinMax_gaussian_integrable a hMa
  have hib := processMinMax_gaussian_integrable b hMb
  have hnorm := standardGaussian_norm_integrable d
  have hnormpos : 0 ≤ ∫ x : Reference.Space d, ‖x‖ ∂standardGaussian d := integral_nonneg (fun x ↦ norm_nonneg _)
  apply le_of_uniform_div_error (c := 2 * ∫ x : Reference.Space d, ‖x‖ ∂standardGaussian d)
    (mul_nonneg (by norm_num) hnormpos)
  intro β hβ
  let ε : ℝ := 1 / β
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨δa, hδa, haunif⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous ha) ε hε
  obtain ⟨δb, hδb, hbunif⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hb) ε hε
  obtain ⟨r, hr, I, hIinj, hInet⟩ := exists_injective_finite_net (U := U) δb hδb
  obtain ⟨c, hc, J, _, hJnet⟩ := exists_injective_finite_net (U := V) δa hδa
  letI : NeZero r := ⟨hr.ne'⟩
  letI : NeZero c := ⟨hc.ne'⟩
  have hJ : ∀ v : V, ∃ j : Fin c, ∀ u : U, ‖a u v - a u (J j)‖ ≤ ε := by
    intro v
    obtain ⟨j, hj⟩ := hJnet v
    refine ⟨j, fun u ↦ ?_⟩
    have hp : dist (u, v) (u, J j) < δa := by simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using hj
    have hh := @haunif (u, v) (u, J j) hp
    simpa only [Function.uncurry_apply_pair, dist_eq_norm] using hh.le
  have hI : ∀ u : U, ∃ i : Fin r, ∀ v : V, ‖b u v - b (I i) v‖ ≤ ε := by
    intro u
    obtain ⟨i, hi⟩ := hInet u
    refine ⟨i, fun v ↦ ?_⟩
    have hp : dist (u, v) (I i, v) < δb := by simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hi
    have hh := @hbunif (u, v) (I i, v) hp
    simpa only [Function.uncurry_apply_pair, dist_eq_norm] using hh.le
  have hsample := finite_rectangular_gordon (fun i j ↦ a (I i) (J j)) (fun i j ↦ b (I i) (J j))
    (fun l ↦ (hsep l).imp (fun h i j ↦ h _ _) (fun h i j ↦ h _ _))
    (fun i j j' ↦ hwithin _ _ _)
    (fun i i' hii j j' ↦ hcross _ _ (fun h ↦ hii (hIinj h)) _ _)
  have hisa := processMinMax_gaussian_integrable (fun i j ↦ a (I i) (J j)) (fun i j ↦ hMa _ _)
  have hisb := processMinMax_gaussian_integrable (fun i j ↦ b (I i) (J j)) (fun i j ↦ hMb _ _)
  have hleft := integral_mono hia (hisa.add (hnorm.const_mul ε))
    (fun x ↦ processMinMax_le_sample_add a hMa I J hJ x)
  have hright := integral_mono hisb (hib.add (hnorm.const_mul ε))
    (fun x ↦ sample_processMinMax_le_add b hMb I J hI x)
  simp only [Pi.add_apply] at hleft hright
  rw [integral_add hisa (hnorm.const_mul ε), integral_const_mul] at hleft
  rw [integral_add hib (hnorm.const_mul ε), integral_const_mul] at hright
  change (∫ x, processMinMax (fun i j ↦ a (I i) (J j)) x ∂standardGaussian d) ≤
    ∫ x, processMinMax (fun i j ↦ b (I i) (J j)) x ∂standardGaussian d at hsample
  dsimp [ε] at hleft hright
  have heq : (2 * ∫ x : Reference.Space d, ‖x‖ ∂standardGaussian d) / β =
      2 * ((1 / β) * ∫ x : Reference.Space d, ‖x‖ ∂standardGaussian d) := by ring
  rw [heq]
  linarith

end CompactIndices

end GaussianTilt.Paouris
