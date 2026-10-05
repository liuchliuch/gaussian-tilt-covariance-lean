import GaussianTilt.MomentMapSchauderCoefficients

/-!
# Positivity and compact bounds of the integrated inverse Hessian

These bounds are consequences of positive definite, continuous Hessians,
and belong only after the first C² regularity stage.
-/
noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 500000 in
lemma trace_averagedInverse_mul_eq_integral {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (D : Matrix ι ι ℝ) :
    Matrix.trace (averagedInverse A B * D) =
      ∫ t in (0 : ℝ)..1, Matrix.trace ((matrixSegment A B t)⁻¹ * D) := by
  symm
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, averagedInverse]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j _
      exact intervalIntegral.integral_mul_const _ _
    · intro j _
      exact (intervalIntegrable_inv_matrixSegment hA hB i j).mul_const _
  · intro i _
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ
      (f := fun j t => (matrixSegment A B t)⁻¹ i j * D j i)
      (fun j _ => (intervalIntegrable_inv_matrixSegment hA hB i j).mul_const (D j i))

lemma quadraticForm_averagedInverse_eq_integral {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (v : ι → ℝ) :
    v ⬝ᵥ (averagedInverse A B *ᵥ v) =
      ∫ t in (0 : ℝ)..1, v ⬝ᵥ ((matrixSegment A B t)⁻¹ *ᵥ v) := by
  have he := trace_averagedInverse_mul_eq_integral hA hB (Matrix.vecMulVec v v)
  simpa only [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] using he

lemma averagedInverse_isHermitian {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) : (averagedInverse A B).IsHermitian := by
  ext i j
  change star (averagedInverse A B j i) = averagedInverse A B i j
  simp only [star_trivial, averagedInverse]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  simpa only [star_trivial] using (matrixSegment_posDef hA hB ht').inv.isHermitian.apply i j

/-- The actual integral coefficient is positive definite; positivity is
proved by integrating the positive inverse quadratic forms. -/
theorem averagedInverse_posDef {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) : (averagedInverse A B).PosDef := by
  refine ⟨averagedInverse_isHermitian hA hB, ?_⟩
  intro v hv
  simp only [star_trivial]
  rw [quadraticForm_averagedInverse_eq_integral hA hB]
  have hc : ContinuousOn (fun t => v ⬝ᵥ ((matrixSegment A B t)⁻¹ *ᵥ v)) (Icc 0 1) :=
    (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)).comp_continuousOn
      (continuousOn_inv_matrixSegment hA hB)
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (hc.intervalIntegrable_of_Icc (by norm_num)) ?_ (by norm_num)
  intro t ht
  simpa only [star_trivial] using (matrixSegment_posDef hA hB (Ioo_subset_Icc_self ht)).inv.2 v hv

/-- Continuous positive matrix fields on a compact set have a uniform bound
for every inverse along every segment between two field values.  This is
obtained from compactness, rather than assumed as uniform ellipticity. -/
theorem exists_bound_inv_segments_on_compact {X : Type*} [TopologicalSpace X]
    {H : X → Matrix ι ι ℝ} {S : Set X}
    (hS : IsCompact S) (hH : ContinuousOn H S) (hpos : ∀ x ∈ S, (H x).PosDef) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ i j, |(matrixSegment (H x) (H y) t)⁻¹ i j| ≤ M := by
  let T : Set (X × X × ℝ) := S ×ˢ (S ×ˢ Icc (0 : ℝ) 1)
  have hT : IsCompact T := hS.prod (hS.prod isCompact_Icc)
  let F : X × X × ℝ → Matrix ι ι ℝ := fun p => matrixSegment (H p.1) (H p.2.1) p.2.2
  have hF : ContinuousOn F T := by
    have hx : ContinuousOn (fun p : X × X × ℝ => H p.1) T :=
      hH.comp continuous_fst.continuousOn (fun _ hp => hp.1)
    have hy : ContinuousOn (fun p : X × X × ℝ => H p.2.1) T :=
      hH.comp (continuous_fst.comp continuous_snd).continuousOn (fun _ hp => hp.2.1)
    exact (continuousOn_const.sub (continuous_snd.comp continuous_snd).continuousOn).smul hx |>.add
      ((continuous_snd.comp continuous_snd).continuousOn.smul hy)
  have hi : ContinuousOn (fun p => (F p)⁻¹) T := by
    intro p hp
    apply ContinuousAt.comp_continuousWithinAt _ (hF p hp)
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀
      (matrixSegment_posDef (hpos p.1 hp.1) (hpos p.2.1 hp.2.1) hp.2.2).det_pos.ne'
  obtain ⟨M, hM⟩ := hT.exists_bound_of_continuousOn hi
  refine ⟨max M 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx y hy t ht i j
  have hb := hM (x, y, t) (show (x, y, t) ∈ T from ⟨hx, hy, ht⟩)
  apply le_trans _ (hb.trans (le_max_left _ _))
  simpa only [Real.norm_eq_abs] using
    (Matrix.norm_entry_le_entrywise_sup_norm ((matrixSegment (H x) (H y) t)⁻¹) (i := i) (j := j))

end GaussianTilt.MomentMapSchauder
