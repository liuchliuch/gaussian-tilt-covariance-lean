import GaussianTilt.MomentMapClassicalDirichletIntrinsicTangentBounds

/-! # Uniform tangent-block bounds from actual global Hessian bounds -/
noncomputable section
open Set Matrix Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def coordinateTangentMatrix (j : Fin n) (β : TangentIndex j → ℝ) :
    Matrix (Fin n) (TangentIndex j) ℝ :=
  fun i a => (Pi.single (a:Fin n) 1 : Fin n → ℝ) i - β a*(Pi.single j 1 : Fin n → ℝ) i

lemma coordinateTangentMatrix_mulVec_apply (j : Fin n) (β c : TangentIndex j → ℝ)
    (a : TangentIndex j) : (coordinateTangentMatrix j β *ᵥ c) a = c a := by
  simp only [coordinateTangentMatrix,Matrix.mulVec,dotProduct,Pi.single_apply,a.property,
    if_false,mul_zero,sub_zero]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hne : (b:Fin n) ≠ a := fun h => hba (Subtype.ext h)
    simp [hne,Ne.symm hne]
  · simp

lemma coordinateTangentMatrix_injective (j : Fin n) (β : TangentIndex j → ℝ) :
    Function.Injective (coordinateTangentMatrix j β).mulVec := by
  intro c d h
  funext a
  have hh := congrFun h (a:Fin n)
  simpa only [coordinateTangentMatrix_mulVec_apply] using hh

lemma coordinateTangentBlock_eq_matrix (H : Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) (β : TangentIndex j → ℝ) :
    coordinateTangentBlock H j β = (coordinateTangentMatrix j β)ᵀ*H*coordinateTangentMatrix j β := by
  ext a b
  simp only [coordinateTangentBlock,Matrix.mul_apply,Matrix.transpose_apply,coordinateTangentMatrix,
    sub_mul,mul_sub,Finset.sum_sub_distrib,Finset.sum_mul,Finset.mul_sum]
  simp [Pi.single_apply]
  <;> ring

lemma coordinateTangentBlock_posDef {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    (j : Fin n) (β : TangentIndex j → ℝ) : (coordinateTangentBlock H j β).PosDef := by
  rw [coordinateTangentBlock_eq_matrix]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hH.conjTranspose_mul_mul_same (coordinateTangentMatrix_injective j β)

lemma isClosed_posSemidef_real_matrix :
    IsClosed {H : Matrix (Fin n) (Fin n) ℝ | H.PosSemidef} := by
  have he : {H : Matrix (Fin n) (Fin n) ℝ | H.PosSemidef} =
      {H | Hᵀ=H} ∩ ⋂ v : Fin n → ℝ, {H | 0 ≤ v ⬝ᵥ (H *ᵥ v)} := by
    ext H
    simp only [mem_setOf_eq,mem_inter_iff,mem_iInter,Matrix.PosSemidef,Matrix.IsHermitian,
      Matrix.conjTranspose_eq_transpose_of_trivial,star_trivial]
  rw [he]
  refine (isClosed_eq (by fun_prop) continuous_id).inter (isClosed_iInter (fun v => ?_))
  exact isClosed_le continuous_const (by unfold dotProduct Matrix.mulVec; fun_prop)

/-- Uniform tangential nonsingularity holds at interior as well as boundary
points. Its constants are constructed on the compact actual matrix class
with bounded entries, nonnegative quadratic form and positive determinant. -/
theorem exists_uniform_coordinateTangentBlock_bounds
    (j : Fin n) {c K B : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hB : 0 ≤ B) :
    ∃ δ I T : ℝ, 0 < δ ∧ 0 < I ∧ 0 < T ∧
      ∀ H : Matrix (Fin n) (Fin n) ℝ, H.PosDef → c ≤ H.det →
      (∀ i l, |H i l| ≤ K) → ∀ β : TangentIndex j → ℝ,
      (∀ a, |β a| ≤ B) →
      (coordinateTangentBlock H j β).PosDef ∧ δ ≤ (coordinateTangentBlock H j β).det ∧
      (∀ a b, |(coordinateTangentBlock H j β)⁻¹ a b| ≤ I) ∧
      (∀ a b, |coordinateTangentBlock H j β a b| ≤ T) := by
  let Q : Set (Matrix (Fin n) (Fin n) ℝ) :=
    Metric.closedBall 0 K ∩ {H | H.PosSemidef} ∩ {H | c ≤ H.det}
  have hQ : IsCompact Q := ((isCompact_closedBall _ _).inter_right isClosed_posSemidef_real_matrix).inter_right
    (isClosed_le continuous_const (continuous_id.matrix_det))
  let P := Q ×ˢ Metric.closedBall (0 : TangentIndex j → ℝ) B
  have hP : IsCompact P := hQ.prod (isCompact_closedBall _ _)
  let Z := fun p : Matrix (Fin n) (Fin n) ℝ × (TangentIndex j → ℝ) => coordinateTangentBlock p.1 j p.2
  have hZ : Continuous Z := by unfold Z coordinateTangentBlock; fun_prop
  have hp (p : Matrix (Fin n) (Fin n) ℝ × (TangentIndex j → ℝ)) (hp : p ∈ P) : (Z p).PosDef := by
    exact coordinateTangentBlock_posDef
      (posDef_of_posSemidef_det_ne_zero hp.1.1.2 (hc.trans_le hp.1.2).ne') j p.2
  obtain ⟨δ,I,hδ,hI,hbounds⟩ := exists_positive_det_and_inverse_bounds_on_compact hP hZ.continuousOn hp
  obtain ⟨M,hM⟩ := hP.exists_bound_of_continuousOn hZ.continuousOn
  refine ⟨δ,I,max M 1,hδ,hI,zero_lt_one.trans_le (le_max_right _ _),?_⟩
  intro H hH hdet hentry β hβ
  have hm : (H,β) ∈ P := by
    refine ⟨⟨⟨?_,hH.posSemidef⟩,hdet⟩,?_⟩
    · rw [Metric.mem_closedBall,dist_zero_right,Matrix.norm_le_iff hK]
      exact hentry
    · rw [Metric.mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg hB]
      exact hβ
  exact ⟨coordinateTangentBlock_posDef hH j β,(hbounds (H,β) hm).1,(hbounds (H,β) hm).2,
    fun a b => (Matrix.norm_entry_le_entrywise_sup_norm (Z (H,β)) (i:=a) (j:=b)).trans
      ((hM (H,β) hm).trans (le_max_left _ _))⟩

end GaussianTilt.MomentMapRegularity
