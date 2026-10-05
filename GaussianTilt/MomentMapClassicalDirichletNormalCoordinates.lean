import GaussianTilt.MomentMapClassicalDirichletNormalShear

/-! # Actual coordinate reindexing for tangential and normal Hessian blocks -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Enumerate every coordinate except `j`, followed by the normal coordinate. -/
def tangentNormalEquiv (j : Fin n) : ({i : Fin n // i ≠ j} ⊕ Unit) ≃ Fin n :=
  Equiv.ofBijective (Sum.elim Subtype.val (fun _ => j)) (by
    constructor
    · rintro (a | ⟨⟩) (b | ⟨⟩) h
      · exact congrArg Sum.inl (Subtype.ext h)
      · exact False.elim (a.property h)
      · exact False.elim (b.property h.symm)
      · rfl
    · intro i
      by_cases hi : i = j
      · exact ⟨Sum.inr (), hi.symm⟩
      · exact ⟨Sum.inl ⟨i,hi⟩, rfl⟩)

@[simp] lemma tangentNormalEquiv_inl (j : Fin n) (i : {i : Fin n // i ≠ j}) :
    tangentNormalEquiv j (Sum.inl i) = i := rfl

@[simp] lemma tangentNormalEquiv_inr (j : Fin n) (i : Unit) :
    tangentNormalEquiv j (Sum.inr i) = j := rfl

lemma submatrix_tangentNormalEquiv {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (j : Fin n) :
    H.submatrix (tangentNormalEquiv j) (tangentNormalEquiv j) =
      normalBlockMatrix (fun a b : {i : Fin n // i ≠ j} => H a b) (fun a : {i : Fin n // i ≠ j} => H a j) (H j j) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  all_goals simp only [Matrix.submatrix_apply, tangentNormalEquiv_inl, tangentNormalEquiv_inr,
    normalBlockMatrix, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  exact hH.apply _ _

lemma normalBlockMatrix_coordinate_det {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (j : Fin n) :
    (normalBlockMatrix (fun a b : {i : Fin n // i ≠ j} => H a b)
      (fun a : {i : Fin n // i ≠ j} => H a j) (H j j)).det = H.det := by
  rw [← submatrix_tangentNormalEquiv hH, Matrix.det_submatrix_equiv_self]

/-- Literal bilinear tangent block associated with the adapted chart. -/
def coordinateTangentBlock (H : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    (β : {i : Fin n // i ≠ j} → ℝ) :
    Matrix {i : Fin n // i ≠ j} {i : Fin n // i ≠ j} ℝ :=
  fun a b => H a b - H a j * β b - β a * H j b + H j j * β a * β b

lemma coordinateTangentBlock_eq {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (j : Fin n) (β : {i : Fin n // i ≠ j} → ℝ) :
    coordinateTangentBlock H j β =
      H.submatrix (fun a : {i : Fin n // i ≠ j} => a.val) (fun a : {i : Fin n // i ≠ j} => a.val) - vecMulVec (fun a : {i : Fin n // i ≠ j} => H a j) β -
        vecMulVec β (fun a : {i : Fin n // i ≠ j} => H a j) + (H j j) • vecMulVec β β := by
  ext a b
  simp only [coordinateTangentBlock, Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply]
  rw [hH.apply j b]
  ring

/-- The original pure coordinate normal entry is bounded using the actual
adapted tangent block and the adapted mixed entries, preserving det(H). -/
theorem coordinate_normal_hessian_bound {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (j : Fin n) (β : {i : Fin n // i ≠ j} → ℝ)
    {d I K F : ℝ} (hT : (coordinateTangentBlock H j β).PosDef)
    (hd : 0 < d) (hI : 0 ≤ I) (hK : 0 ≤ K) (hF : 0 ≤ F)
    (hdetT : d ≤ (coordinateTangentBlock H j β).det)
    (hInv : ∀ a b, |(coordinateTangentBlock H j β)⁻¹ a b| ≤ I)
    (hMixed : ∀ a : {i : Fin n // i ≠ j}, |H a j - β a * H j j| ≤ K) (hdetH : H.det ≤ F) :
    H j j ≤ F / d + (Fintype.card {i : Fin n // i ≠ j} : ℝ)^2 * I * K^2 := by
  rw [coordinateTangentBlock_eq hH] at hT hdetT hInv
  apply normalBlockMatrix_bound_of_tangential_data hT hd hI hK hF hdetT hInv
  · simpa only [mul_comm] using hMixed
  · change (normalBlockMatrix (fun a b : {i : Fin n // i ≠ j} => H a b)
      (fun a => H a j) (H j j)).det ≤ F
    rwa [normalBlockMatrix_coordinate_det hH]

/-- Tangential, adapted mixed, and pure normal estimates control every
original Hessian entry. The source is only pointwise positive semidefinite. -/
theorem coordinate_hessian_entries_bound_of_adapted_bounds
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosSemidef) (j : Fin n)
    (β : {i : Fin n // i ≠ j} → ℝ) {T B K N : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hN : 0 ≤ N)
    (hTang : ∀ a, |coordinateTangentBlock H j β a a| ≤ T)
    (hβ : ∀ a, |β a| ≤ B)
    (hMixed : ∀ a : {i : Fin n // i ≠ j}, |H a j - β a*H j j| ≤ K)
    (hNormal : H j j ≤ N) :
    ∀ i l, |H i l| ≤ (n:ℝ)*max N (T+2*B*K+B^2*N) := by
  have hsym : H.IsSymm := by
    simpa only [Matrix.IsHermitian,Matrix.IsSymm,Matrix.conjTranspose_eq_transpose_of_trivial] using hH.isHermitian
  have hc : 0 ≤ H j j := by
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using hH.2 (Pi.single j (1:ℝ))
  have hdiag (i : Fin n) : H i i ≤ max N (T+2*B*K+B^2*N) := by
    by_cases hij : i = j
    · subst i
      exact hNormal.trans (le_max_left _ _)
    · let a : {i : Fin n // i ≠ j} := ⟨i,hij⟩
      have ht := (le_abs_self (coordinateTangentBlock H j β a a)).trans (hTang a)
      have hm : β a*(H i j-β a*H j j) ≤ B*K := by
        calc
          _ ≤ |β a*(H i j-β a*H j j)| := le_abs_self _
          _ = |β a| * |H i j-β a*H j j| := abs_mul _ _
          _ ≤ B*K := mul_le_mul (hβ a) (hMixed a) (abs_nonneg _) hB
      have hs : (β a)^2 ≤ B^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (β a)) hB).mpr (hβ a)
      have hp : (β a)^2*H j j ≤ B^2*N := mul_le_mul hs hNormal hc (sq_nonneg _)
      have he : H i i = coordinateTangentBlock H j β a a +
          2*(β a*(H i j-β a*H j j))+(β a)^2*H j j := by
        change H i i = H i i-H i j*β a-β a*H j i+H j j*β a*β a+
          2*(β a*(H i j-β a*H j j))+(β a)^2*H j j
        rw [hsym.apply i j]
        ring
      apply le_trans _ (le_max_right _ _)
      nlinarith
  intro i l
  apply (abs_matrix_entry_le_trace hH i l).trans
  calc
    H.trace ≤ ∑ _i : Fin n, max N (T+2*B*K+B^2*N) :=
      Finset.sum_le_sum (fun i _ => hdiag i)
    _ = _ := by simp

end GaussianTilt.MomentMapRegularity
