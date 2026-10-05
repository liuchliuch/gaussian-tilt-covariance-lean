import GaussianTilt.MomentMapRegularityConstantDensityCalabiContraction
import GaussianTilt.MomentMapCalabiMetric

/-! # Finite reindexing of the normalized Calabi contraction -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma calabiTensorSymm_cycle {T : Fin n → Fin n → Fin n → ℝ}
    (hT : calabiTensorSymm T) (a b c : Fin n) : T a b c = T b c a := by
  rw [hT.1 a b c, hT.2 b a c]

lemma calabiContraction_one_one_one (T U : Fin n → Fin n → Fin n → ℝ) :
    calabiContraction 1 1 1 T U = ∑ a, ∑ b, ∑ c, T a b c * U a b c := by
  simp [calabiContraction, Fintype.sum_prod_type, Matrix.one_apply]

lemma calabiContraction_one_one (A : Matrix (Fin n) (Fin n) ℝ)
    (T U : Fin n → Fin n → Fin n → ℝ) :
    calabiContraction A 1 1 T U = ∑ a, ∑ i, ∑ b, ∑ c, A a i * T a b c * U i b c := by
  simp [calabiContraction, Fintype.sum_prod_type, Matrix.one_apply]

lemma calabiContraction_one (A B : Matrix (Fin n) (Fin n) ℝ)
    (T U : Fin n → Fin n → Fin n → ℝ) :
    calabiContraction A B 1 T U =
      ∑ a, ∑ i, ∑ b, ∑ j, ∑ c, A a i * B b j * T a b c * U i j c := by
  simp [calabiContraction, Fintype.sum_prod_type, Matrix.one_apply]

lemma calabiContraction_sum_first {κ : Type*} [Fintype κ]
    (A : κ → Matrix (Fin n) (Fin n) ℝ) (B C : Matrix (Fin n) (Fin n) ℝ)
    (T U : Fin n → Fin n → Fin n → ℝ) :
    calabiContraction (∑ l, A l) B C T U = ∑ l, calabiContraction (A l) B C T U := by
  simp only [calabiContraction, Matrix.sum_apply, Finset.sum_mul]
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun z : (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n) => fun l : κ =>
        A l z.1.1 z.1.2 * B z.2.1.1 z.2.1.2 * C z.2.2.1 z.2.2.2 *
          T z.1.1 z.2.1.1 z.2.2.1 * U z.1.2 z.2.1.2 z.2.2.2))

lemma calabiContraction_sub_first (A B C D : Matrix (Fin n) (Fin n) ℝ)
    (T U : Fin n → Fin n → Fin n → ℝ) :
    calabiContraction (A - B) C D T U = calabiContraction A C D T U - calabiContraction B C D T U := by
  simp only [calabiContraction, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma calabiContraction_smul_first (a : ℝ) (A B C : Matrix (Fin n) (Fin n) ℝ)
    (T U : Fin n → Fin n → Fin n → ℝ) :
    calabiContraction (a • A) B C T U = a * calabiContraction A B C T U := by
  simp only [calabiContraction, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  ring

def calabiCubicGram (T : Fin n → Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b => ∑ i, ∑ j, T a i j * T b i j

def calabiSlice (T : Fin n → Fin n → Fin n → ℝ) (l : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun a b => T l a b)

lemma calabi_slice_square_sum (T : Fin n → Fin n → Fin n → ℝ) (hT : calabiTensorSymm T) :
    (∑ l, calabiSlice T l * calabiSlice T l) = calabiCubicGram T := by
  ext a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Matrix.mul_apply, calabiCubicGram, calabiSlice, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  rw [hT.1 l a m, hT.2 l m b, hT.1 l b m]

lemma calabiContraction_cubicGram (T : Fin n → Fin n → Fin n → ℝ) :
    calabiContraction (calabiCubicGram T) 1 1 T T = sum4 (fun i j k l => calabiGram4 T i j k l ^ 2) := by
  rw [calabiContraction_one_one, calabi_gram_square_identity]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  change (∑ b, ∑ c, calabiCubicGram T a i * T a b c * T i b c) = (calabiCubicGram T a i)^2
  calc
    _ = ∑ b, ∑ c, calabiCubicGram T a i * (T a b c * T i b c) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by simp only [← Finset.mul_sum, pow_two]; rfl

lemma calabiContraction_slice_squares (T : Fin n → Fin n → Fin n → ℝ) (hT : calabiTensorSymm T) :
    (∑ l, calabiContraction
      (calabiSlice T l * calabiSlice T l)
      1 1 T T) = sum4 (fun i j k l => calabiGram4 T i j k l ^ 2) := by
  rw [← calabiContraction_sum_first, calabi_slice_square_sum T hT, calabiContraction_cubicGram]

lemma calabiContraction_inverse_second_sum (T : Fin n → Fin n → Fin n → ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : calabiTensorSymm T)
    (hQ : ∑ l, Q l = calabiCubicGram T) :
    (∑ l, calabiContraction
      ((2 : ℝ) • (calabiSlice T l * calabiSlice T l) - Q l)
      1 1 T T) = sum4 (fun i j k l => calabiGram4 T i j k l ^ 2) := by
  simp only [calabiContraction_sub_first, calabiContraction_smul_first, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, calabiContraction_slice_squares T hT,
    ← calabiContraction_sum_first, hQ, calabiContraction_cubicGram]
  ring

lemma calabiContraction_two_slices (T : Fin n → Fin n → Fin n → ℝ) (hT : calabiTensorSymm T) :
    (∑ l, calabiContraction (calabiSlice T l) (calabiSlice T l) 1 T T) =
      sum4 (fun i j k l => calabiGram4 T i j k l * calabiGram4 T i k j l) := by
  simp only [calabiContraction_one, sum4, calabiGram4, calabiSlice, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  have hswap := Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun l : Fin n => fun z : Fin n × Fin n × Fin n × Fin n =>
      ∑ c, T l z.1 z.2.1 * T l z.2.2.1 z.2.2.2 * T z.1 z.2.2.1 c * T z.2.1 z.2.2.2 c)
  simp only [Fintype.sum_prod_type] at hswap
  rw [hswap]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro c _
  rw [← calabiTensorSymm_cycle hT l a b, ← calabiTensorSymm_cycle hT l i j]
  ring

lemma calabiContraction_neg_first (A B C : Matrix (Fin n) (Fin n) ℝ)
    (T U : Fin n → Fin n → Fin n → ℝ) :
    calabiContraction (-A) B C T U = -calabiContraction A B C T U := by
  simp only [calabiContraction, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]

lemma calabiContraction_neg_neg (A B C : Matrix (Fin n) (Fin n) ℝ)
    (T U : Fin n → Fin n → Fin n → ℝ) :
    calabiContraction (-A) (-B) C T U = calabiContraction A B C T U := by
  simp only [calabiContraction, Matrix.neg_apply, neg_mul_neg]

lemma calabiContraction_fourth_square (Q : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ l, calabiContraction 1 1 1 (fun a b c => Q a b c l) (fun a b c => Q a b c l)) =
      sum4 (fun a b c l => Q a b c l ^ 2) := by
  simp only [calabiContraction_one_one_one, ← pow_two, sum4]
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun l : Fin n => fun z : Fin n × Fin n × Fin n => Q z.1 z.2.1 z.2.2 l ^ 2))

lemma calabiContraction_mixed_fourth
    (T : Fin n → Fin n → Fin n → ℝ) (Q : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hT : calabiTensorSymm T) (hQ : ∀ a b c l, Q a b c l = Q l a b c) :
    (∑ l, calabiContraction (calabiSlice T l) 1 1 (fun a b c => Q a b c l) T) =
      sum4 (fun a b c l => Q a b c l * calabiGram4 T a b c l) := by
  simp only [calabiContraction_one_one, calabiSlice, Matrix.of_apply, sum4, calabiGram4, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro a _
  have hs := Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun i : Fin n => fun z : Fin n × Fin n => T l a i * Q a z.1 z.2 l * T i z.1 z.2)
  simp only [Fintype.sum_prod_type] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro i _
  rw [hQ a b c l, ← calabiTensorSymm_cycle hT i l a]
  ring

set_option maxHeartbeats 1000000 in
lemma calabi_triple_trace_contraction (T : Fin n → Fin n → Fin n → ℝ) (hT : calabiTensorSymm T) :
    (∑ a, ∑ b, ∑ c, ∑ i, ∑ j, ∑ k,
      T a b c * T a i j * T b j k * T c k i) =
      sum4 (fun a b c d => calabiGram4 T a b c d * calabiGram4 T a c b d) := by
  let e : (Fin n × Fin n × Fin n × Fin n × Fin n × Fin n) ≃
      (Fin n × Fin n × Fin n × Fin n × Fin n × Fin n) := {
    toFun := fun z => (z.2.1, z.2.2.1, z.2.2.2.2.1, z.2.2.2.1, z.1, z.2.2.2.2.2)
    invFun := fun z => (z.2.2.2.2.1, z.1, z.2.1, z.2.2.2.1, z.2.2.1, z.2.2.2.2.2)
    left_inv := by intro ⟨a,b,c,i,j,k⟩; rfl
    right_inv := by intro ⟨a,b,c,i,j,k⟩; rfl }
  have he := Fintype.sum_equiv e
    (fun z => T z.1 z.2.1 z.2.2.1 * T z.1 z.2.2.2.1 z.2.2.2.2.1 *
      T z.2.1 z.2.2.2.2.1 z.2.2.2.2.2 * T z.2.2.1 z.2.2.2.2.2 z.2.2.2.1)
    (fun z => (T z.2.2.2.2.1 z.1 z.2.1 * T z.2.2.2.2.1 z.2.2.1 z.2.2.2.1) *
      (T z.2.2.2.2.2 z.1 z.2.2.1 * T z.2.2.2.2.2 z.2.1 z.2.2.2.1)) ?_
  · simp only [Fintype.sum_prod_type] at he
    rw [he]
    simp only [sum4, calabiGram4, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_comm]
  · intro ⟨a,b,c,i,j,k⟩
    change T a b c * T a i j * T b j k * T c k i =
      (T a b c * T a j i) * (T k b j * T k c i)
    rw [hT.2 a j i, calabiTensorSymm_cycle hT k b j, hT.1 k c i]
    ring

end GaussianTilt.MomentMapRegularity
