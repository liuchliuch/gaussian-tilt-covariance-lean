import GaussianTilt.MomentMapRegularityVariableDensityCalabi
import GaussianTilt.MomentMapCalabiFifthReduction

/-! # Finite Calabi contraction with all logarithmic-forcing terms -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma calabiContraction_add_first (A B C D : Matrix (Fin n) (Fin n) ℝ)
    (T U : Fin n → Fin n → Fin n → ℝ) :
    calabiContraction (A+B) C D T U = calabiContraction A C D T U + calabiContraction B C D T U := by
  simp only [calabiContraction, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

lemma calabiContraction_inverse_second_sum_forced (T : Fin n → Fin n → Fin n → ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hT : calabiTensorSymm T) (hQ : ∑ l, Q l = calabiCubicGram T+G) :
    (∑ l, calabiContraction ((2 : ℝ) • (calabiSlice T l * calabiSlice T l) - Q l) 1 1 T T) =
      sum4 (fun i j k l => calabiGram4 T i j k l ^ 2) - calabiContraction G 1 1 T T := by
  simp only [calabiContraction_sub_first, calabiContraction_smul_first, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, calabiContraction_slice_squares T hT,
    ← calabiContraction_sum_first, hQ, calabiContraction_add_first, calabiContraction_cubicGram]
  ring

lemma calabiContraction_fifth_sum_forced
    (T : Fin n → Fin n → Fin n → ℝ)
    (Q P : Fin n → Fin n → Fin n → Fin n → ℝ) (G : Fin n → Fin n → Fin n → ℝ) (hT : calabiTensorSymm T)
    (hP : ∀ a b c, (∑ l, P a b c l) =
      (∑ i, ∑ j, (Q a b i j * T c i j + Q a c i j * T b i j + Q b c i j * T a i j)) -
        2 * ∑ i, ∑ j, ∑ k, T a i j * T b j k * T c k i + G a b c) :
    (∑ l, calabiContraction 1 1 1 (fun a b c => P a b c l) T) =
      3 * sum4 (fun a b c d => Q a b c d * calabiGram4 T a b c d) -
        2 * sum4 (fun a b c d => calabiGram4 T a b c d * calabiGram4 T a c b d) +
        (∑ a, ∑ b, ∑ c, G a b c * T a b c) := by
  simp only [calabiContraction_one_one_one]
  have he := Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun l : Fin n => fun z : Fin n × Fin n × Fin n => P z.1 z.2.1 z.2.2 l * T z.1 z.2.1 z.2.2)
  simp only [Fintype.sum_prod_type] at he
  rw [he]
  simp_rw [← Finset.sum_mul, hP]
  simp only [sub_mul, Finset.sum_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [calabi_fourth_cubic_contraction T Q hT, calabi_fourth_cubic_contraction_second T Q hT,
    calabi_fourth_cubic_contraction_third T Q hT]
  have hb : (∑ a, ∑ b, ∑ c, ∑ i, ∑ j, ∑ k,
      2 * (T a i j * T b j k * T c k i) * T a b c) =
      2 * sum4 (fun a b c d => calabiGram4 T a b c d * calabiGram4 T a c b d) := by
    rw [← calabi_triple_trace_contraction T hT]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [hb]
  ring


theorem calabi_five_term_reduction_forced
    (T : Fin n → Fin n → Fin n → ℝ)
    (Q P : Fin n → Fin n → Fin n → Fin n → ℝ)
    (G₂ : Matrix (Fin n) (Fin n) ℝ) (G₃ : Fin n → Fin n → Fin n → ℝ) (hT : calabiTensorSymm T)
    (hQcycle : ∀ a b c l, Q a b c l = Q l a b c)
    (hQ : ∀ a b, (∑ l, Q a b l l) = (∑ i, ∑ j, T a i j * T b i j)+G₂ a b)
    (hP : ∀ a b c, (∑ l, P a b c l) =
      (∑ i, ∑ j, (Q a b i j * T c i j + Q a c i j * T b i j + Q b c i j * T a i j)) -
        2 * ∑ i, ∑ j, ∑ k, T a i j * T b j k * T c k i + G₃ a b c) :
    (∑ l, (3 * calabiContraction
        ((2 : ℝ) • (calabiSlice T l * calabiSlice T l) - (show Matrix (Fin n) (Fin n) ℝ from fun a b => Q a b l l))
        1 1 T T +
      6 * calabiContraction (-calabiSlice T l) (-calabiSlice T l) 1 T T +
      12 * calabiContraction (-calabiSlice T l) 1 1 (fun a b c => Q a b c l) T +
      2 * calabiContraction 1 1 1 (fun a b c => P a b c l) T +
      2 * calabiContraction 1 1 1 (fun a b c => Q a b c l) (fun a b c => Q a b c l))) =
    2 * sum4 (fun a b c d => Q a b c d ^ 2) -
      6 * sum4 (fun a b c d => Q a b c d * calabiGram4 T a b c d) +
      3 * sum4 (fun a b c d => calabiGram4 T a b c d ^ 2) +
      2 * sum4 (fun a b c d => calabiGram4 T a b c d * calabiGram4 T a c b d) -
      3 * calabiContraction G₂ 1 1 T T + 2 * (∑ a, ∑ b, ∑ c, G₃ a b c*T a b c) := by
  have hQmat : (∑ l, (show Matrix (Fin n) (Fin n) ℝ from fun a b => Q a b l l)) = calabiCubicGram T+G₂ := by
    ext a b
    simpa only [Matrix.sum_apply, calabiCubicGram, Matrix.add_apply] using hQ a b
  simp only [calabiContraction_neg_neg]
  simp only [calabiContraction_neg_first, mul_neg,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [calabiContraction_inverse_second_sum_forced T _ G₂ hT hQmat,
    calabiContraction_two_slices T hT, calabiContraction_mixed_fourth T Q hT hQcycle,
    calabiContraction_fifth_sum_forced T Q P G₃ hT hP, calabiContraction_fourth_square Q]
  ring

end GaussianTilt.MomentMapRegularity
