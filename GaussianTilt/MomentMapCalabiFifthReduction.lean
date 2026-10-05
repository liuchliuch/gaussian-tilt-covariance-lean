import GaussianTilt.MomentMapCalabiContractionReduction

/-! # Finite contraction of the actual third differentiated determinant identity -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma sum3_cycle (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, f b c a) = ∑ a, ∑ b, ∑ c, f a b c := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun a : Fin n => fun z : Fin n × Fin n => f z.1 z.2 a))

lemma calabi_fourth_cubic_contraction (T : Fin n → Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → Fin n → Fin n → ℝ) (hT : calabiTensorSymm T) :
    (∑ a, ∑ b, ∑ c, ∑ i, ∑ j, Q a b i j * T c i j * T a b c) =
      sum4 (fun a b c d => Q a b c d * calabiGram4 T a b c d) := by
  unfold sum4 calabiGram4
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have he := Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun c : Fin n => fun z : Fin n × Fin n => Q a b z.1 z.2 * T c z.1 z.2 * T a b c)
  simp only [Fintype.sum_prod_type] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro c _
  rw [← calabiTensorSymm_cycle hT c a b]
  ring

lemma calabi_fourth_cubic_contraction_second (T : Fin n → Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → Fin n → Fin n → ℝ) (hT : calabiTensorSymm T) :
    (∑ a, ∑ b, ∑ c, ∑ i, ∑ j, Q a c i j * T b i j * T a b c) =
      sum4 (fun a b c d => Q a b c d * calabiGram4 T a b c d) := by
  rw [← calabi_fourth_cubic_contraction T Q hT]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  simp only [hT.2 a c b]

lemma calabi_fourth_cubic_contraction_third (T : Fin n → Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → Fin n → Fin n → ℝ) (hT : calabiTensorSymm T) :
    (∑ a, ∑ b, ∑ c, ∑ i, ∑ j, Q b c i j * T a i j * T a b c) =
      sum4 (fun a b c d => Q a b c d * calabiGram4 T a b c d) := by
  calc
    _ = ∑ a, ∑ b, ∑ c, ∑ i, ∑ j, Q b c i j * T a i j * T b c a := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [calabiTensorSymm_cycle hT a b c]
    _ = ∑ a, ∑ b, ∑ c, ∑ i, ∑ j, Q a b i j * T c i j * T a b c := sum3_cycle _
    _ = _ := calabi_fourth_cubic_contraction T Q hT

lemma calabiContraction_fifth_sum
    (T : Fin n → Fin n → Fin n → ℝ)
    (Q P : Fin n → Fin n → Fin n → Fin n → ℝ) (hT : calabiTensorSymm T)
    (hP : ∀ a b c, (∑ l, P a b c l) =
      (∑ i, ∑ j, (Q a b i j * T c i j + Q a c i j * T b i j + Q b c i j * T a i j)) -
        2 * ∑ i, ∑ j, ∑ k, T a i j * T b j k * T c k i) :
    (∑ l, calabiContraction 1 1 1 (fun a b c => P a b c l) T) =
      3 * sum4 (fun a b c d => Q a b c d * calabiGram4 T a b c d) -
        2 * sum4 (fun a b c d => calabiGram4 T a b c d * calabiGram4 T a c b d) := by
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

/-- The entire normalized five-term second-derivative expansion reduces to
Calabi's square-completion expression. The two trace premises are finite
identities supplied by actual differentiation of det Hess=1. -/
theorem calabi_five_term_reduction
    (T : Fin n → Fin n → Fin n → ℝ)
    (Q P : Fin n → Fin n → Fin n → Fin n → ℝ) (hT : calabiTensorSymm T)
    (hQcycle : ∀ a b c l, Q a b c l = Q l a b c)
    (hQ : ∀ a b, (∑ l, Q a b l l) = ∑ i, ∑ j, T a i j * T b i j)
    (hP : ∀ a b c, (∑ l, P a b c l) =
      (∑ i, ∑ j, (Q a b i j * T c i j + Q a c i j * T b i j + Q b c i j * T a i j)) -
        2 * ∑ i, ∑ j, ∑ k, T a i j * T b j k * T c k i) :
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
      2 * sum4 (fun a b c d => calabiGram4 T a b c d * calabiGram4 T a c b d) := by
  have hQmat : (∑ l, (show Matrix (Fin n) (Fin n) ℝ from fun a b => Q a b l l)) = calabiCubicGram T := by
    ext a b
    simpa only [Matrix.sum_apply, calabiCubicGram] using hQ a b
  simp only [calabiContraction_neg_neg]
  simp only [calabiContraction_neg_first, mul_neg,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [calabiContraction_inverse_second_sum T _ hT hQmat,
    calabiContraction_two_slices T hT, calabiContraction_mixed_fourth T Q hT hQcycle,
    calabiContraction_fifth_sum T Q P hT hP, calabiContraction_fourth_square Q]
  ring

end GaussianTilt.MomentMapRegularity
