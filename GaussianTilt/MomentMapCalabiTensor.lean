import GaussianTilt.LetwinTensorMetric

/-! # Tensor square-completion in Calabi's third-derivative estimate

These are finite algebraic identities and inequalities, separate from the
actual differential computation. The proof follows Calabi's sum-of-squares
structure (see C. Mooney, The Monge–Ampère Equation, 2018, §4.2).
-/
noncomputable section
open Matrix
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity
variable {ι : Type*} [Fintype ι]

def sum4 (f : ι → ι → ι → ι → ℝ) : ℝ := ∑ i, ∑ j, ∑ k, ∑ l, f i j k l

lemma sum4_add (f g : ι → ι → ι → ι → ℝ) :
    sum4 (fun i j k l => f i j k l + g i j k l) = sum4 f + sum4 g := by
  simp only [sum4, Finset.sum_add_distrib]

lemma sum4_sub (f g : ι → ι → ι → ι → ℝ) :
    sum4 (fun i j k l => f i j k l - g i j k l) = sum4 f - sum4 g := by
  simp only [sum4, Finset.sum_sub_distrib]

lemma sum4_const_mul (c : ℝ) (f : ι → ι → ι → ι → ℝ) :
    sum4 (fun i j k l => c * f i j k l) = c * sum4 f := by
  simp only [sum4, Finset.mul_sum]

lemma sum4_congr {f g : ι → ι → ι → ι → ℝ}
    (h : ∀ i j k l, f i j k l = g i j k l) : sum4 f = sum4 g := by
  unfold sum4
  congr 1
  funext i
  congr 1
  funext j
  congr 1
  funext k
  congr 1
  funext l
  exact h i j k l

lemma sum4_nonneg {f : ι → ι → ι → ι → ℝ}
    (h : ∀ i j k l, 0 ≤ f i j k l) : 0 ≤ sum4 f := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => h i j k l

lemma sum4_swap23 (f : ι → ι → ι → ι → ℝ) :
    sum4 (fun i j k l => f i k j l) = sum4 f := by
  unfold sum4
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

lemma sum4_swap34 (f : ι → ι → ι → ι → ℝ) :
    sum4 (fun i j k l => f i j l k) = sum4 f := by
  unfold sum4
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

lemma sum4_cycle234 (f : ι → ι → ι → ι → ℝ) :
    sum4 (fun i j k l => f i l j k) = sum4 f := by
  calc
    _ = sum4 (fun i j k l => f i k j l) :=
      sum4_swap34 (fun i j k l => f i k j l)
    _ = sum4 f := sum4_swap23 f

/-- The crossing contraction is bounded by the actual squared tensor norm. -/
lemma calabi_cross_le_square (F : ι → ι → ι → ι → ℝ) :
    sum4 (fun i j k l => F i j k l * F i k j l) ≤ sum4 (fun i j k l => F i j k l ^ 2) := by
  have hp := sum4_nonneg (fun i j k l => sq_nonneg (F i j k l - F i k j l))
  have he : sum4 (fun i j k l => (F i j k l - F i k j l) ^ 2) =
      2 * sum4 (fun i j k l => F i j k l ^ 2) -
        2 * sum4 (fun i j k l => F i j k l * F i k j l) := by
    calc
      _ = sum4 (fun i j k l => F i j k l ^ 2 + F i k j l ^ 2 -
        2 * (F i j k l * F i k j l)) := sum4_congr (fun _ _ _ _ => by ring)
      _ = _ := by rw [sum4_sub, sum4_add, sum4_const_mul, sum4_swap23]; ring
  rw [he] at hp
  linarith

/-- Calabi's exact square completion absorbs the fourth/third derivative
mixed term. The only premises are genuine tensor permutation symmetries. -/
theorem calabi_square_completion
    (F Q : ι → ι → ι → ι → ℝ)
    (hF : ∀ i j k l, F i j k l = F i j l k)
    (hQ23 : ∀ i j k l, Q i j k l = Q i k j l)
    (hQ34 : ∀ i j k l, Q i j k l = Q i j l k) :
    2 * sum4 (fun i j k l => Q i j k l ^ 2) -
        6 * sum4 (fun i j k l => Q i j k l * F i j k l) +
        3 * sum4 (fun i j k l => F i j k l ^ 2) +
        2 * sum4 (fun i j k l => F i j k l * F i k j l) ≥
      (1 / 2 : ℝ) * sum4 (fun i j k l => F i j k l ^ 2) := by
  let A := sum4 (fun i j k l => F i j k l ^ 2)
  let B := sum4 (fun i j k l => F i j k l * F i k j l)
  let M := sum4 (fun i j k l => Q i j k l * F i j k l)
  have hN₂ : sum4 (fun i j k l => F i k j l ^ 2) = A := sum4_swap23 _
  have hN₃ : sum4 (fun i j k l => F i l j k ^ 2) = A := sum4_cycle234 _
  have hM₂ : sum4 (fun i j k l => Q i j k l * F i k j l) = M := by
    calc
      _ = sum4 (fun i j k l => Q i k j l * F i k j l) := sum4_congr (fun i j k l => by rw [hQ23 i j k l])
      _ = M := sum4_swap23 _
  have hM₃ : sum4 (fun i j k l => Q i j k l * F i l j k) = M := by
    calc
      _ = sum4 (fun i j k l => Q i l j k * F i l j k) := by
        apply sum4_congr
        intro i j k l
        rw [hQ23 i l j k, hQ34 i j l k]
      _ = M := sum4_cycle234 _
  have hB₁₃ : sum4 (fun i j k l => F i j k l * F i l j k) = B := by
    calc
      _ = sum4 (fun i j k l => F i j l k * F i k j l) := (sum4_swap34 _).symm
      _ = B := sum4_congr (fun i j k l => by rw [hF i j l k])
  have hB₂₃ : sum4 (fun i j k l => F i k j l * F i l j k) = B := by
    calc
      _ = sum4 (fun i j k l => F i j k l * F i l k j) := (sum4_swap23 _).symm
      _ = sum4 (fun i j k l => F i j k l * F i l j k) :=
        sum4_congr (fun i j k l => by rw [hF i l k j])
      _ = B := hB₁₃
  have hpos := sum4_nonneg (fun i j k l =>
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (sq_nonneg (Q i j k l - (F i j k l + F i k j l + F i l j k) / 2)))
  have hid : sum4 (fun i j k l =>
      2 * (Q i j k l - (F i j k l + F i k j l + F i l j k) / 2) ^ 2) =
      2 * sum4 (fun i j k l => Q i j k l ^ 2) - 6 * M + (3 / 2 : ℝ) * A + 3 * B := by
    calc
      _ = sum4 (fun i j k l => 2 * Q i j k l ^ 2 -
          2 * (Q i j k l * F i j k l + Q i j k l * F i k j l + Q i j k l * F i l j k) +
          (1 / 2 : ℝ) * (F i j k l ^ 2 + F i k j l ^ 2 + F i l j k ^ 2) +
          (F i j k l * F i k j l + F i j k l * F i l j k + F i k j l * F i l j k)) :=
        sum4_congr (fun _ _ _ _ => by ring)
      _ = _ := by
        simp only [sum4_add, sum4_sub, sum4_const_mul, hN₂, hN₃, hM₂, hM₃, hB₁₃, hB₂₃]
        change 2 * _ - 2 * (M + M + M) + (1 / 2 : ℝ) * (A + A + A) + (B + B + B) = _
        ring
  rw [hid] at hpos
  have hAB : B ≤ A := calabi_cross_le_square F
  change 2 * _ - 6 * M + 3 * A + 2 * B ≥ (1 / 2 : ℝ) * A
  linarith

def calabiGram4 (T : ι → ι → ι → ℝ) (i j k l : ι) : ℝ :=
  ∑ p, T p i j * T p k l

def calabiCubicNorm (T : ι → ι → ι → ℝ) : ℝ := ∑ p, ∑ i, ∑ j, T p i j ^ 2

lemma sum4_sum2_exchange (f : ι → ι → ι → ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q, f i j k l p q) =
      ∑ p, ∑ q, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l p q := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun a : ι × ι × ι × ι => fun b : ι × ι => f a.1 a.2.1 a.2.2.1 a.2.2.2 b.1 b.2))

lemma calabi_gram_square_identity (T : ι → ι → ι → ℝ) :
    sum4 (fun i j k l => calabiGram4 T i j k l ^ 2) =
      ∑ p, ∑ q, (∑ i, ∑ j, T p i j * T q i j) ^ 2 := by
  unfold sum4 calabiGram4
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [sum4_sum2_exchange]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The Gram contraction dominates the square of the cubic tensor energy
with the exact dimensional constant needed by Calabi's inequality. -/
theorem calabi_gram_controls_cubic_square (T : ι → ι → ι → ℝ) :
    calabiCubicNorm T ^ 2 ≤ (Fintype.card ι : ℝ) *
      sum4 (fun i j k l => calabiGram4 T i j k l ^ 2) := by
  have hdiag : (∑ p, (∑ i, ∑ j, T p i j ^ 2) ^ 2) ≤
      ∑ p, ∑ q, (∑ i, ∑ j, T p i j * T q i j) ^ 2 := by
    apply Finset.sum_le_sum
    intro p _
    have hh := Finset.single_le_sum (f := fun q => (∑ i, ∑ j, T p i j * T q i j) ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_univ p)
    simpa only [← pow_two] using hh
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun _ : ι => (1 : ℝ)) (g := fun p => ∑ i, ∑ j, T p i j ^ 2)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hCS
  rw [calabi_gram_square_identity]
  exact hCS.trans (mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg _))

/-- The finite-dimensional normalized Calabi estimate, before substituting
actual derivatives and the differentiated Monge–Ampère equation. -/
theorem calabi_normalized_tensor_inequality
    (T : ι → ι → ι → ℝ) (Q : ι → ι → ι → ι → ℝ)
    (hT : ∀ p i j, T p i j = T p j i)
    (hQ23 : ∀ i j k l, Q i j k l = Q i k j l)
    (hQ34 : ∀ i j k l, Q i j k l = Q i j l k)
    (hn : 0 < Fintype.card ι) :
    calabiCubicNorm T ^ 2 / (2 * Fintype.card ι) ≤
      2 * sum4 (fun i j k l => Q i j k l ^ 2) -
        6 * sum4 (fun i j k l => Q i j k l * calabiGram4 T i j k l) +
        3 * sum4 (fun i j k l => calabiGram4 T i j k l ^ 2) +
        2 * sum4 (fun i j k l => calabiGram4 T i j k l * calabiGram4 T i k j l) := by
  have hF : ∀ i j k l, calabiGram4 T i j k l = calabiGram4 T i j l k := by
    intro i j k l
    unfold calabiGram4
    simp only [hT]
  have hsq := calabi_square_completion (calabiGram4 T) Q hF hQ23 hQ34
  have hgram := calabi_gram_controls_cubic_square T
  have hn' : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr hn
  apply le_trans _ hsq
  apply (div_le_iff₀ (by positivity : 0 < 2 * (Fintype.card ι : ℝ))).mpr
  nlinarith

end GaussianTilt.MomentMapRegularity
