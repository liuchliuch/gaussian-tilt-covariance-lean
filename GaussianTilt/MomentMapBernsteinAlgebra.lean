import Mathlib

/-! # Finite Bernstein coercivity for the logarithmic gradient equation -/
noncomputable section
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity

lemma twice_le_add_of_sq_le_mul {x U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hx : x ^ 2 ≤ U * V) : 2 * x ≤ U + V := by
  nlinarith [sq_nonneg (U - V)]

/-- The scalar absorption step, with constants fixed before the fields.
The negative cubic term is absorbed by the quartic coercivity supplied by
ellipticity and the logarithmic PDE. -/
theorem bernstein_scalar_constants {ell a b G N : ℝ}
    (hell : 0 < ell) (ha : 0 ≤ a) (hb : 0 ≤ b) (hG : 0 ≤ G) (hN : 0 ≤ N) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ S Q E T X Y Z : ℝ,
      0 ≤ S → 0 ≤ Q → ell * Q ≤ E → T ^ 2 ≤ b * Q → ell * S ≤ G - T →
      X ^ 2 ≤ a * S * Q → Y ^ 2 ≤ a * S ^ 3 →
      -(G * N + 3 * G * S) ≤ 2 * Z →
      c * S ^ 2 ≤ 2 * E - 2 * X - 2 * Y + 2 * Z + C * (S + 1) := by
  let c := ell ^ 3 / (4 * (b + 1))
  let A := a / ell + a / c + 3 * G
  let B := ell * G ^ 2 / (b + 1) + G * N
  have hc : 0 < c := by dsimp [c]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨c, A + B, hc, add_nonneg hA hB, ?_⟩
  intro S Q E T X Y Z hS hQ hE hT hP hX hY hZ
  have hX' : 2 * X ≤ ell * Q + (a / ell) * S := by
    apply twice_le_add_of_sq_le_mul (mul_nonneg hell.le hQ) (by positivity)
    convert hX using 1 <;> field_simp <;> ring
  have hY' : 2 * Y ≤ c * S ^ 2 + (a / c) * S := by
    apply twice_le_add_of_sq_le_mul (by positivity) (by positivity)
    convert hY using 1 <;> field_simp <;> ring
  have hsq : (ell * S) ^ 2 ≤ (G - T) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hell.le hS) hP 2
  have hPQ : ell ^ 2 * S ^ 2 ≤ 2 * G ^ 2 + 2 * b * Q := by
    nlinarith [sq_nonneg (G + T)]
  have hPQ' : 2 * c * S ^ 2 ≤ ell * Q + ell * G ^ 2 / (b + 1) := by
    have hmul := mul_le_mul_of_nonneg_left hPQ (show 0 ≤ ell / (2 * (b + 1)) by positivity)
    dsimp [c]
    field_simp at hmul ⊢
    nlinarith [mul_nonneg hell.le hQ]
  dsimp [A, B] at *
  nlinarith [mul_nonneg hB hS]

variable {n : ℕ}

lemma sum_abs_le_half_squares (g : Fin n → ℝ) :
    ∑ k, |g k| ≤ ((n : ℝ) + ∑ k, g k ^ 2) / 2 := by
  have hh : ∀ k, 2 * |g k| ≤ 1 + g k ^ 2 := by
    intro k
    nlinarith [sq_nonneg (|g k| - 1), sq_abs (g k)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hh k)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  linarith

lemma square_sum_pair_bound (A H : Fin n → Fin n → ℝ) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hA : ∀ i j, |A i j| ≤ Λ) :
    (∑ i, ∑ j, A i j * H i j) ^ 2 ≤ (n : ℝ) ^ 2 * Λ ^ 2 * (∑ i, ∑ j, H i j ^ 2) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun p : Fin n × Fin n => A p.1 p.2) (g := fun p => H p.1 p.2)
  simp only [Fintype.sum_prod_type] at hc
  have hb : (∑ i, ∑ j, A i j ^ 2) ≤ (n : ℝ) ^ 2 * Λ ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, Λ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (A i j)) (hA i j) 2
      _ = _ := by simp; ring
  exact hc.trans (mul_le_mul_of_nonneg_right hb (by positivity))

lemma square_sum_triple_bound (B V : Fin n → Fin n → Fin n → ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hB : ∀ k i j, |B k i j| ≤ K) :
    (∑ k, ∑ i, ∑ j, B k i j * V k i j) ^ 2 ≤
      (n : ℝ) ^ 3 * K ^ 2 * (∑ k, ∑ i, ∑ j, V k i j ^ 2) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun p : Fin n × Fin n × Fin n => B p.1 p.2.1 p.2.2)
    (g := fun p => V p.1 p.2.1 p.2.2)
  simp only [Fintype.sum_prod_type] at hc
  have hb : (∑ k, ∑ i, ∑ j, B k i j ^ 2) ≤ (n : ℝ) ^ 3 * K ^ 2 := by
    calc
      _ ≤ ∑ _k : Fin n, ∑ _i : Fin n, ∑ _j : Fin n, K ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (B k i j)) (hB k i j) 2
      _ = _ := by simp; ring
  exact hc.trans (mul_le_mul_of_nonneg_right hb (by positivity))


/-- Finite-dimensional Bernstein coercivity for the exact differentiated
logarithmic equation. Constants depend only on dimension and the displayed
coefficient/forcing bounds, and are fixed before all pointwise fields. -/
theorem bernstein_log_gradient_coercivity {ell Λ K G : ℝ}
    (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) (hG : 0 ≤ G) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ (A H : Fin n → Fin n → ℝ) (B : Fin n → Fin n → Fin n → ℝ)
        (g dh : Fin n → ℝ) (h : ℝ),
      (∀ v : Fin n → ℝ, ell * (∑ i, v i ^ 2) ≤ ∑ i, ∑ j, A i j * v i * v j) →
      (∀ i j, |A i j| ≤ Λ) → (∀ k i j, |B k i j| ≤ K) → |h| ≤ G →
      (∀ k, |dh k| ≤ G * (1 + |g k|)) →
      (∑ i, ∑ j, A i j * H i j) + (∑ i, ∑ j, A i j * g i * g j) = h →
      c * (∑ k, g k ^ 2) ^ 2 ≤
        2 * (∑ k, ∑ i, ∑ j, A i j * H i k * H j k) -
        2 * (∑ k, ∑ i, ∑ j, g k * B k i j * H i j) -
        2 * (∑ k, ∑ i, ∑ j, g k * g i * B k i j * g j) +
        2 * (∑ k, g k * dh k) + C * ((∑ k, g k ^ 2) + 1) := by
  let a := (n : ℝ) ^ 3 * K ^ 2
  let b := (n : ℝ) ^ 2 * Λ ^ 2
  obtain ⟨c, C, hc, hC, hscalar⟩ := bernstein_scalar_constants hell
    (show 0 ≤ a by dsimp [a]; positivity) (show 0 ≤ b by dsimp [b]; positivity)
    hG (show 0 ≤ (n : ℝ) by positivity)
  refine ⟨c, C, hc, hC, ?_⟩
  intro A H B g dh h hA hAb hBb hh hd hP
  let S := ∑ k, g k ^ 2
  let Q := ∑ i, ∑ j, H i j ^ 2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have henergy : ell * Q ≤ ∑ k, ∑ i, ∑ j, A i j * H i k * H j k := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hA (fun i => H i k))
    rw [← Finset.mul_sum] at hs
    convert hs using 1
    exact congrArg (ell * ·) (Finset.sum_comm)
  have htrace := square_sum_pair_bound A H hΛ hAb
  have hp : ell * S ≤ G - (∑ i, ∑ j, A i j * H i j) := by
    have he := hA g
    have hh' := le_trans (le_abs_self h) hh
    dsimp [S]
    linarith
  have hX : (∑ k, ∑ i, ∑ j, g k * B k i j * H i j) ^ 2 ≤ a * S * Q := by
    have hx := square_sum_triple_bound B (fun k i j => g k * H i j) hK hBb
    have he : (∑ k, ∑ i, ∑ j, (g k * H i j) ^ 2) = S * Q := by
      simp only [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
      rfl
    rw [he] at hx
    convert hx using 1
    · congr 1
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · dsimp [a]; ring
  have hY : (∑ k, ∑ i, ∑ j, g k * g i * B k i j * g j) ^ 2 ≤ a * S ^ 3 := by
    have hy := square_sum_triple_bound B (fun k i j => g k * g i * g j) hK hBb
    have he : (∑ k, ∑ i, ∑ j, (g k * g i * g j) ^ 2) = S ^ 3 := by
      simp only [mul_pow, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      dsimp [S]
      ring
    rw [he] at hy
    convert hy using 1
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hforce : -(G * (n : ℝ) + 3 * G * S) ≤ 2 * ∑ k, g k * dh k := by
    have hpw : ∀ k, -(G * |g k| + G * g k ^ 2) ≤ g k * dh k := by
      intro k
      have hb := mul_le_mul_of_nonneg_left (hd k) (abs_nonneg (g k))
      have ha := neg_abs_le (g k * dh k)
      rw [abs_mul] at ha
      nlinarith [sq_abs (g k)]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hpw k)
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    have ha := mul_le_mul_of_nonneg_left (sum_abs_le_half_squares g) hG
    dsimp [S]
    nlinarith
  exact hscalar S Q _ _ _ _ _ hS hQ henergy htrace hp hX hY hforce

end GaussianTilt.MomentMapRegularity
