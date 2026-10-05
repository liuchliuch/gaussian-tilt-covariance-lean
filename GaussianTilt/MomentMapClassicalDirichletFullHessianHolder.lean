import GaussianTilt.MomentMapClassicalDirichletNormalHolder

/-! # Quantitative recovery of every Hessian entry from the actual tangent shear -/
noncomputable section
open Set Matrix
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma scalar_mul_difference_bound {a b c d B C ε η : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : |a| ≤ B) (hd : |d| ≤ C) (hab : |a-b| ≤ ε) (hcd : |c-d| ≤ η) :
    |a*c-b*d| ≤ B*η+C*ε := by
  calc
    _ = |a*(c-d)+(a-b)*d| := by congr 1; ring
    _ ≤ |a| * |c-d|+|a-b| * |d| := by simpa only [abs_mul] using abs_add_le (a*(c-d)) ((a-b)*d)
    _ ≤ B*η+ε*C := add_le_add (mul_le_mul ha hcd (abs_nonneg _) hB)
      (mul_le_mul hab hd (abs_nonneg _) (le_trans (abs_nonneg _) hab))
    _ = _ := by ring

lemma coordinateTangentBlock_reconstruction {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (j : Fin n) (β : {i : Fin n // i ≠ j} → ℝ)
    (a b : {i : Fin n // i ≠ j}) :
    H a b = coordinateTangentBlock H j β a b +
      β b*(H a j-β a*H j j)+β a*(H b j-β b*H j j)+β a*β b*H j j := by
  unfold coordinateTangentBlock
  rw [hH.apply j b]
  ring

/-- A finite quantitative inverse to the tangent shear. Every entry, not
just the normal-normal one, has a controlled difference. -/
theorem coordinate_hessian_difference_of_adapted_bounds
    {H G : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) (hG : G.IsSymm)
    (j : Fin n) {β γ : {i : Fin n // i ≠ j} → ℝ} {B K N ε : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hN : 0 ≤ N) (hε : 0 ≤ ε)
    (hβ : ∀ a, |β a| ≤ B) (hγ : ∀ a, |γ a| ≤ B)
    (hmH : ∀ a : {i : Fin n // i ≠ j}, |H a j-β a*H j j| ≤ K)
    (hmG : ∀ a : {i : Fin n // i ≠ j}, |G a j-γ a*G j j| ≤ K)
    (hnH : |H j j| ≤ N) (hnG : |G j j| ≤ N)
    (hβγ : ∀ a, |β a-γ a| ≤ ε)
    (hTang : ∀ a b, |coordinateTangentBlock H j β a b-coordinateTangentBlock G j γ a b| ≤ ε)
    (hMixed : ∀ a : {i : Fin n // i ≠ j}, |(H a j-β a*H j j)-(G a j-γ a*G j j)| ≤ ε)
    (hNormal : |H j j-G j j| ≤ ε) :
    ∀ i l, |H i l-G i l| ≤
      (1+(1+B+N)+(1+2*(B+K)+B^2+2*B*N))*ε := by
  have hcross (a : {i : Fin n // i ≠ j}) : |H a j-G a j| ≤ (1+B+N)*ε := by
    have hh := scalar_mul_difference_bound hB hN (hβ a) hnG (hβγ a) hNormal
    have he : H a j-G a j = ((H a j-β a*H j j)-(G a j-γ a*G j j))+
        (β a*H j j-γ a*G j j) := by ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith [hMixed a])
  have htang (a b : {i : Fin n // i ≠ j}) : |H a b-G a b| ≤ (1+2*(B+K)+B^2+2*B*N)*ε := by
    have h1 := scalar_mul_difference_bound hB hK (hβ b) (hmG a) (hβγ b) (hMixed a)
    have h2 := scalar_mul_difference_bound hB hK (hβ a) (hmG b) (hβγ a) (hMixed b)
    have hbb := scalar_mul_difference_bound hB hB (hβ a) (hγ b) (hβγ a) (hβγ b)
    have hβb : |β a*β b| ≤ B^2 := by rw [abs_mul]; simpa only [pow_two] using mul_le_mul (hβ a) (hβ b) (abs_nonneg _) hB
    have h3 := scalar_mul_difference_bound (sq_nonneg B) hN hβb hnG hbb hNormal
    rw [coordinateTangentBlock_reconstruction hH j β a b,coordinateTangentBlock_reconstruction hG j γ a b]
    have he : coordinateTangentBlock H j β a b + β b*(H a j-β a*H j j)+
        β a*(H b j-β b*H j j)+β a*β b*H j j -
        (coordinateTangentBlock G j γ a b+γ b*(G a j-γ a*G j j)+
        γ a*(G b j-γ b*G j j)+γ a*γ b*G j j) =
        (coordinateTangentBlock H j β a b-coordinateTangentBlock G j γ a b)+
        (β b*(H a j-β a*H j j)-γ b*(G a j-γ a*G j j))+
        (β a*(H b j-β b*H j j)-γ a*(G b j-γ b*G j j))+
        (β a*β b*H j j-γ a*γ b*G j j) := by ring
    rw [he]
    calc
      _ ≤ |coordinateTangentBlock H j β a b-coordinateTangentBlock G j γ a b|+
          |β b*(H a j-β a*H j j)-γ b*(G a j-γ a*G j j)|+
          |β a*(H b j-β b*H j j)-γ a*(G b j-γ b*G j j)|+
          |β a*β b*H j j-γ a*γ b*G j j| :=
        (abs_add_le _ _).trans (add_le_add_right ((abs_add_le _ _).trans
          (add_le_add_right (abs_add_le _ _) _)) _)
      _ ≤ _ := by nlinarith [hTang a b]
  intro i l
  by_cases hi : i = j
  · subst i
    by_cases hl : l = j
    · subst l
      apply hNormal.trans
      nlinarith [sq_nonneg B,mul_nonneg hB hN]
    · rw [hH.apply l j,hG.apply l j]
      apply (hcross ⟨l,hl⟩).trans
      nlinarith [sq_nonneg B,mul_nonneg hB hN]
  · by_cases hl : l = j
    · subst l
      apply (hcross ⟨i,hi⟩).trans
      nlinarith [sq_nonneg B,mul_nonneg hB hN]
    · apply (htang ⟨i,hi⟩ ⟨l,hl⟩).trans
      nlinarith

/-- Hölder tangent and adapted mixed data recover the full original
Hessian. The normal modulus is proved from the determinant equation, with
no separately assumed inverse or determinant Hölder estimate. -/
theorem coordinate_full_hessian_holder
    {X : Type*} [PseudoMetricSpace X] {S : Set X}
    (j : Fin n) {H : X → Matrix (Fin n) (Fin n) ℝ}
    {β : X → {i : Fin n // i ≠ j} → ℝ} {δ I K M F L B N α : ℝ}
    (hδ : 0 < δ) (hI : 0 ≤ I) (hK : 0 ≤ K) (hM : 0 ≤ M) (hF : 0 ≤ F) (hL : 0 ≤ L)
    (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hsym : ∀ x ∈ S, (H x).IsSymm)
    (hp : ∀ x ∈ S, (coordinateTangentBlock (H x) j (β x)).PosDef)
    (hd : ∀ x ∈ S, δ ≤ (coordinateTangentBlock (H x) j (β x)).det)
    (hA : ∀ x ∈ S, ∀ a b, |coordinateTangentBlock (H x) j (β x) a b| ≤ M)
    (hInv : ∀ x ∈ S, ∀ a b, |(coordinateTangentBlock (H x) j (β x))⁻¹ a b| ≤ I)
    (hb : ∀ x ∈ S, ∀ a : {i : Fin n // i ≠ j}, |H x a j-β x a*H x j j| ≤ K)
    (hdet : ∀ x ∈ S, |(H x).det| ≤ F)
    (hβ : ∀ x ∈ S, ∀ a, |β x a| ≤ B) (hNormal : ∀ x ∈ S, |H x j j| ≤ N)
    (hAH : ∀ x ∈ S, ∀ y ∈ S, ∀ a b,
      |coordinateTangentBlock (H x) j (β x) a b-coordinateTangentBlock (H y) j (β y) a b| ≤ L*dist x y^α)
    (hbH : ∀ x ∈ S, ∀ y ∈ S, ∀ a : {i : Fin n // i ≠ j},
      |(H x a j-β x a*H x j j)-(H y a j-β y a*H y j j)| ≤ L*dist x y^α)
    (hfH : ∀ x ∈ S, ∀ y ∈ S, |(H x).det-(H y).det| ≤ L*dist x y^α)
    (hβH : ∀ x ∈ S, ∀ y ∈ S, ∀ a, |β x a-β y a| ≤ L*dist x y^α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ i l, |H x i l-H y i l| ≤ C*dist x y^α := by
  obtain ⟨C₀,hC₀,hc⟩ := coordinate_normal_hessian_holder j hδ hI hK hM hF hL
    hsym hp hd hA hInv hb hdet hAH hbH hfH
  let Q := 1+(1+B+N)+(1+2*(B+K)+B^2+2*B*N)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨Q*max L C₀,mul_nonneg hQ (hL.trans (le_max_left _ _)),?_⟩
  intro x hx y hy i l
  have hdxy : 0 ≤ dist x y^α := Real.rpow_nonneg (dist_nonneg) _
  have hLL : L*dist x y^α ≤ max L C₀*dist x y^α := mul_le_mul_of_nonneg_right (le_max_left _ _) hdxy
  have hCC : C₀*dist x y^α ≤ max L C₀*dist x y^α := mul_le_mul_of_nonneg_right (le_max_right _ _) hdxy
  have hh := coordinate_hessian_difference_of_adapted_bounds (hsym x hx) (hsym y hy) j hB hK hN
    (mul_nonneg (hL.trans (le_max_left _ _)) hdxy) (hβ x hx) (hβ y hy)
    (hb x hx) (hb y hy) (hNormal x hx) (hNormal y hy)
    (fun a => (hβH x hx y hy a).trans hLL)
    (fun a b => (hAH x hx y hy a b).trans hLL)
    (fun a => (hbH x hx y hy a).trans hLL) ((hc x hx y hy).trans hCC) i l
  exact hh.trans_eq (by dsimp [Q]; ring)

end GaussianTilt.MomentMapRegularity
