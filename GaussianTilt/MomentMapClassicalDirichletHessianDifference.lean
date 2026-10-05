import GaussianTilt.MomentMapClassicalDirichletTangentFieldRecovery

/-! # Pairwise Hessian recovery for genuine boundary approach estimates -/
noncomputable section
open Set Matrix
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- A fixed quantitative inverse estimate for the tangent shear on the
uniformly positive matrix class. It applies directly to an interior point
and a boundary point, without a pairwise Hölder assumption on a set. -/
theorem exists_coordinate_hessian_difference_bound
    (q : Fin n) {c K B F : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hB : 0 ≤ B) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H G : Matrix (Fin n) (Fin n) ℝ,
      H.PosDef → G.PosDef → c ≤ H.det → c ≤ G.det →
      (∀ i l, |H i l| ≤ K) → (∀ i l, |G i l| ≤ K) → |G.det| ≤ F →
      ∀ β γ : TangentIndex q → ℝ, (∀ a, |β a| ≤ B) → (∀ a, |γ a| ≤ B) →
      ∀ ε : ℝ, 0 ≤ ε → (∀ a, |β a-γ a| ≤ ε) →
      (∀ a b, |coordinateTangentBlock H q β a b-coordinateTangentBlock G q γ a b| ≤ ε) →
      (∀ a : TangentIndex q, |(H a q-β a*H q q)-(G a q-γ a*G q q)| ≤ ε) →
      |H.det-G.det| ≤ ε → ∀ i l, |H i l-G i l| ≤ C*ε := by
  obtain ⟨δ,I,T,hδ,hI,hT,hbounds⟩ := exists_uniform_coordinateTangentBlock_bounds q hc hK hB
  let M := (1+B)*K
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨C₀,hC₀,hSchur⟩ := exists_normalBlockMatrix_normal_lipschitz (ι := TangentIndex q) hδ hI.le hM hT.le hF
  let Q := 1+(1+B+K)+(1+2*(B+M)+B^2+2*B*K)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨Q*max 1 C₀,mul_nonneg hQ (zero_le_one.trans (le_max_left _ _)),?_⟩
  intro H G hH hG hdH hdG hHE hGE hf β γ hβ hγ ε hε hβγ hTang hMixed hdet i l
  have hsH : H.IsSymm := by simpa only [Matrix.IsSymm,Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hH.isHermitian
  have hsG : G.IsSymm := by simpa only [Matrix.IsSymm,Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hG.isHermitian
  have hHB := hbounds H hH hdH hHE β hβ
  have hGB := hbounds G hG hdG hGE γ hγ
  have hmixed (A : Matrix (Fin n) (Fin n) ℝ) (b : TangentIndex q → ℝ)
      (hA : ∀ i l, |A i l| ≤ K) (hb : ∀ a, |b a| ≤ B) (a : TangentIndex q) :
      |A a q-b a*A q q| ≤ M := by
    calc
      _ ≤ |A a q|+|b a| * |A q q| := by simpa only [abs_mul] using abs_sub (A a q) (b a*A q q)
      _ ≤ K+B*K := by gcongr <;> first | exact hA _ _ | exact hb _
      _ = M := by dsimp [M]; ring
  have hn : |H q q-G q q| ≤ C₀*ε := by
    apply hSchur _ _ (fun a : TangentIndex q => H a q-β a*H q q)
      (fun a : TangentIndex q => G a q-γ a*G q q) (H q q) (G q q) ε
      hHB.1 hGB.1 hHB.2.1 hGB.2.1 hHB.2.2.2 hGB.2.2.2 hHB.2.2.1 hGB.2.2.1
      (hmixed H β hHE hβ) (hmixed G γ hGE hγ)
    · rwa [coordinate_normalBlockMatrix_det hsG]
    · exact hε
    · exact hTang
    · exact hMixed
    · rwa [coordinate_normalBlockMatrix_det hsH,coordinate_normalBlockMatrix_det hsG]
  have hεe : ε ≤ max 1 C₀*ε := by nlinarith [mul_le_mul_of_nonneg_right (le_max_left 1 C₀) hε]
  have hne : C₀*ε ≤ max 1 C₀*ε := mul_le_mul_of_nonneg_right (le_max_right _ _) hε
  have hh := coordinate_hessian_difference_of_adapted_bounds hsH hsG q hB hM hK
    (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hε) hβ hγ
    (hmixed H β hHE hβ) (hmixed G γ hGE hγ) (hHE q q) (hGE q q)
    (fun a => (hβγ a).trans hεe) (fun a b => (hTang a b).trans hεe)
    (fun a => (hMixed a).trans hεe) (hn.trans hne) i l
  exact hh.trans_eq (by dsimp [Q]; ring)

/-- Pairwise recovery directly from the real tangential-field identity.
This is the form used for approach from an interior point to a boundary
point before the independent global Hölder gluing theorem is applied. -/
theorem exists_hessian_difference_bound_of_tangent_field_data
    (q : Fin n) {c K B B₁ U P F : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hB₁ : 0 ≤ B₁) (hU : 0 ≤ U) (hP : 0 ≤ P) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H G : Matrix (Fin n) (Fin n) ℝ,
      H.PosDef → G.PosDef → c ≤ H.det → c ≤ G.det →
      (∀ i l, |H i l| ≤ K) → (∀ i l, |G i l| ≤ K) → |G.det| ≤ F →
      ∀ β γ : TangentIndex q → ℝ, ∀ β₁ γ₁ W V : TangentIndex q → Fin n → ℝ, ∀ u v : ℝ,
      (∀ a, |β a| ≤ B) → (∀ a, |γ a| ≤ B) →
      (∀ a k, |β₁ a k| ≤ B₁) → (∀ a k, |γ₁ a k| ≤ B₁) →
      |u| ≤ U → |v| ≤ U → (∀ a k, |W a k| ≤ P) → (∀ a k, |V a k| ≤ P) →
      (∀ a k, W a k = H a k-β a*H q k-β₁ a k*u) →
      (∀ a k, V a k = G a k-γ a*G q k-γ₁ a k*v) →
      ∀ ε : ℝ, 0 ≤ ε → (∀ a, |β a-γ a| ≤ ε) →
      (∀ a k, |β₁ a k-γ₁ a k| ≤ ε) → |u-v| ≤ ε →
      (∀ a k, |W a k-V a k| ≤ ε) → |H.det-G.det| ≤ ε →
      ∀ i l, |H i l-G i l| ≤ C*ε := by
  obtain ⟨C₀,hC₀,hrecover⟩ := exists_coordinate_hessian_difference_bound q hc hK hB hF
  let Cₘ := 1+B₁+U
  let Cₜ := 1+(B+P)+(B₁+U)+B*B₁+U*(B+B₁)
  let R := max 1 (max Cₘ Cₜ)
  have hR : 0 ≤ R := zero_le_one.trans (le_max_left _ _)
  refine ⟨C₀*R,mul_nonneg hC₀ hR,?_⟩
  intro H G hH hG hdH hdG hHE hGE hf β γ β₁ γ₁ W V u v hβ hγ hβ₁ hγ₁ hu hv hW hV heH heG ε hε hb hb₁ huv hWV hdet i l
  have hrec := adapted_hessian_difference_of_tangent_field_difference q hB hB₁ hU hP hε
    hβ hγ hβ₁ hγ₁ hu hv hW hV heH heG hb hb₁ huv hWV
  have hεR : ε ≤ R*ε := by
    have hh := mul_le_mul_of_nonneg_right (le_max_left 1 (max Cₘ Cₜ)) hε
    simpa only [one_mul] using hh
  have hmR : Cₘ*ε ≤ R*ε := mul_le_mul_of_nonneg_right
    ((le_max_left Cₘ Cₜ).trans (le_max_right _ _)) hε
  have htR : Cₜ*ε ≤ R*ε := mul_le_mul_of_nonneg_right
    ((le_max_right Cₘ Cₜ).trans (le_max_right _ _)) hε
  have hh := hrecover H G hH hG hdH hdG hHE hGE hf β γ hβ hγ (R*ε) (mul_nonneg hR hε)
    (fun a => (hb a).trans hεR) (fun a b => (hrec.2 a b).trans htR)
    (fun a => (hrec.1 a).trans hmR) (hdet.trans hεR) i l
  exact hh.trans_eq (by ring)

end GaussianTilt.MomentMapRegularity
