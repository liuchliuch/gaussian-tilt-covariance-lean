import GaussianTilt.MomentMapClassicalDirichletFullHessianHolder
import GaussianTilt.MomentMapClassicalDirichletIntrinsicLipschitz
import GaussianTilt.MomentMapClassicalDirichletTangentUniformBounds

/-! # Actual adapted Hessian entries recovered from tangential-field gradients -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Matrix
open scoped Topology BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

lemma intrinsic_adaptedMixed_eq_tangentDifferential
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) (β : CoordinateSpace n → ℝ)
    (a q : Fin n) (x : CoordinateSpace n) :
    intrinsicHessian hS α j x a q-β x*intrinsicHessian hS α j x q q =
      intrinsicTangentDifferential hS α j β a q x (Pi.single q 1)+
        coordinateDerivative q β x*intrinsicDerivative hS α j q x := by
  rw [intrinsicTangentDifferential_apply_coordinate]
  ring

lemma intrinsic_tangentBlock_eq_tangentDifferential
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) (q : Fin n)
    (β : TangentIndex q → CoordinateSpace n → ℝ) (x : CoordinateSpace n)
    (a b : TangentIndex q) :
    coordinateTangentBlock (intrinsicHessian hS α j x) q (fun a => β a x) a b =
      intrinsicTangentDifferential hS α j (β a) a q x (Pi.single b 1)-
      β b x*intrinsicTangentDifferential hS α j (β a) a q x (Pi.single q 1)+
      coordinateDerivative b (β a) x*intrinsicDerivative hS α j q x-
      β b x*coordinateDerivative q (β a) x*intrinsicDerivative hS α j q x := by
  rw [intrinsicTangentDifferential_apply_coordinate,intrinsicTangentDifferential_apply_coordinate]
  unfold coordinateTangentBlock
  ring

/-- A quantitative finite algebra estimate for the actual tangential
field identity. This controls tangent as well as mixed entries from their
true first derivatives; boundary tangent regularity is not assumed. -/
theorem adapted_hessian_difference_of_tangent_field_difference
    (q : Fin n) {H G : Matrix (Fin n) (Fin n) ℝ}
    {β γ : TangentIndex q → ℝ} {β₁ γ₁ W V : TangentIndex q → Fin n → ℝ}
    {u v B B₁ U P ε : ℝ} (hB : 0 ≤ B) (hB₁ : 0 ≤ B₁) (hU : 0 ≤ U) (hP : 0 ≤ P) (hε : 0 ≤ ε)
    (hβ : ∀ a, |β a| ≤ B) (hγ : ∀ a, |γ a| ≤ B)
    (hβ₁ : ∀ a k, |β₁ a k| ≤ B₁) (hγ₁ : ∀ a k, |γ₁ a k| ≤ B₁)
    (hu : |u| ≤ U) (hv : |v| ≤ U) (hW : ∀ a k, |W a k| ≤ P) (hV : ∀ a k, |V a k| ≤ P)
    (heH : ∀ a k, W a k = H a k-β a*H q k-β₁ a k*u)
    (heG : ∀ a k, V a k = G a k-γ a*G q k-γ₁ a k*v)
    (hb : ∀ a, |β a-γ a| ≤ ε) (hb₁ : ∀ a k, |β₁ a k-γ₁ a k| ≤ ε)
    (huv : |u-v| ≤ ε) (hWV : ∀ a k, |W a k-V a k| ≤ ε) :
    (∀ a : TangentIndex q, |(H a q-β a*H q q)-(G a q-γ a*G q q)| ≤ (1+B₁+U)*ε) ∧
    (∀ a b, |coordinateTangentBlock H q β a b-coordinateTangentBlock G q γ a b| ≤
      (1+(B+P)+(B₁+U)+B*B₁+U*(B+B₁))*ε) := by
  constructor
  · intro a
    have hp := scalar_mul_difference_bound hB₁ hU (hβ₁ a q) hv (hb₁ a q) huv
    have he : (H a q-β a*H q q)-(G a q-γ a*G q q) =
        (W a q-V a q)+(β₁ a q*u-γ₁ a q*v) := by rw [heH,heG]; ring
    rw [he]
    exact (abs_add_le _ _).trans (by nlinarith [hWV a q])
  · intro a b
    have h1 := scalar_mul_difference_bound hB hP (hβ b) (hV a q) (hb b) (hWV a q)
    have h2 := scalar_mul_difference_bound hB₁ hU (hβ₁ a b) hv (hb₁ a b) huv
    have hp := scalar_mul_difference_bound hB hB₁ (hβ b) (hγ₁ a q) (hb b) (hb₁ a q)
    have hprod : |β b*β₁ a q| ≤ B*B₁ := by
      rw [abs_mul]
      exact mul_le_mul (hβ b) (hβ₁ a q) (abs_nonneg _) hB
    have h3 := scalar_mul_difference_bound (mul_nonneg hB hB₁) hU hprod hv hp huv
    have he : coordinateTangentBlock H q β a b-coordinateTangentBlock G q γ a b =
        (W a b-V a b)-(β b*W a q-γ b*V a q)+(β₁ a b*u-γ₁ a b*v)-
        (β b*β₁ a q*u-γ b*γ₁ a q*v) := by
      rw [heH,heH,heG,heG]
      unfold coordinateTangentBlock
      ring
    rw [he]
    calc
      _ ≤ |W a b-V a b|+|β b*W a q-γ b*V a q|+|β₁ a b*u-γ₁ a b*v|+
          |β b*β₁ a q*u-γ b*γ₁ a q*v| :=
        (abs_sub _ _).trans (add_le_add_right ((abs_add_le _ _).trans (add_le_add_right (abs_sub _ _) _)) _)
      _ ≤ _ := by nlinarith [hWV a b]

/-- Full Hessian Hölder control follows from the actual tangential-field
gradient modulus, lower-order chart data, a Hessian supremum bound, and
the literal determinant equation. No tangent-block or normal-entry
modulus is assumed. -/
theorem hessian_holder_of_tangent_field_holder
    {X : Type*} [PseudoMetricSpace X] {S : Set X} (q : Fin n)
    {H : X → Matrix (Fin n) (Fin n) ℝ} {β : X → TangentIndex q → ℝ}
    {β₁ W : X → TangentIndex q → Fin n → ℝ} {u : X → ℝ}
    {c K B B₁ U F L α : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hB₁ : 0 ≤ B₁) (hU : 0 ≤ U) (hF : 0 ≤ F) (hL : 0 ≤ L)
    (hp : ∀ x ∈ S, (H x).PosDef) (hd : ∀ x ∈ S, c ≤ (H x).det)
    (hH : ∀ x ∈ S, ∀ i l, |H x i l| ≤ K) (hf : ∀ x ∈ S, |(H x).det| ≤ F)
    (hb : ∀ x ∈ S, ∀ a, |β x a| ≤ B) (hb₁ : ∀ x ∈ S, ∀ a k, |β₁ x a k| ≤ B₁)
    (hu : ∀ x ∈ S, |u x| ≤ U)
    (he : ∀ x ∈ S, ∀ a k, W x a k = H x a k-β x a*H x q k-β₁ x a k*u x)
    (hβmod : ∀ x ∈ S, ∀ y ∈ S, ∀ a, |β x a-β y a| ≤ L*dist x y^α)
    (hβ₁mod : ∀ x ∈ S, ∀ y ∈ S, ∀ a k, |β₁ x a k-β₁ y a k| ≤ L*dist x y^α)
    (humod : ∀ x ∈ S, ∀ y ∈ S, |u x-u y| ≤ L*dist x y^α)
    (hWmod : ∀ x ∈ S, ∀ y ∈ S, ∀ a k, |W x a k-W y a k| ≤ L*dist x y^α)
    (hfmod : ∀ x ∈ S, ∀ y ∈ S, |(H x).det-(H y).det| ≤ L*dist x y^α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ i l, |H x i l-H y i l| ≤ C*dist x y^α := by
  obtain ⟨δ,I,T,hδ,hI,hT,hbounds⟩ := exists_uniform_coordinateTangentBlock_bounds q hc hK hB
  let P := (1+B)*K+B₁*U
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hW (x : X) (hx : x ∈ S) (a : TangentIndex q) (k : Fin n) : |W x a k| ≤ P := by
    rw [he x hx a k]
    calc
      _ ≤ |H x a k|+|β x a| * |H x q k|+|β₁ x a k| * |u x| := by
        calc
          _ ≤ _ := (abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)
          _ = _ := by simp only [abs_mul]
      _ ≤ K+B*K+B₁*U := by gcongr <;> first | exact hH x hx _ _ | exact hb x hx _ | exact hb₁ x hx _ _ | exact hu x hx
      _ = P := by dsimp [P]; ring
  let Cₘ := 1+B₁+U
  let Cₜ := 1+(B+P)+(B₁+U)+B*B₁+U*(B+B₁)
  let D := max L (max (Cₘ*L) (Cₜ*L))
  have hD : 0 ≤ D := hL.trans (le_max_left _ _)
  have hLD : L ≤ D := le_max_left _ _
  have hmD : Cₘ*L ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have htD : Cₜ*L ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hrec (x : X) (hx : x ∈ S) (y : X) (hy : y ∈ S) :=
    adapted_hessian_difference_of_tangent_field_difference q hB hB₁ hU hP
      (mul_nonneg hL (Real.rpow_nonneg dist_nonneg _)) (hb x hx) (hb y hy)
      (hb₁ x hx) (hb₁ y hy) (hu x hx) (hu y hy) (hW x hx) (hW y hy)
      (he x hx) (he y hy) (hβmod x hx y hy) (hβ₁mod x hx y hy) (humod x hx y hy) (hWmod x hx y hy)
  apply coordinate_full_hessian_holder q hδ hI.le (show 0 ≤ (1+B)*K by positivity) hT.le hF hD hB hK
  · intro x hx
    simpa only [Matrix.IsSymm,Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using (hp x hx).isHermitian
  · intro x hx
    exact (hbounds (H x) (hp x hx) (hd x hx) (hH x hx) (β x) (hb x hx)).1
  · intro x hx
    exact (hbounds (H x) (hp x hx) (hd x hx) (hH x hx) (β x) (hb x hx)).2.1
  · intro x hx
    exact (hbounds (H x) (hp x hx) (hd x hx) (hH x hx) (β x) (hb x hx)).2.2.2
  · intro x hx
    exact (hbounds (H x) (hp x hx) (hd x hx) (hH x hx) (β x) (hb x hx)).2.2.1
  · intro x hx a
    calc
      _ ≤ |H x a q|+|β x a| * |H x q q| := by simpa only [abs_mul] using abs_sub (H x a q) (β x a*H x q q)
      _ ≤ K+B*K := by gcongr <;> first | exact hH x hx _ _ | exact hb x hx _
      _ = _ := by ring
  · exact hf
  · exact hb
  · intro x hx
    exact hH x hx q q
  · intro x hx y hy a b
    exact ((hrec x hx y hy).2 a b).trans (by dsimp [Cₜ] at htD; nlinarith [mul_le_mul_of_nonneg_right htD (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist x y) α)])
  · intro x hx y hy a
    exact ((hrec x hx y hy).1 a).trans (by dsimp [Cₘ] at hmD; nlinarith [mul_le_mul_of_nonneg_right hmD (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist x y) α)])
  · intro x hx y hy
    exact (hfmod x hx y hy).trans (mul_le_mul_of_nonneg_right hLD (Real.rpow_nonneg dist_nonneg _))
  · intro x hx y hy a
    exact (hβmod x hx y hy a).trans (mul_le_mul_of_nonneg_right hLD (Real.rpow_nonneg dist_nonneg _))

end GaussianTilt.MomentMapRegularity
