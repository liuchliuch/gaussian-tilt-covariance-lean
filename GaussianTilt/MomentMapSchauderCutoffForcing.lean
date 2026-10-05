import GaussianTilt.MomentMapSchauderEuclideanCutoff
import GaussianTilt.MomentMapSchauderFiniteSums

/-! # Quantitative forcing for actual localized nondivergence equations

The lower-order cutoff terms are controlled by local C¹,α data. No second
Hölder derivative enters their bounds, which is crucial for step-uniform
source difference quotients.
-/
noncomputable section
open Matrix Set Filter
open scoped BigOperators ContDiff Topology
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic

lemma localized_product_bounds {E : Type*} [NormedAddCommGroup E]
    {χ f : E → ℝ} {S : Set E} {A U L H α : ℝ}
    (hA : 0 ≤ A) (hU : 0 ≤ U) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hχb : ∀ x, |χ x| ≤ A) (hfb : ∀ x ∈ S, |f x| ≤ U)
    (hχh : ∀ x y, |χ x-χ y| ≤ L*‖x-y‖^α)
    (hfh : ∀ x ∈ S, ∀ y ∈ S, |f x-f y| ≤ H*‖x-y‖^α)
    (hsupp : ∀ x ∉ S, χ x = 0) :
    (∀ x, |χ x*f x| ≤ A*U) ∧
    (∀ x y, |χ x*f x-χ y*f y| ≤ (A*H+U*L)*‖x-y‖^α) := by
  refine ⟨?_, global_holder_cutoff_product hA hU hL hH hχb hfb hχh hfh hsupp⟩
  intro x
  by_cases hx : x ∈ S
  · rw [abs_mul]
    exact mul_le_mul (hχb x) (hfb x hx) (abs_nonneg _) hA
  · simp only [hsupp x hx, zero_mul, abs_zero]
    positivity

lemma cutoff_jets_zero_off {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ : E → ℝ} {S : Set E} (hs : tsupport χ ⊆ S) {x : E} (hx : x ∉ S) :
    χ x = 0 ∧ fderiv ℝ χ x = 0 ∧ fderiv ℝ (fderiv ℝ χ) x = 0 := by
  have he : χ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hs h))
  refine ⟨he.self_of_nhds, ?_, ?_⟩
  · rw [he.fderiv_eq]; simp
  · rw [he.fderiv.fderiv_eq]; simp

lemma abs_euclidean_linear_entry_le_norm {n : ℕ} (L : KernelSpace n →L[ℝ] ℝ) (i : Fin n) :
    |L (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤ ‖L‖ := by
  simpa only [Real.norm_eq_abs, (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i,
    mul_one] using L.le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ i)

variable {n : ℕ}

def euclideanCutoffRemainder (χ u : KernelSpace n → ℝ) (x : KernelSpace n) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  fderiv ℝ (fderiv ℝ χ) x (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j) * u x +
  2 * (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i) *
    fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))

/-- The cutoff error uses only local value and gradient data of the original
potential. All derivative-cutoff support conditions are derived. -/
theorem euclideanCutoffRemainder_bounds {χ u : KernelSpace n → ℝ} {S : Set (KernelSpace n)}
    {C₁ C₂ L₁ L₂ U D HU HD α : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hU : 0 ≤ U) (hD : 0 ≤ D) (hHU : 0 ≤ HU) (hHD : 0 ≤ HD)
    (hs : tsupport χ ⊆ S)
    (hχ₁ : ∀ x, ‖fderiv ℝ χ x‖ ≤ C₁)
    (hχ₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ C₂)
    (hχH₁ : ∀ x y, ‖fderiv ℝ χ x-fderiv ℝ χ y‖ ≤ L₁*‖x-y‖^α)
    (hχH₂ : ∀ x y, ‖fderiv ℝ (fderiv ℝ χ) x-fderiv ℝ (fderiv ℝ χ) y‖ ≤ L₂*‖x-y‖^α)
    (hu : ∀ x ∈ S, |u x| ≤ U) (hDu : ∀ x ∈ S, ‖fderiv ℝ u x‖ ≤ D)
    (huH : ∀ x ∈ S, ∀ y ∈ S, |u x-u y| ≤ HU*‖x-y‖^α)
    (hDuH : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ u x-fderiv ℝ u y‖ ≤ HD*‖x-y‖^α) :
    (∀ x i j, |euclideanCutoffRemainder χ u x i j| ≤ C₂*U+2*(C₁*D)) ∧
    (∀ x y i j, |euclideanCutoffRemainder χ u x i j-euclideanCutoffRemainder χ u y i j| ≤
      (C₂*HU+U*L₂+2*(C₁*HD+D*L₁))*‖x-y‖^α) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hP (i j : Fin n) := localized_product_bounds hC₂ hU hL₂ hHU
    (χ := fun x => fderiv ℝ (fderiv ℝ χ) x (e i) (e j))
    (fun x => (abs_euclidean_bilinear_entry_le_norm _ i j).trans (hχ₂ x)) hu
    (fun x y => (abs_euclidean_bilinear_entry_le_norm
      (fderiv ℝ (fderiv ℝ χ) x-fderiv ℝ (fderiv ℝ χ) y) i j).trans (hχH₂ x y)) huH
    (fun x hx => by dsimp only; rw [(cutoff_jets_zero_off hs hx).2.2]; simp)
  have hQ (i j : Fin n) := localized_product_bounds hC₁ hD hL₁ hHD
    (χ := fun x => fderiv ℝ χ x (e i)) (f := fun x => fderiv ℝ u x (e j))
    (fun x => (abs_euclidean_linear_entry_le_norm _ i).trans (hχ₁ x))
    (fun x hx => (abs_euclidean_linear_entry_le_norm _ j).trans (hDu x hx))
    (fun x y => (abs_euclidean_linear_entry_le_norm
      (fderiv ℝ χ x-fderiv ℝ χ y) i).trans (hχH₁ x y))
    (fun x hx y hy => (abs_euclidean_linear_entry_le_norm
      (fderiv ℝ u x-fderiv ℝ u y) j).trans (hDuH x hx y hy))
    (fun x hx => by dsimp only; rw [(cutoff_jets_zero_off hs hx).2.1]; simp)
  constructor
  · intro x i j
    apply (abs_add_le _ _).trans
    have hh := (hQ i j).1 x
    exact add_le_add ((hP i j).1 x) (by
      simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ)<2)] using
        (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)))
  · intro x y i j
    exact holder_sum_two ((hP i j).2) (by simpa only [abs_of_pos (by norm_num : (0 : ℝ)<2)]
      using (holder_const_mul ((hQ i j).2) 2)) x y

lemma euclideanEllipticOperator_cutoff_eq {χ u f : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) (hχ : ContDiff ℝ 2 χ)
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} {S : Set (KernelSpace n)}
    (hA : ∀ x, (A x).IsSymm) (hs : tsupport χ ⊆ S)
    (heq : ∀ x ∈ S, euclideanEllipticOperator (A x) u x = f x) (x : KernelSpace n) :
    euclideanEllipticOperator (A x) (fun y => χ y*u y) x =
      χ x*f x+matrixContraction (A x) (euclideanCutoffRemainder χ u x) := by
  have hprincipal : χ x*euclideanEllipticOperator (A x) u x = χ x*f x := by
    by_cases hx : x ∈ S
    · rw [heq x hx]
    · rw [(cutoff_jets_zero_off hs hx).1]; simp
  rw [euclideanEllipticOperator_mul _ hu hχ _ (hA x), hprincipal]
  simp only [euclideanEllipticOperator, euclideanEllipticCross, matrixContraction,
    euclideanCutoffRemainder, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 1
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Supremum and Hölder bounds for the literal localized forcing, from the
proved lower-order cutoff remainder and local forcing data. -/
theorem euclidean_cutoff_forcing_bounds {χ u f : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) (hχ : ContDiff ℝ 2 χ)
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} {S : Set (KernelSpace n)}
    {M K C₀ L₀ F H R HR α : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hL₀ : 0 ≤ L₀)
    (hF : 0 ≤ F) (hH : 0 ≤ H) (hR : 0 ≤ R) (hHR : 0 ≤ HR)
    (hA : ∀ x, (A x).IsSymm) (hs : tsupport χ ⊆ S)
    (hAb : ∀ x i j, |A x i j| ≤ M)
    (hAH : ∀ x y i j, |A x i j-A y i j| ≤ K*‖x-y‖^α)
    (hχb : ∀ x, |χ x| ≤ C₀)
    (hχH : ∀ x y, |χ x-χ y| ≤ L₀*‖x-y‖^α)
    (hfb : ∀ x ∈ S, |f x| ≤ F)
    (hfH : ∀ x ∈ S, ∀ y ∈ S, |f x-f y| ≤ H*‖x-y‖^α)
    (heq : ∀ x ∈ S, euclideanEllipticOperator (A x) u x = f x)
    (hRb : ∀ x i j, |euclideanCutoffRemainder χ u x i j| ≤ R)
    (hRH : ∀ x y i j, |euclideanCutoffRemainder χ u x i j-euclideanCutoffRemainder χ u y i j| ≤ HR*‖x-y‖^α) :
    (∀ x, |euclideanEllipticOperator (A x) (fun y => χ y*u y) x| ≤
      C₀*F+(n : ℝ)^2*M*R) ∧
    (∀ x y, |euclideanEllipticOperator (A x) (fun z => χ z*u z) x-
      euclideanEllipticOperator (A y) (fun z => χ z*u z) y| ≤
      (C₀*H+F*L₀+(n : ℝ)^2*(M*HR+K*R))*‖x-y‖^α) := by
  have hP := localized_product_bounds hC₀ hF hL₀ hH hχb hfb hχH hfH
    (fun x hx => (cutoff_jets_zero_off hs hx).1)
  constructor
  · intro x
    rw [euclideanEllipticOperator_cutoff_eq hu hχ hA hs heq]
    apply (abs_add_le _ _).trans
    have hb := abs_matrixContraction_le hM hR (hAb x) (hRb x)
    exact add_le_add (hP.1 x) (by simpa only [Fintype.card_fin] using hb)
  · intro x y
    rw [euclideanEllipticOperator_cutoff_eq hu hχ hA hs heq,
      euclideanEllipticOperator_cutoff_eq hu hχ hA hs heq]
    have hp := Real.rpow_nonneg (norm_nonneg (x-y)) α
    have hcon := abs_matrixContraction_sub_le hM hR (mul_nonneg hK hp) (mul_nonneg hHR hp)
      (hAb x) (hRb y) (hAH x y) (hRH x y)
    have hrh : |matrixContraction (A x) (euclideanCutoffRemainder χ u x)-
        matrixContraction (A y) (euclideanCutoffRemainder χ u y)| ≤
        ((n : ℝ)^2*(M*HR+K*R))*‖x-y‖^α := by
      exact hcon.trans_eq (by simp only [Fintype.card_fin]; ring)
    have he : χ x*f x+matrixContraction (A x) (euclideanCutoffRemainder χ u x)-
      (χ y*f y+matrixContraction (A y) (euclideanCutoffRemainder χ u y)) =
      (χ x*f x-χ y*f y)+(matrixContraction (A x) (euclideanCutoffRemainder χ u x)-
        matrixContraction (A y) (euclideanCutoffRemainder χ u y)) := by ring
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add (hP.2 x y) hrh).trans_eq (by ring))

end GaussianTilt.MomentMapSchauder
