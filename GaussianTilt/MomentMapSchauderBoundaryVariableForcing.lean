import GaussianTilt.MomentMapSchauderBoundaryVariableCutoff

/-! # Uniform lower-jet bounds for the true boundary cutoff commutator -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 1800000
open Set Matrix
open scoped ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- The cutoff remainder is bounded only by the original value and first
field; its estimate contains no original second-derivative Hölder norm. -/
theorem boundaryCutoffRemainder_bounds_on {χ u : KernelSpace n → ℝ}
    {D : KernelSpace n → KernelSpace n →L[ℝ] ℝ} {S : Set (KernelSpace n)}
    {C₁ C₂ L₁ L₂ U V HU HD α : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hHU : 0 ≤ HU) (hHD : 0 ≤ HD)
    (hχ₁ : ∀ x ∈ S, ‖fderiv ℝ χ x‖ ≤ C₁)
    (hχ₂ : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ C₂)
    (hχH₁ : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ χ x-fderiv ℝ χ y‖ ≤ L₁*‖x-y‖^α)
    (hχH₂ : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ (fderiv ℝ χ) x-fderiv ℝ (fderiv ℝ χ) y‖ ≤ L₂*‖x-y‖^α)
    (hu : ∀ x ∈ S, |u x| ≤ U) (hD : ∀ x ∈ S, ‖D x‖ ≤ V)
    (huH : ∀ x ∈ S, ∀ y ∈ S, |u x-u y| ≤ HU*‖x-y‖^α)
    (hDH : ∀ x ∈ S, ∀ y ∈ S, ‖D x-D y‖ ≤ HD*‖x-y‖^α) :
    (∀ x ∈ S, ∀ i k, |boundaryCutoffRemainder χ u D x i k| ≤ C₂*U+2*(C₁*V)) ∧
    (∀ x ∈ S, ∀ y ∈ S, ∀ i k,
      |boundaryCutoffRemainder χ u D x i k-boundaryCutoffRemainder χ u D y i k| ≤
        (C₂*HU+U*L₂+2*(C₁*HD+V*L₁))*‖x-y‖^α) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hP (i k : Fin n) : ∀ x ∈ S, ∀ y ∈ S,
      |fderiv ℝ (fderiv ℝ χ) x (e i) (e k)*u x-fderiv ℝ (fderiv ℝ χ) y (e i) (e k)*u y| ≤
        (C₂*HU+U*L₂)*‖x-y‖^α :=
    holder_product_bound hC₂ hU hL₂ hHU
      (fun x hx => (abs_euclidean_bilinear_entry_le_norm _ i k).trans (hχ₂ x hx)) hu
      (fun x hx y hy => (abs_euclidean_bilinear_entry_le_norm
        (fderiv ℝ (fderiv ℝ χ) x-fderiv ℝ (fderiv ℝ χ) y) i k).trans (hχH₂ x hx y hy)) huH
  have hQ (i k : Fin n) : ∀ x ∈ S, ∀ y ∈ S,
      |fderiv ℝ χ x (e i)*D x (e k)-fderiv ℝ χ y (e i)*D y (e k)| ≤
        (C₁*HD+V*L₁)*‖x-y‖^α :=
    holder_product_bound hC₁ hV hL₁ hHD
      (fun x hx => (abs_euclidean_linear_entry_le_norm _ i).trans (hχ₁ x hx))
      (fun x hx => (abs_euclidean_linear_entry_le_norm _ k).trans (hD x hx))
      (fun x hx y hy => (abs_euclidean_linear_entry_le_norm
        (fderiv ℝ χ x-fderiv ℝ χ y) i).trans (hχH₁ x hx y hy))
      (fun x hx y hy => (abs_euclidean_linear_entry_le_norm (D x-D y) k).trans (hDH x hx y hy))
  constructor
  · intro x hx i k
    change |fderiv ℝ (fderiv ℝ χ) x (e i) (e k)*u x+2*(fderiv ℝ χ x (e i)*D x (e k))| ≤ _
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply add_le_add
    · exact mul_le_mul ((abs_euclidean_bilinear_entry_le_norm _ i k).trans (hχ₂ x hx)) (hu x hx) (abs_nonneg _) hC₂
    · exact mul_le_mul_of_nonneg_left
        (mul_le_mul ((abs_euclidean_linear_entry_le_norm _ i).trans (hχ₁ x hx))
          ((abs_euclidean_linear_entry_le_norm _ k).trans (hD x hx)) (abs_nonneg _) hC₁) (by norm_num)
  · intro x hx y hy i k
    have he : boundaryCutoffRemainder χ u D x i k-boundaryCutoffRemainder χ u D y i k=
        (fderiv ℝ (fderiv ℝ χ) x (e i) (e k)*u x-fderiv ℝ (fderiv ℝ χ) y (e i) (e k)*u y)+
          2*(fderiv ℝ χ x (e i)*D x (e k)-fderiv ℝ χ y (e i)*D y (e k)) := by
      dsimp [boundaryCutoffRemainder,e]
      ring
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact (add_le_add (hP i k x hx y hy) (mul_le_mul_of_nonneg_left (hQ i k x hx y hy) (by norm_num))).trans_eq (by ring)

def boundaryLocalizedForcing (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (χ u : KernelSpace n → ℝ) (D : KernelSpace n → KernelSpace n →L[ℝ] ℝ)
    (f : KernelSpace n → ℝ) (x : KernelSpace n) : ℝ :=
  χ x*f x+matrixContraction (A x) (boundaryCutoffRemainder χ u D x)

lemma boundaryLocalizedForcing_eq_operator (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (χ u f : KernelSpace n → ℝ) (D : KernelSpace n → KernelSpace n →L[ℝ] ℝ)
    (B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ)
    {x : KernelSpace n} (hA : (A x).IsSymm)
    (heq : matrixContraction (A x) (bilinearEntryMatrix (B x))=f x) :
    matrixContraction (A x) (bilinearEntryMatrix (boundaryCutoffSecond χ u D B x))=
      boundaryLocalizedForcing A χ u D f x := by
  rw [boundaryCutoffSecond_contraction (A x) hA,heq]
  rfl

/-- Literal forcing bounds for localized boundary equations. Coefficients
are never differentiated, and the only solution inputs are lower jets. -/
theorem boundaryLocalizedForcing_bounds_on {χ u f : KernelSpace n → ℝ}
    {D : KernelSpace n → KernelSpace n →L[ℝ] ℝ}
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} {S : Set (KernelSpace n)}
    {M K C₀ L₀ F H R HR α : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hL₀ : 0 ≤ L₀)
    (hF : 0 ≤ F) (hH : 0 ≤ H) (hR : 0 ≤ R) (hHR : 0 ≤ HR)
    (hAb : ∀ x ∈ S, ∀ i k, |A x i k| ≤ M)
    (hAH : ∀ x ∈ S, ∀ y ∈ S, ∀ i k, |A x i k-A y i k| ≤ K*‖x-y‖^α)
    (hχb : ∀ x ∈ S, |χ x| ≤ C₀)
    (hχH : ∀ x ∈ S, ∀ y ∈ S, |χ x-χ y| ≤ L₀*‖x-y‖^α)
    (hfb : ∀ x ∈ S, |f x| ≤ F)
    (hfH : ∀ x ∈ S, ∀ y ∈ S, |f x-f y| ≤ H*‖x-y‖^α)
    (hRb : ∀ x ∈ S, ∀ i k, |boundaryCutoffRemainder χ u D x i k| ≤ R)
    (hRH : ∀ x ∈ S, ∀ y ∈ S, ∀ i k, |boundaryCutoffRemainder χ u D x i k-boundaryCutoffRemainder χ u D y i k| ≤ HR*‖x-y‖^α) :
    (∀ x ∈ S, |boundaryLocalizedForcing A χ u D f x| ≤ C₀*F+(n:ℝ)^2*M*R) ∧
    (∀ x ∈ S, ∀ y ∈ S, |boundaryLocalizedForcing A χ u D f x-boundaryLocalizedForcing A χ u D f y| ≤
      (C₀*H+F*L₀+(n:ℝ)^2*(M*HR+K*R))*‖x-y‖^α) := by
  constructor
  · intro x hx
    apply (abs_add_le _ _).trans
    have hp : |χ x*f x| ≤ C₀*F := by
      rw [abs_mul]
      exact mul_le_mul (hχb x hx) (hfb x hx) (abs_nonneg _) hC₀
    exact add_le_add hp ((abs_matrixContraction_le hM hR (hAb x hx) (hRb x hx)).trans_eq
      (by simp only [Fintype.card_fin]))
  · intro x hx y hy
    have hp := Real.rpow_nonneg (norm_nonneg (x-y)) α
    have hcon := abs_matrixContraction_sub_le hM hR (mul_nonneg hK hp) (mul_nonneg hHR hp)
      (hAb x hx) (hRb y hy) (hAH x hx y hy) (hRH x hx y hy)
    have hrh : |matrixContraction (A x) (boundaryCutoffRemainder χ u D x)-
        matrixContraction (A y) (boundaryCutoffRemainder χ u D y)| ≤
        ((n:ℝ)^2*(M*HR+K*R))*‖x-y‖^α :=
      hcon.trans_eq (by simp only [Fintype.card_fin]; ring)
    have hprod := holder_product_bound hC₀ hF hL₀ hH hχb hfb hχH hfH x hx y hy
    have he : boundaryLocalizedForcing A χ u D f x-boundaryLocalizedForcing A χ u D f y=
        (χ x*f x-χ y*f y)+(matrixContraction (A x) (boundaryCutoffRemainder χ u D x)-
          matrixContraction (A y) (boundaryCutoffRemainder χ u D y)) := by
      dsimp [boundaryLocalizedForcing]
      ring
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add hprod hrh).trans_eq (by ring))

end GaussianTilt.MomentMapSchauder
