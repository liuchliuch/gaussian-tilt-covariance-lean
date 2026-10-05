import GaussianTilt.MomentMapSchauderBoundaryEstimate
import GaussianTilt.MomentMapHolderExtension
import GaussianTilt.MomentMapSchauderEuclideanFreezing

/-! # Literal frozen-boundary right-hand side and its constructed extension -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 1600000
open Set Matrix
open scoped ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

def bilinearEntryMatrix (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)

lemma matrixContraction_one_bilinear (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) :
    matrixContraction (1 : Matrix (Fin n) (Fin n) ℝ) (bilinearEntryMatrix B)=kernelHessianTrace B := by
  classical
  simp only [matrixContraction,Matrix.one_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  rfl

/-- Freezing at the identity is an exact algebraic identity for the true
closure Hessian field, including boundary points. -/
lemma boundary_frozen_trace_identity (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (f : KernelSpace n → ℝ) (B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ)
    {x : KernelSpace n} (heq : matrixContraction (A x) (bilinearEntryMatrix (B x))=f x) :
    kernelHessianTrace (B x)=f x+matrixContraction (1-A x) (bilinearEntryMatrix (B x)) := by
  rw [matrixContraction_sub_left,matrixContraction_one_bilinear,heq]
  ring

/-- The frozen trace has a genuinely constructed global Hölder forcing
extension. Both its supremum and its Hölder modulus display the exact
small coefficients multiplying the initial Hessian size. -/
theorem exists_boundary_frozen_forcing_extension
    {S : Set (KernelSpace n)} (hS : S.Nonempty) {α ε K Q F H : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hF : 0 ≤ F) (hH : 0 ≤ H)
    (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ) (f : KernelSpace n → ℝ)
    (B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ)
    (hA : ∀ x ∈ S, ∀ i j, |(1 : Matrix (Fin n) (Fin n) ℝ) i j-A x i j| ≤ ε)
    (hAH : ∀ x ∈ S, ∀ y ∈ S, ∀ i j, |A x i j-A y i j| ≤ K*‖x-y‖^α)
    (hB : ∀ x ∈ S, ‖B x‖ ≤ Q)
    (hBH : ∀ x ∈ S, ∀ y ∈ S, ‖B x-B y‖ ≤ Q*‖x-y‖^α)
    (hf : ∀ x ∈ S, |f x| ≤ F) (hfH : ∀ x ∈ S, ∀ y ∈ S, |f x-f y| ≤ H*‖x-y‖^α)
    (heq : ∀ x ∈ S, matrixContraction (A x) (bilinearEntryMatrix (B x))=f x) :
    ∃ g : KernelSpace n → ℝ, Continuous g ∧
      (∀ x ∈ S, g x= -kernelHessianTrace (B x)) ∧
      (∀ x, |g x| ≤ F+(n:ℝ)^2*ε*Q) ∧
      (∀ x y, |g x-g y| ≤ (H+(n:ℝ)^2*(ε+K)*Q)*‖x-y‖^α) := by
  let R := fun x => matrixContraction (1-A x) (bilinearEntryMatrix (B x))
  have hRb : ∀ x ∈ S, |R x| ≤ (n:ℝ)^2*ε*Q := by
    intro x hx
    exact (abs_matrixContraction_le hε hQ (hA x hx)
      (fun i j => (abs_euclidean_bilinear_entry_le_norm (B x) i j).trans (hB x hx))).trans_eq
      (by simp only [Fintype.card_fin])
  have hRH : ∀ x ∈ S, ∀ y ∈ S, |R x-R y| ≤ (n:ℝ)^2*(ε+K)*Q*‖x-y‖^α := by
    intro x hx y hy
    have hp := Real.rpow_nonneg (norm_nonneg (x-y)) α
    have hh := abs_matrixContraction_sub_le hε hQ (mul_nonneg hK hp) (mul_nonneg hQ hp)
      (A := 1-A x) (C := 1-A y) (B := bilinearEntryMatrix (B x)) (D := bilinearEntryMatrix (B y))
      (hA x hx) (fun i j => (abs_euclidean_bilinear_entry_le_norm (B y) i j).trans (hB y hy))
      (fun i j => by
        simp only [Matrix.sub_apply]
        have he : ((1:Matrix (Fin n) (Fin n) ℝ) i j-A x i j)-((1:Matrix (Fin n) (Fin n) ℝ) i j-A y i j)=
            -(A x i j-A y i j) := by ring
        rw [he,abs_neg]
        exact hAH x hx y hy i j)
      (fun i j => (abs_euclidean_bilinear_entry_le_norm (B x-B y) i j).trans (hBH x hx y hy))
    exact hh.trans_eq (by simp only [Fintype.card_fin]; ring)
  let g₀ : S → ℝ := fun x => -(f x+R x)
  have hg₀ : ∀ x : S, |g₀ x| ≤ F+(n:ℝ)^2*ε*Q := by
    intro x
    exact (abs_neg (f x+R x)).le.trans ((abs_add_le _ _).trans (add_le_add (hf x x.2) (hRb x x.2)))
  have hg₀H : ∀ x y : S, |g₀ x-g₀ y| ≤ (H+(n:ℝ)^2*(ε+K)*Q)*dist x y^α := by
    intro x y
    have he : g₀ x-g₀ y= -((f x-f y)+(R x-R y)) := by dsimp [g₀]; ring
    rw [he,abs_neg]
    exact (abs_add_le _ _).trans ((add_le_add (hfH x x.2 y y.2) (hRH x x.2 y y.2)).trans_eq
      (by simp only [Subtype.dist_eq,dist_eq_norm]; ring))
  obtain ⟨g,hgc,hge,hgb,hgH⟩ := HolderSpace.exists_bounded_holder_extension hS hα hα1
    (by positivity : 0 ≤ F+(n:ℝ)^2*ε*Q) (by positivity : 0 ≤ H+(n:ℝ)^2*(ε+K)*Q) g₀ hg₀ hg₀H
  refine ⟨g,hgc,?_,hgb,?_⟩
  · intro x hx
    rw [hge ⟨x,hx⟩,boundary_frozen_trace_identity A f B (heq x hx)]
  · simpa only [dist_eq_norm] using hgH

end GaussianTilt.MomentMapSchauder
