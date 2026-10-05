import GaussianTilt.MomentMapSchauderBoundaryVariableForcing
import GaussianTilt.MomentMapHolderChartBounds

/-! # Uniform Hölder algebra for the actual flattened principal and drift fields -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 1800000
open Set Matrix
open scoped ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Fixed smooth matrix fields have genuine uniform entrywise Hölder
bounds on the compact chart domain. -/
theorem exists_smooth_matrix_entry_holder_bound {T : Set (KernelSpace n)} (hT : IsCompact T) (hTc : Convex ℝ T)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (L : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hL : ∀ i k, ContDiff ℝ 1 (fun x => L x i k)) :
    ∃ C : ℝ, 1 ≤ C ∧ (∀ x ∈ T, ∀ i k, |L x i k| ≤ C) ∧
      (∀ x ∈ T, ∀ y ∈ T, ∀ i k, |L x i k-L y i k| ≤ C*‖x-y‖^α) := by
  classical
  choose C hC hb hh using fun i k => exists_contDiff_holder_bound_on_compact_convex (hL i k) hT hTc hα hα1
  let M := 1+∑ i, ∑ k, C i k
  have hnon : 0 ≤ ∑ i, ∑ k, C i k := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => (hC i k).le))
  have hle (i k : Fin n) : C i k ≤ M := by
    have h1 := Finset.single_le_sum (s := Finset.univ) (f := fun l : Fin n => C i l) (fun l _ => (hC i l).le) (Finset.mem_univ k)
    have h2 := Finset.single_le_sum (s := Finset.univ) (f := fun a : Fin n => ∑ l : Fin n, C a l)
      (fun a _ => Finset.sum_nonneg (fun l _ => (hC a l).le)) (Finset.mem_univ i)
    dsimp [M]
    linarith
  refine ⟨M,by dsimp [M]; linarith,?_,?_⟩
  · intro x hx i k
    have ht : |L x i k| ≤ C i k := by simpa only [Real.norm_eq_abs] using hb i k x hx
    exact ht.trans (hle i k)
  · intro x hx y hy i k
    have ht : |L x i k-L y i k| ≤ C i k*‖x-y‖^α := by simpa only [Real.norm_eq_abs] using hh i k x hx y hy
    exact ht.trans (mul_le_mul_of_nonneg_right (hle i k) (Real.rpow_nonneg (norm_nonneg _) α))

/-- Exact finite-product estimates for a variable principal coefficient
under a fixed smooth Jacobian. -/
theorem matrix_sandwich_holder_bounds {T : Set (KernelSpace n)}
    {L A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} {α B M K : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hLb : ∀ x ∈ T, ∀ i k, |L x i k| ≤ B)
    (hLH : ∀ x ∈ T, ∀ y ∈ T, ∀ i k, |L x i k-L y i k| ≤ B*‖x-y‖^α)
    (hAb : ∀ x ∈ T, ∀ i k, |A x i k| ≤ M)
    (hAH : ∀ x ∈ T, ∀ y ∈ T, ∀ i k, |A x i k-A y i k| ≤ K*‖x-y‖^α) :
    (∀ x ∈ T, ∀ i k, |(L x*A x*(L x)ᵀ) i k| ≤ (n:ℝ)^2*B^2*M) ∧
    (∀ x ∈ T, ∀ y ∈ T, ∀ i k,
      |(L x*A x*(L x)ᵀ) i k-(L y*A y*(L y)ᵀ) i k| ≤ (n:ℝ)^2*B^2*(K+2*M)*‖x-y‖^α) := by
  have hterm (i a b k : Fin n) : ∀ x ∈ T, |L x i a*A x a b*L x k b| ≤ B*M*B := by
    intro x hx
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (hLb x hx i a) (hAb x hx a b) (abs_nonneg _) hB) (hLb x hx k b) (abs_nonneg _) (mul_nonneg hB hM)
  have htermH (i a b k : Fin n) : ∀ x ∈ T, ∀ y ∈ T,
      |L x i a*A x a b*L x k b-L y i a*A y a b*L y k b| ≤
        (B*M*B+B*(B*K+M*B))*‖x-y‖^α := by
    apply holder_product_bound (mul_nonneg hB hM) hB (by positivity) hB
      (fun x hx => by rw [abs_mul]; exact mul_le_mul (hLb x hx i a) (hAb x hx a b) (abs_nonneg _) hB)
      (fun x hx => hLb x hx k b)
      (holder_product_bound hB hM hB hK (fun x hx => hLb x hx i a) (fun x hx => hAb x hx a b)
        (fun x hx y hy => hLH x hx y hy i a) (fun x hx y hy => hAH x hx y hy a b))
      (fun x hx y hy => hLH x hx y hy k b)
  constructor
  · intro x hx i k
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
    exact (abs_finset_sum_bound (fun b => abs_finset_sum_bound (fun a => hterm i a b k x hx))).trans_eq
      (by simp only [Fintype.card_fin]; ring)
  · intro x hx y hy i k
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    have hinner (b : Fin n) : |(∑ a, L x i a*A x a b*L x k b)-(∑ a, L y i a*A y a b*L y k b)| ≤
        (n:ℝ)*(B*M*B+B*(B*K+M*B))*‖x-y‖^α := by
      rw [← Finset.sum_sub_distrib]
      exact (abs_finset_sum_bound (fun a => htermH i a b k x hx y hy)).trans_eq (by simp only [Fintype.card_fin]; ring)
    exact (abs_finset_sum_bound hinner).trans_eq (by simp only [Fintype.card_fin]; ring)

/-- The drift contraction with a fixed smooth Hessian has an actual
Hölder bound, with no derivative of the unknown coefficient field. -/
theorem matrixContraction_holder_bounds_on {T : Set (KernelSpace n)}
    {A B : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} {α M K L : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hAb : ∀ x ∈ T, ∀ i k, |A x i k| ≤ M)
    (hAH : ∀ x ∈ T, ∀ y ∈ T, ∀ i k, |A x i k-A y i k| ≤ K*‖x-y‖^α)
    (hBb : ∀ x ∈ T, ∀ i k, |B x i k| ≤ L)
    (hBH : ∀ x ∈ T, ∀ y ∈ T, ∀ i k, |B x i k-B y i k| ≤ L*‖x-y‖^α) :
    (∀ x ∈ T, |matrixContraction (A x) (B x)| ≤ (n:ℝ)^2*M*L) ∧
    (∀ x ∈ T, ∀ y ∈ T, |matrixContraction (A x) (B x)-matrixContraction (A y) (B y)| ≤
      (n:ℝ)^2*(M*L+K*L)*‖x-y‖^α) := by
  constructor
  · intro x hx
    exact (abs_matrixContraction_le hM hL (hAb x hx) (hBb x hx)).trans_eq (by simp only [Fintype.card_fin])
  · intro x hx y hy
    have hp := Real.rpow_nonneg (norm_nonneg (x-y)) α
    exact (abs_matrixContraction_sub_le hM hL (mul_nonneg hK hp) (mul_nonneg hL hp)
      (hAb x hx) (hBb y hy) (hAH x hx y hy) (hBH x hx y hy)).trans_eq
      (by simp only [Fintype.card_fin]; ring)

end GaussianTilt.MomentMapSchauder
