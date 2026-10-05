import GaussianTilt.MomentMapSchauderMatrixCalculus
import GaussianTilt.MomentMapSchauderLinearCoefficientBounds
import GaussianTilt.MomentMapSchauderHolderAlgebra

/-! # Actual C¹,α inverse coefficient regularity for source bootstrap -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1400000
open Matrix Set
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Inverse first-derivative Hölder bounds follow from the actual inverse
identity. Uniform inverse bounds are derived by compactness, rather than
assumed as an extra source ellipticity hypothesis. -/
theorem exists_matrix_inverse_derivative_holder
    {H : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hH : ∀ i j, ContDiff ℝ 1 (fun x => H x i j)) (hpos : ∀ x, (H x).PosDef)
    {S : Set (KernelSpace n)} (hS : IsCompact S) (hSc : Convex ℝ S)
    {Q α : ℝ} (hQ : 0 ≤ Q) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hDH : ∀ x ∈ S, ∀ y ∈ S, ∀ i j,
      ‖fderiv ℝ (fun z => H z i j) x-fderiv ℝ (fun z => H z i j) y‖ ≤ Q*‖x-y‖^α) :
    (∀ i j, ContDiff ℝ 1 (fun x => (H x)⁻¹ i j)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ i j,
        ‖fderiv ℝ (fun z => (H z)⁻¹ i j) x-fderiv ℝ (fun z => (H z)⁻¹ i j) y‖ ≤ C*‖x-y‖^α := by
  have hdet : ∀ x, (H x).det ≠ 0 := fun x => (hpos x).det_pos.ne'
  refine ⟨contDiff_matrix_inv_field hH hdet, ?_⟩
  obtain ⟨M₀, D, K₀, _, hD, hK₀, _, hDb, hHH⟩ :=
    exists_C1_matrix_bounds_on_compact_convex hH hS hSc hα hα1
  obtain ⟨M, hM, hMb⟩ := exists_bound_inv_segments_on_compact hS
    (continuous_matrix_of_contDiff_entries hH).continuousOn (fun x _ => hpos x)
  have hIb : ∀ x ∈ S, ∀ i j, |(H x)⁻¹ i j| ≤ M := by
    intro x hx i j
    simpa only [matrixSegment, sub_zero, one_smul, zero_smul, add_zero] using
      hMb x hx x hx 0 ⟨le_rfl, zero_le_one⟩ i j
  let K := (n : ℝ)^2*M^2*K₀
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hIH : ∀ x ∈ S, ∀ y ∈ S, ∀ i j, |(H x)⁻¹ i j-(H y)⁻¹ i j| ≤ K*‖x-y‖^α := by
    intro x hx y hy i j
    have hp := Real.rpow_nonneg (norm_nonneg (x-y)) α
    have hh := abs_inv_entry_sub_le (hpos x) (hpos y) hM.le (mul_nonneg hK₀.le hp)
      (hIb x hx) (hIb y hy) (hHH x hx y hy) i j
    exact hh.trans_eq (by simp only [Fintype.card_fin]; dsimp [K]; ring)
  let B := M^2*Q+(2*M*K)*D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hprod (i a b j : Fin n) :
      ∀ x ∈ S, ∀ y ∈ S,
      |((H x)⁻¹ i a*(H x)⁻¹ b j)-((H y)⁻¹ i a*(H y)⁻¹ b j)| ≤ (2*M*K)*‖x-y‖^α := by
    intro x hx y hy
    have hh := holder_product_bound hM.le hM.le hK hK
      (fun z hz => hIb z hz i a) (fun z hz => hIb z hz b j)
      (fun z hz w hw => hIH z hz w hw i a) (fun z hz w hw => hIH z hz w hw b j) x hx y hy
    exact hh.trans_eq (by ring)
  have hterm (i a b j : Fin n) : ∀ x ∈ S, ∀ y ∈ S,
      ‖((H x)⁻¹ i a*(H x)⁻¹ b j) • fderiv ℝ (fun z => H z a b) x-
        ((H y)⁻¹ i a*(H y)⁻¹ b j) • fderiv ℝ (fun z => H z a b) y‖ ≤ B*‖x-y‖^α := by
    apply holder_smul_bound_norm (by positivity) hD.le (by positivity) hQ
    · intro x hx
      rw [abs_mul, pow_two]
      exact mul_le_mul (hIb x hx i a) (hIb x hx b j) (abs_nonneg _) hM.le
    · intro x hx
      exact hDb x hx a b
    · exact hprod i a b j
    · intro x hx y hy
      exact hDH x hx y hy a b
  refine ⟨(n : ℝ)^2*B+1, by positivity, ?_⟩
  intro x hx y hy i j
  rw [fderiv_matrix_inv_field hH hdet, fderiv_matrix_inv_field hH hdet]
  have hh := holder_finset_sum_norm Finset.univ
    (fun a _ => holder_finset_sum_norm Finset.univ (fun b _ => hterm i a b j)) x hx y hy
  have hn : ‖(∑ a, ∑ b, ((H x)⁻¹ i a*(H x)⁻¹ b j) • fderiv ℝ (fun z => H z a b) x)-
      ∑ a, ∑ b, ((H y)⁻¹ i a*(H y)⁻¹ b j) • fderiv ℝ (fun z => H z a b) y‖ ≤
      ((n : ℝ)^2*B)*‖x-y‖^α := by
    exact hh.trans_eq (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring)
  simpa only [neg_sub_neg, norm_sub_rev] using hn.trans (mul_le_mul_of_nonneg_right
    (show (n : ℝ)^2*B ≤ (n : ℝ)^2*B+1 by linarith) (Real.rpow_nonneg (norm_nonneg (x-y)) α))

lemma contDiff_euclideanHessian_entry {φ : KernelSpace n → ℝ} {k : WithTop ℕ∞}
    (hφ : ContDiff ℝ (k+2) φ) (i j : Fin n) :
    ContDiff ℝ k (fun x => euclideanHessianMatrix φ x i j) := by
  have hh : ContDiff ℝ k (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := k+1) (le_of_eq (by rw [add_assoc]; rfl))).fderiv_right le_rfl
  exact (hh.clm_apply contDiff_const).clm_apply contDiff_const

lemma fderiv_euclideanHessian_entry_apply {φ : KernelSpace n → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x v : KernelSpace n) (i j : Fin n) :
    fderiv ℝ (fun y => euclideanHessianMatrix φ y i j) x v=
      fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x v (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  have hh := ((hφ.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
    (by norm_num)).differentiable le_rfl x
  unfold euclideanHessianMatrix
  rw [fderiv_clm_apply_const_apply (hh.clm_apply (differentiableAt_const _)),
    fderiv_clm_apply_const_apply hh]

lemma norm_fderiv_euclideanHessian_entry_sub_le {φ : KernelSpace n → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x y : KernelSpace n) (i j : Fin n) :
    ‖fderiv ℝ (fun z => euclideanHessianMatrix φ z i j) x-
      fderiv ℝ (fun z => euclideanHessianMatrix φ z i j) y‖ ≤
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  simp only [ContinuousLinearMap.sub_apply, fderiv_euclideanHessian_entry_apply hφ, Real.norm_eq_abs]
  have hh := abs_euclidean_bilinear_entry_le_norm
    ((fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y) v) i j
  exact hh.trans ((fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y).le_opNorm v)

/-- The genuine linearized source coefficients are C¹,α after the first
C³,α gain, with no separately assumed inverse regularity or ellipticity. -/
theorem exists_source_inverse_derivative_holder {φ : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    {S : Set (KernelSpace n)} (hS : IsCompact S) (hSc : Convex ℝ S)
    {Q α : ℝ} (hQ : 0 ≤ Q) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hD3 : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y‖ ≤ Q*‖x-y‖^α) :
    (∀ i j, ContDiff ℝ 1 (fun x => (euclideanHessianMatrix φ x)⁻¹ i j)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ i j,
        ‖fderiv ℝ (fun z => (euclideanHessianMatrix φ z)⁻¹ i j) x-
          fderiv ℝ (fun z => (euclideanHessianMatrix φ z)⁻¹ i j) y‖ ≤ C*‖x-y‖^α := by
  apply exists_matrix_inverse_derivative_holder (fun i j => contDiff_euclideanHessian_entry (k := 1) hφ i j)
    hpos hS hSc hQ hα hα1
  intro x hx y hy i j
  exact (norm_fderiv_euclideanHessian_entry_sub_le hφ x y i j).trans (hD3 x hx y hy)

end GaussianTilt.MomentMapSchauder
