import GaussianTilt.LetwinTraceEnergy
import GaussianTilt.WhiteningMatrices

/-! # The finite-dimensional tensor comparison in a positive definite metric -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GaussianTilt.Letwin
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma metric_trace_symm (M N U V : Matrix ι ι ℝ)
    (hM : M.IsSymm) (hN : N.IsSymm) (hU : U.IsSymm) (hV : V.IsSymm) :
    Matrix.trace (M * U * N * V) = Matrix.trace (M * V * N * U) := by
  calc
    _ = Matrix.trace (M * U * N * V).transpose := (Matrix.trace_transpose _).symm
    _ = Matrix.trace (V * (N * (U * M))) := by
      simp only [Matrix.transpose_mul, hM.eq, hN.eq, hU.eq, hV.eq]
    _ = Matrix.trace (M * V * N * U) := by
      rw [show V * (N * (U * M)) = (V * N * U) * M by noncomm_ring,
        Matrix.trace_mul_comm]
      congr 1
      noncomm_ring

private lemma metric_commutator_trace (R S B U V : Matrix ι ι ℝ)
    (hR : R.IsSymm) (hS : S.IsSymm) (hB : B.IsSymm)
    (hU : U.IsSymm) (hV : V.IsSymm) (hRS : R * S = 1) (hSR : S * R = 1) :
    Matrix.trace ((R * B * U * S - S * U * B * R) *
      (R * B * V * S - S * V * B * R).transpose) =
      2 * (Matrix.trace ((B * (R * R) * B) * U * (S * S) * V) -
        Matrix.trace (B * U * B * V)) := by
  have hM : (B * (R * R) * B).IsSymm := by
    change (B * (R * R) * B).transpose = _
    simp only [Matrix.transpose_mul, hB.eq, hR.eq]
    noncomm_ring
  have hN : (S * S).IsSymm := by
    change (S * S).transpose = _
    simp only [Matrix.transpose_mul, hS.eq]
  have h₁ : Matrix.trace (R * B * U * S * (S * V * B * R)) =
      Matrix.trace ((B * (R * R) * B) * U * (S * S) * V) := by
    calc
      _ = Matrix.trace ((R * B * U * (S * S) * V) * (B * R)) := by congr 1; noncomm_ring
      _ = Matrix.trace ((B * R) * (R * B * U * (S * S) * V)) := Matrix.trace_mul_comm _ _
      _ = _ := by congr 1; noncomm_ring
  have h₂ : Matrix.trace (R * B * U * S * (R * B * V * S)) =
      Matrix.trace (B * U * B * V) := by
    calc
      _ = Matrix.trace ((R * B * U * (S * R) * B * V) * S) := by congr 1; noncomm_ring
      _ = Matrix.trace (S * (R * B * U * (S * R) * B * V)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((S * R) * B * U * (S * R) * B * V) := by congr 1; noncomm_ring
      _ = _ := by rw [hSR]; simp
  have h₃ : Matrix.trace (S * U * B * R * (S * V * B * R)) =
      Matrix.trace (B * U * B * V) := by
    calc
      _ = Matrix.trace ((S * U * B * (R * S) * V) * (B * R)) := by congr 1; noncomm_ring
      _ = Matrix.trace ((B * R) * (S * U * B * (R * S) * V)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (B * (R * S) * U * B * (R * S) * V) := by congr 1; noncomm_ring
      _ = _ := by rw [hRS]; simp
  have h₄ : Matrix.trace (S * U * B * R * (R * B * V * S)) =
      Matrix.trace ((B * (R * R) * B) * U * (S * S) * V) := by
    calc
      _ = Matrix.trace ((S * U) * (B * (R * R) * B * V * S)) := by congr 1; noncomm_ring
      _ = Matrix.trace ((B * (R * R) * B * V * S) * (S * U)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((B * (R * R) * B) * V * (S * S) * U) := by congr 1; noncomm_ring
      _ = _ := metric_trace_symm _ _ _ _ hM hN hV hU
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, hR.eq, hS.eq, hB.eq, hV.eq]
  simp only [← Matrix.mul_assoc]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
  simp only [← Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc] at h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  ring

/-- The weighted trace comparison is an exact positive Gram contraction of
metric commutators. No sign assumption on the symmetric matrix `B` is needed. -/
theorem weighted_metric_trace_comparison (H B : Matrix ι ι ℝ)
    (hH : H.PosDef) (hB : B.IsSymm) (T : ι → Matrix ι ι ℝ)
    (hT : ∀ a, (T a).IsSymm) :
    (∑ a, ∑ b, H⁻¹ a b * Matrix.trace (B * T a * B * T b)) ≤
      ∑ a, ∑ b, H⁻¹ a b * Matrix.trace ((B * H * B) * T a * H⁻¹ * T b) := by
  let R := Whitening.root H
  let S := Whitening.inverseRoot H
  have hR : R.IsSymm := Whitening.root_symm H
  have hS : S.IsSymm := Whitening.inverseRoot_symm hH
  have hRR : R * R = H := Whitening.root_mul_root hH.posSemidef
  have hSS : S * S = H⁻¹ := by
    rw [← hRR, Matrix.mul_inv_rev]
    rfl
  have hRS : R * S = 1 := Whitening.root_mul_inverseRoot hH
  have hSR : S * R = 1 := Whitening.inverseRoot_mul_root hH
  let F := fun a => R * B * T a * S - S * T a * B * R
  have hG := matrix_hs_gram_posSemidef F
  have ht := trace_mul_nonneg_of_posSemidef H⁻¹ _ hH.inv.posSemidef hG
  change 0 ≤ ∑ a, ∑ b, H⁻¹ a b * (∑ i, ∑ j, F b i j * F a i j) at ht
  have hpair (a b : ι) : (∑ i, ∑ j, F b i j * F a i j) =
      Matrix.trace (F a * (F b).transpose) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hpair] at ht
  simp only [F, metric_commutator_trace R S B _ _ hR hS hB (hT _) (hT _) hRS hSR,
    hRR, hSS] at ht
  simp_rw [mul_sub, Finset.sum_sub_distrib] at ht
  have hscale (q : ι → ι → ℝ) :
      (∑ a, ∑ b, H⁻¹ a b * (2 * q a b)) = 2 * ∑ a, ∑ b, H⁻¹ a b * q a b := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hscale, hscale] at ht
  linarith

private def tensorContraction (X Y Z : Matrix ι ι ℝ) (T : ι → Matrix ι ι ℝ) : ℝ :=
  ∑ p : ι × ι, ∑ q : ι × ι, ∑ r : ι × ι,
    X p.1 p.2 * Y q.1 q.2 * Z r.1 r.2 * T p.1 q.1 r.1 * T p.2 q.2 r.2

private lemma trace_eq_tensorContraction (X Y Z : Matrix ι ι ℝ)
    (T : ι → Matrix ι ι ℝ) (hY : Y.IsSymm) (hT : ∀ a, (T a).IsSymm) :
    (∑ a, ∑ b, X a b * Matrix.trace (Y * T a * Z * T b)) =
      tensorContraction X Y Z T := by
  simp only [tensorContraction, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Matrix.mul_assoc, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hY.apply i j, (hT b).apply j l]
  ring

private lemma tensorContraction_swap (X Y Z : Matrix ι ι ℝ)
    (T : ι → Matrix ι ι ℝ) (hSwap : ∀ a i j, T a i j = T i a j) :
    tensorContraction X Y Z T = tensorContraction Y X Z T := by
  unfold tensorContraction
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  rw [hSwap q.1 p.1 r.1, hSwap q.2 p.2 r.2]
  ring

/-- Full third-tensor symmetry permits interchanging the two contracted
matrix slots. The third matrix need not be positive or symmetric. -/
theorem symmetric_tensor_trace_swap (X Y Z : Matrix ι ι ℝ)
    (hX : X.IsSymm) (hY : Y.IsSymm) (T : ι → Matrix ι ι ℝ)
    (hT : ∀ a, (T a).IsSymm) (hSwap : ∀ a i j, T a i j = T i a j) :
    (∑ a, ∑ b, X a b * Matrix.trace (Y * T a * Z * T b)) =
      ∑ a, ∑ b, Y a b * Matrix.trace (X * T a * Z * T b) := by
  rw [trace_eq_tensorContraction X Y Z T hY hT,
    trace_eq_tensorContraction Y X Z T hX hT, tensorContraction_swap X Y Z T hSwap]

/-- Letwin's third-derivative tensor comparison in an arbitrary positive
 definite metric, proved by weighted commutator squares and tensor symmetry. -/
theorem tensor_metric_comparison (H B : Matrix ι ι ℝ)
    (hH : H.PosDef) (hB : B.IsSymm) (T : ι → Matrix ι ι ℝ)
    (hT : ∀ a, (T a).IsSymm) (hSwap : ∀ a i j, T a i j = T i a j) :
    (∑ a, ∑ b, H⁻¹ a b * Matrix.trace (B * T a * B * T b)) ≤
      ∑ i, ∑ j, (B * H * B) i j * Matrix.trace (H⁻¹ * T i * H⁻¹ * T j) := by
  have hHs : H.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hH.isHermitian
  have hAs : H⁻¹.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hH.inv.isHermitian
  have hM : (B * H * B).IsSymm := by
    change (B * H * B).transpose = _
    simp only [Matrix.transpose_mul, hB.eq, hHs.eq]
    noncomm_ring
  have h := weighted_metric_trace_comparison H B hH hB T hT
  rwa [symmetric_tensor_trace_swap H⁻¹ (B * H * B) H⁻¹ hAs hM T hT hSwap] at h

/-- Coordinate differentiation commutes with a constant matrix sandwich. -/
lemma coordinateDerivative_conjugate {n : ℕ} (R : Matrix ι ι ℝ)
    {H : CoordinateSpace n → Matrix ι ι ℝ}
    (hH : ∀ a b, Differentiable ℝ (fun y => H y a b))
    (k : Fin n) (i j : ι) (x : CoordinateSpace n) :
    coordinateDerivative k (fun y => (R * H y * R) i j) x =
      (R * matrixCoordinateDerivative H k x * R) i j := by
  simp_rw [matrix_conjugate_entry]
  rw [coordinateDerivative_sum
    (fun a y => ∑ b, (R i a * R b j) * H y a b)
    (fun a => Differentiable.fun_sum (fun b _ => (hH a b).const_mul _))]
  apply Finset.sum_congr rfl
  intro a _
  rw [coordinateDerivative_sum
    (fun b y => (R i a * R b j) * H y a b)
    (fun b => (hH a b).const_mul _)]
  simp only [coordinateDerivative_const_mul (hH _ _), matrixCoordinateDerivative]

/-- The actual carré-du-champ energy is the contracted tensor trace on the
left side of the finite-dimensional comparison. -/
lemma hessianSandwichEnergy_eq_tensor_trace {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm)
    (x : CoordinateSpace n) :
    hessianSandwichEnergy R φ x =
      ∑ a, ∑ b, inverseHessian φ x a b *
        Matrix.trace ((R * R) * matrixCoordinateDerivative (coordinateHessian φ) a x *
          (R * R) * matrixCoordinateDerivative (coordinateHessian φ) b x) := by
  have hH (a b : Fin n) : Differentiable ℝ (fun y => coordinateHessian φ y a b) :=
    (contDiff_coordinateHessian hφ a b).differentiable le_rfl
  have hT (a : Fin n) : (matrixCoordinateDerivative (coordinateHessian φ) a x).IsSymm :=
    matrixCoordinateDerivative_hessian_isSymm (hφ.of_le (by norm_num)) a x
  simp only [hessianSandwichEnergy, diffusionGamma, diffusionFlux,
    coordinateDerivative_conjugate R hH, Finset.sum_mul]
  have hperm (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
      (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
    simpa only [Fintype.sum_prod_type] using
      (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun p : Fin n × Fin n => fun q : Fin n × Fin n => f p.1 p.2 q.1 q.2))
  rw [hperm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [← conjugate_hs_inner_eq_trace R
    (matrixCoordinateDerivative (coordinateHessian φ) a x)
    (matrixCoordinateDerivative (coordinateHessian φ) b x) hR (hT a)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Equation (2.12) for the actual Hessian and its actual third derivatives,
with no tensor, energy, or variance bound assumed. -/
theorem hessianSandwichEnergy_le_thirdTerm {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm)
    (x : CoordinateSpace n) (hH : (coordinateHessian φ x).PosDef) :
    hessianSandwichEnergy R φ x ≤ hessianSandwichThirdTerm R φ x := by
  have hB : (R * R).IsSymm := by
    change (R * R).transpose = _
    simp only [Matrix.transpose_mul, hR.eq]
  have hT (a : Fin n) : (matrixCoordinateDerivative (coordinateHessian φ) a x).IsSymm :=
    matrixCoordinateDerivative_hessian_isSymm (hφ.of_le (by norm_num)) a x
  have hSwap (a i j : Fin n) :
      matrixCoordinateDerivative (coordinateHessian φ) a x i j =
        matrixCoordinateDerivative (coordinateHessian φ) i x a j := by
    change coordinateThirdDerivative φ x i j a = coordinateThirdDerivative φ x a j i
    rw [coordinateThirdDerivative_cycle hφ x i j a,
      coordinateThirdDerivative_symm (hφ.of_le (by norm_num)) x j a i]
  rw [hessianSandwichEnergy_eq_tensor_trace hφ R hR x]
  have h := tensor_metric_comparison (coordinateHessian φ x) (R * R) hH hB
    (fun a => matrixCoordinateDerivative (coordinateHessian φ) a x) hT hSwap
  change _ ≤ ∑ i, ∑ j, ((R * R) * coordinateHessian φ x * (R * R)) i j *
    Matrix.trace (inverseHessian φ x * matrixCoordinateDerivative (coordinateHessian φ) i x *
      inverseHessian φ x * matrixCoordinateDerivative (coordinateHessian φ) j x)
  exact h

end GaussianTilt.Letwin
