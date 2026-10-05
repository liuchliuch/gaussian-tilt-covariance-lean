import GaussianTilt.MomentMapSchauderIteratedEquation
import GaussianTilt.MomentMapSchauderMatrixCalculus

/-! # Actual higher differentiated equations for the nonlinear moment source -/
noncomputable section
set_option maxHeartbeats 2000000
open Matrix Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma scalarDerivativeJet_directional {k : ℕ} {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ (↑(k + 1) : WithTop ℕ∞) u)
    (d : Fin k → KernelSpace n) (v : KernelSpace n) :
    scalarDerivativeJet k (kernelDirectionalDerivative v u) d =
      scalarDerivativeJet (k + 1) u (Fin.snoc d v) := by
  have hDu : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ u) :=
    hu.fderiv_right (by simp only [Nat.cast_add, Nat.cast_one, le_refl])
  funext x
  simp only [scalarDerivativeJet, iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  exact iteratedFDeriv_clm_apply_const_apply hDu le_rfl

lemma contDiff_euclideanHessianMatrix_entry {m : ℕ} {φ : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ (↑(m + 2) : WithTop ℕ∞) φ) (i j : Fin n) :
    ContDiff ℝ (m : WithTop ℕ∞) (fun x => euclideanHessianMatrix φ x i j) :=
  contDiff_secondFrechet_entry (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hφ) _ _

lemma matrixDirectionalDerivative_euclideanHessian {φ : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (v x : KernelSpace n) :
    matrixDirectionalDerivative (euclideanHessianMatrix φ) v x =
      euclideanHessianMatrix (kernelDirectionalDerivative v φ) x := by
  ext i j
  exact directional_derivative_secondFrechet hφ v x _ _

/-- The first scalar source equation is derived from the actual logarithmic
determinant identity and Jacobi's formula, with true inverse coefficients. -/
theorem source_directional_elliptic_equation {φ g : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (euclideanHessianMatrix φ x).det = g x)
    (v x : KernelSpace n) :
    euclideanEllipticOperator (euclideanHessianMatrix φ x)⁻¹
      (kernelDirectionalDerivative v φ) x = kernelDirectionalDerivative v g x := by
  have hH : ∀ i j, ContDiff ℝ 1 (fun y => euclideanHessianMatrix φ y i j) :=
    contDiff_euclideanHessianMatrix_entry hφ
  have hj := fderiv_matrix_logdet_field_apply hH (fun y => (hpos y).det_pos.ne') v x
  rw [show (fun y => Real.log (euclideanHessianMatrix φ y).det) = g from funext hMA,
    matrixDirectionalDerivative_euclideanHessian hφ] at hj
  have hD : ContDiff ℝ 2 (kernelDirectionalDerivative v φ) := contDiff_kernelDirectionalDerivative hφ v
  have hsym := euclideanHessianMatrix_isSymm hD x
  change euclideanEllipticOperator _ _ x = fderiv ℝ g x v
  rw [hj]
  simp only [euclideanEllipticOperator, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hsym.apply i j]
  rfl

/-- Arbitrary true source jets satisfy the explicitly constructed elliptic
forcing recursion. This is the PDE input needed for the higher Schauder induction. -/
theorem source_iterated_elliptic_equation (k : ℕ) {φ g : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ (↑(k + 3) : WithTop ℕ∞) φ)
    (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (euclideanHessianMatrix φ x).det = g x)
    (d : Fin k → KernelSpace n) (v x : KernelSpace n) :
    euclideanEllipticOperator (euclideanHessianMatrix φ x)⁻¹
      (scalarDerivativeJet (k + 1) φ (Fin.snoc d v)) x =
      iteratedEllipticForcing (fun y => (euclideanHessianMatrix φ y)⁻¹)
        (kernelDirectionalDerivative v φ) (kernelDirectionalDerivative v g) k d x := by
  have hφ3 : ContDiff ℝ 3 φ := hφ.of_le (by exact_mod_cast (show 3 ≤ k + 3 by omega))
  have hA : ∀ i j, ContDiff ℝ 1 (fun y => (euclideanHessianMatrix φ y)⁻¹ i j) :=
    contDiff_matrix_inv_field (contDiff_euclideanHessianMatrix_entry hφ3) (fun y => (hpos y).det_pos.ne')
  have hD : ContDiff ℝ (↑(k + 2) : WithTop ℕ∞) (kernelDirectionalDerivative v φ) :=
    contDiff_kernelDirectionalDerivative (by simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc] using hφ) v
  have hh := iterated_differentiated_elliptic_equation k hD hA
    (source_directional_elliptic_equation hφ3 hpos hMA v) d x
  rw [scalarDerivativeJet_directional (hφ.of_le (by exact_mod_cast (show k + 1 ≤ k + 3 by omega)))] at hh
  exact hh

/-- The repeated source forcing is genuinely C¹ at precisely the derivative
order available to the bootstrap. Inverse coefficient regularity is derived
from the actual positive Hessian; it is not an extra premise. -/
theorem source_iterated_forcing_contDiff_one (k : ℕ) {φ g : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ (↑(k + 3) : WithTop ℕ∞) φ)
    (hg : ContDiff ℝ (↑(k + 2) : WithTop ℕ∞) g)
    (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (d : Fin k → KernelSpace n) (v : KernelSpace n) :
    ContDiff ℝ 1 (iteratedEllipticForcing (fun y => (euclideanHessianMatrix φ y)⁻¹)
      (kernelDirectionalDerivative v φ) (kernelDirectionalDerivative v g) k d) := by
  have hH : ∀ i j, ContDiff ℝ (↑(k + 1) : WithTop ℕ∞) (fun y => euclideanHessianMatrix φ y i j) := by
    apply contDiff_euclideanHessianMatrix_entry
    convert hφ using 1 <;> congr 1 <;> omega
  have hA := contDiff_matrix_inv_field hH (fun y => (hpos y).det_pos.ne')
  have hD : ContDiff ℝ (↑(k + 2) : WithTop ℕ∞) (kernelDirectionalDerivative v φ) :=
    contDiff_kernelDirectionalDerivative (by simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc] using hφ) v
  have hF : ContDiff ℝ (↑(k + 1) : WithTop ℕ∞) (kernelDirectionalDerivative v g) :=
    contDiff_kernelDirectionalDerivative (by norm_num [Nat.cast_add, add_assoc] at hg ⊢; exact hg) v
  exact contDiff_iteratedEllipticForcing k 1 (by convert hD using 1 <;> congr 1 <;> omega) hA hF d

end GaussianTilt.MomentMapSchauder
