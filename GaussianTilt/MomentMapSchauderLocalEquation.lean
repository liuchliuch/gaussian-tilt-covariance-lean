import GaussianTilt.MomentMapSchauderLocalCoefficients

/-! # Literal differentiated equations on an open local domain -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 1800000
open Matrix Set Filter
open scoped ContDiff BigOperators Topology
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma fderiv_matrix_logdet_field_apply_at {H : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hH : ∀ i j, ContDiff ℝ 1 (fun x => H x i j)) (v x : KernelSpace n) (hdet : (H x).det ≠ 0) :
    fderiv ℝ (fun y => Real.log (H y).det) x v=Matrix.trace ((H x)⁻¹*matrixDirectionalDerivative H v x) := by
  have hd := ((contDiff_matrix_det_field hH).differentiable le_rfl x).hasFDerivAt.log hdet
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_matrix_det_field_apply (fun a b => (hH a b).differentiable le_rfl),
    Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.trace_smul]
  rfl

theorem differentiated_elliptic_equation_on {u f : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 3 u) {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) {U : Set (KernelSpace n)} (hU : IsOpen U)
    (heq : ∀ x ∈ U, euclideanEllipticOperator (A x) u x=f x)
    (v : KernelSpace n) {x : KernelSpace n} (hx : x ∈ U) :
    euclideanEllipticOperator (A x) (kernelDirectionalDerivative v u) x=
      kernelDirectionalDerivative v f x-ellipticDerivativeError A u v x := by
  have he : (fun y => euclideanEllipticOperator (A y) u y) =ᶠ[𝓝 x] f := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact heq y hy
  have hh := directional_ellipticOperator_product_rule hu hA v x
  rw [he.fderiv_eq] at hh
  change fderiv ℝ f x v= _ at hh
  dsimp only [kernelDirectionalDerivative]
  linarith

theorem iterated_differentiated_elliptic_equation_on (k : ℕ)
    {u f : KernelSpace n → ℝ} (hu : ContDiff ℝ (↑(k+2) : WithTop ℕ∞) u)
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) {U : Set (KernelSpace n)} (hU : IsOpen U)
    (heq : ∀ x ∈ U, euclideanEllipticOperator (A x) u x=f x)
    (v : Fin k → KernelSpace n) {x : KernelSpace n} (hx : x ∈ U) :
    euclideanEllipticOperator (A x) (scalarDerivativeJet k u v) x=iteratedEllipticForcing A u f k v x := by
  induction k generalizing x with
  | zero => simpa only [scalarDerivativeJet_zero, iteratedEllipticForcing] using heq x hx
  | succ k ih =>
    have hu' : ContDiff ℝ (↑(k+2) : WithTop ℕ∞) u :=
      hu.of_le (by exact_mod_cast (show k+2 ≤ k+1+2 by omega))
    have hjet : ContDiff ℝ 3 (scalarDerivativeJet k u (Fin.tail v)) :=
      contDiff_scalarDerivativeJet k 3 (by convert hu using 1 <;> congr 1 <;> omega) (Fin.tail v)
    have hp : ∀ y ∈ U, euclideanEllipticOperator (A y) (scalarDerivativeJet k u (Fin.tail v)) y=
        iteratedEllipticForcing A u f k (Fin.tail v) y := fun y hy => ih hu' (Fin.tail v) hy
    have hstep := differentiated_elliptic_equation_on hjet hA hU hp (v 0) hx
    rw [scalarDerivativeJet_succ (hu.of_le (by exact_mod_cast (show k+1 ≤ k+1+2 by omega)))]
    exact hstep

/-- Constant-logdet source gradients satisfy the true local homogeneous
linear equation. Positivity and the nonlinear PDE are used only on U. -/
theorem local_logdet_directional_equation {φ : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) {U : Set (KernelSpace n)} (hU : IsOpen U) {c : ℝ}
    (hpos : ∀ x ∈ U, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x ∈ U, Real.log (euclideanHessianMatrix φ x).det=c)
    (v : KernelSpace n) {x : KernelSpace n} (hx : x ∈ U) :
    euclideanEllipticOperator (euclideanHessianMatrix φ x)⁻¹ (kernelDirectionalDerivative v φ) x=0 := by
  have hH : ∀ i j, ContDiff ℝ 1 (fun y => euclideanHessianMatrix φ y i j) :=
    contDiff_euclideanHessianMatrix_entry hφ
  have he : (fun y => Real.log (euclideanHessianMatrix φ y).det) =ᶠ[𝓝 x] (fun _ => c) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hMA y hy
  have hz : fderiv ℝ (fun y => Real.log (euclideanHessianMatrix φ y).det) x=0 := by
    rw [he.fderiv_eq]
    simp
  have hj := fderiv_matrix_logdet_field_apply_at hH v x (hpos x hx).det_pos.ne'
  rw [hz, ContinuousLinearMap.zero_apply, matrixDirectionalDerivative_euclideanHessian hφ] at hj
  have hD : ContDiff ℝ 2 (kernelDirectionalDerivative v φ) := contDiff_kernelDirectionalDerivative hφ v
  have hsym := euclideanHessianMatrix_isSymm hD x
  rw [hj]
  simp only [euclideanEllipticOperator, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hsym.apply i j]
  rfl

/-- Any smooth coefficient extension agreeing with the inverse Hessian on
U gives the actual repeated local PDE, with explicitly constructed forcing. -/
theorem local_logdet_iterated_equation (k : ℕ) {φ : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ (↑(k+3) : WithTop ℕ∞) φ)
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    {U : Set (KernelSpace n)} (hU : IsOpen U) {c : ℝ}
    (hpos : ∀ x ∈ U, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x ∈ U, Real.log (euclideanHessianMatrix φ x).det=c)
    (hAe : ∀ x ∈ U, A x=(euclideanHessianMatrix φ x)⁻¹)
    (d : Fin k → KernelSpace n) (v : KernelSpace n) {x : KernelSpace n} (hx : x ∈ U) :
    euclideanEllipticOperator (A x) (scalarDerivativeJet (k+1) φ (Fin.snoc d v)) x=
      iteratedEllipticForcing A (kernelDirectionalDerivative v φ) (fun _ => 0) k d x := by
  have hφ3 : ContDiff ℝ 3 φ := hφ.of_le (by exact_mod_cast (show 3 ≤ k+3 by omega))
  have hD : ContDiff ℝ (↑(k+2) : WithTop ℕ∞) (kernelDirectionalDerivative v φ) :=
    contDiff_kernelDirectionalDerivative (by simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc] using hφ) v
  have hbase : ∀ y ∈ U, euclideanEllipticOperator (A y) (kernelDirectionalDerivative v φ) y=0 := by
    intro y hy
    rw [hAe y hy]
    exact local_logdet_directional_equation hφ3 hU hpos hMA v hy
  have hh := iterated_differentiated_elliptic_equation_on k hD hA hU hbase d hx
  rw [scalarDerivativeJet_directional (hφ.of_le (by exact_mod_cast (show k+1 ≤ k+3 by omega)))] at hh
  exact hh

end GaussianTilt.MomentMapSchauder
