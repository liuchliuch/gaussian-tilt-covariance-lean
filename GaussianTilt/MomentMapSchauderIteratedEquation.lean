import GaussianTilt.MomentMapSchauderDifferentiatedEquation

/-! # Literal iterated elliptic equations and regularity of their true forcing -/
noncomputable section
set_option maxHeartbeats 2000000
open Matrix Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def scalarDerivativeJet (k : ℕ) (u : KernelSpace n → ℝ) (v : Fin k → KernelSpace n) : KernelSpace n → ℝ :=
  fun x => iteratedFDeriv ℝ k u x v

lemma contDiff_scalarDerivativeJet (k m : ℕ) {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ (↑(m + k) : WithTop ℕ∞) u) (v : Fin k → KernelSpace n) :
    ContDiff ℝ (m : WithTop ℕ∞) (scalarDerivativeJet k u v) := by
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => KernelSpace n) ℝ v).contDiff.comp
    (hu.iteratedFDeriv_right (by simp only [Nat.cast_add, le_refl]))

@[simp] lemma scalarDerivativeJet_zero (u : KernelSpace n → ℝ) (v : Fin 0 → KernelSpace n) :
    scalarDerivativeJet 0 u v = u := by
  funext x
  simp only [scalarDerivativeJet, iteratedFDeriv_zero_apply]

lemma scalarDerivativeJet_succ {k : ℕ} {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ (↑(k + 1) : WithTop ℕ∞) u) (v : Fin (k + 1) → KernelSpace n) :
    scalarDerivativeJet (k + 1) u v = kernelDirectionalDerivative (v 0) (scalarDerivativeJet k u (Fin.tail v)) := by
  have hc : ContDiff ℝ 1 (iteratedFDeriv ℝ k u) := hu.iteratedFDeriv_right (by simp [Nat.cast_add, add_comm])
  funext x
  exact (fderiv_continuousMultilinear_apply_const_apply (hc.differentiable le_rfl x) (Fin.tail v) (v 0)).symm

def iteratedEllipticForcing (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (u f : KernelSpace n → ℝ) : (k : ℕ) → (Fin k → KernelSpace n) → KernelSpace n → ℝ
  | 0, _ => f
  | k + 1, v => fun x =>
      kernelDirectionalDerivative (v 0) (iteratedEllipticForcing A u f k (Fin.tail v)) x -
        ellipticDerivativeError A (scalarDerivativeJet k u (Fin.tail v)) (v 0) x

lemma contDiff_ellipticDerivativeError {m : ℕ} {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ (↑(m + 2) : WithTop ℕ∞) u)
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ (↑(m + 1) : WithTop ℕ∞) (fun x => A x i j))
    (v : KernelSpace n) : ContDiff ℝ (m : WithTop ℕ∞) (ellipticDerivativeError A u v) := by
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  have hc : ContDiff ℝ (m : WithTop ℕ∞) (fun x => fderiv ℝ (fun y => A y i j) x v) :=
    ((hA i j).fderiv_right (by simp only [Nat.cast_add, Nat.cast_one, le_refl])).clm_apply contDiff_const
  exact hc.mul (contDiff_secondFrechet_entry (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hu) _ _)

/-- Every forcing term is genuinely Cᵐ from the displayed lower-order
source/coefficient/forcing derivatives. No differentiability of a formal
forcing symbol is assumed. -/
theorem contDiff_iteratedEllipticForcing (k m : ℕ)
    {u f : KernelSpace n → ℝ} (hu : ContDiff ℝ (↑(k + m + 1) : WithTop ℕ∞) u)
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ (↑(k + m) : WithTop ℕ∞) (fun x => A x i j))
    (hf : ContDiff ℝ (↑(k + m) : WithTop ℕ∞) f) (v : Fin k → KernelSpace n) :
    ContDiff ℝ (m : WithTop ℕ∞) (iteratedEllipticForcing A u f k v) := by
  induction k generalizing m with
  | zero => simpa only [iteratedEllipticForcing, zero_add] using hf
  | succ k ih =>
    have hprev : ContDiff ℝ (↑(m + 1) : WithTop ℕ∞) (iteratedEllipticForcing A u f k (Fin.tail v)) :=
      ih (m + 1) (by convert hu using 1 <;> congr 1 <;> omega)
        (fun i j => by convert hA i j using 1 <;> congr 1 <;> omega)
        (by convert hf using 1 <;> congr 1 <;> omega) (Fin.tail v)
    have hjet : ContDiff ℝ (↑(m + 2) : WithTop ℕ∞) (scalarDerivativeJet k u (Fin.tail v)) :=
      contDiff_scalarDerivativeJet k (m + 2) (by convert hu using 1 <;> congr 1 <;> omega) (Fin.tail v)
    have hAsmall : ∀ i j, ContDiff ℝ (↑(m + 1) : WithTop ℕ∞) (fun x => A x i j) :=
      fun i j => (hA i j).of_le (by exact_mod_cast (show m + 1 ≤ k + 1 + m by omega))
    exact (contDiff_kernelDirectionalDerivative
      (by simpa only [Nat.cast_add, Nat.cast_one] using hprev) (v 0)).sub
      (contDiff_ellipticDerivativeError hjet hAsmall (v 0))

/-- All iterated equations are literal equations of actual Fréchet jets,
proved by real product rules and repeated differentiation of the original PDE. -/
theorem iterated_differentiated_elliptic_equation (k : ℕ)
    {u f : KernelSpace n → ℝ} (hu : ContDiff ℝ (↑(k + 2) : WithTop ℕ∞) u)
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (heq : ∀ x, euclideanEllipticOperator (A x) u x = f x)
    (v : Fin k → KernelSpace n) (x : KernelSpace n) :
    euclideanEllipticOperator (A x) (scalarDerivativeJet k u v) x =
      iteratedEllipticForcing A u f k v x := by
  induction k generalizing x with
  | zero => simpa only [scalarDerivativeJet_zero, iteratedEllipticForcing] using heq x
  | succ k ih =>
    have hu' : ContDiff ℝ (↑(k + 2) : WithTop ℕ∞) u :=
      hu.of_le (by exact_mod_cast (show k + 2 ≤ k + 1 + 2 by omega))
    have hjet : ContDiff ℝ 3 (scalarDerivativeJet k u (Fin.tail v)) :=
      contDiff_scalarDerivativeJet k 3 (by convert hu using 1 <;> congr 1 <;> omega) (Fin.tail v)
    have hp : ∀ y, euclideanEllipticOperator (A y) (scalarDerivativeJet k u (Fin.tail v)) y =
        iteratedEllipticForcing A u f k (Fin.tail v) y := fun y => ih hu' (Fin.tail v) y
    have hstep := differentiated_elliptic_equation hjet hA hp (v 0) x
    rw [scalarDerivativeJet_succ (hu.of_le (by exact_mod_cast (show k + 1 ≤ k + 1 + 2 by omega)))]
    exact hstep

end GaussianTilt.MomentMapSchauder
