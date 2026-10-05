import GaussianTilt.MomentMapSchauderEuclideanFreezing
import GaussianTilt.MomentMapSchauderHolderInterpolation

/-!
# Explicit cutoff extension of a local coefficient field

The extension is the affine interpolation `A₀ + χ(A-A₀)`. Its closeness and
Hölder constant are proved from local coefficient data and the actual
cutoff, so no extension theorem or outside-domain regularity is assumed.
-/
noncomputable section
open Matrix Set Filter
open scoped Topology BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def cutoffCoefficient (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ) (χ : KernelSpace n → ℝ)
    (x : KernelSpace n) : Matrix (Fin n) (Fin n) ℝ := A₀ + χ x • (A x - A₀)

lemma cutoffCoefficient_eq_of_one {A₀ : Matrix (Fin n) (Fin n) ℝ}
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} {χ : KernelSpace n → ℝ}
    {x : KernelSpace n} (hx : χ x = 1) : cutoffCoefficient A₀ A χ x = A x := by
  simp [cutoffCoefficient, hx]

lemma cutoffCoefficient_eq_of_zero {A₀ : Matrix (Fin n) (Fin n) ℝ}
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} {χ : KernelSpace n → ℝ}
    {x : KernelSpace n} (hx : χ x = 0) : cutoffCoefficient A₀ A χ x = A₀ := by
  simp [cutoffCoefficient, hx]

lemma cutoffCoefficient_close {A₀ : Matrix (Fin n) (Fin n) ℝ}
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} {χ : KernelSpace n → ℝ}
    {S : Set (KernelSpace n)} {ε : ℝ} (hε : 0 ≤ ε)
    (hχ : ∀ x, |χ x| ≤ 1) (hsupp : ∀ x ∉ S, χ x = 0)
    (hA : ∀ x ∈ S, ∀ i j, |A₀ i j - A x i j| ≤ ε) :
    ∀ x i j, |A₀ i j - cutoffCoefficient A₀ A χ x i j| ≤ ε := by
  intro x i j
  by_cases hx : x ∈ S
  · have he : A₀ i j - cutoffCoefficient A₀ A χ x i j = χ x * (A₀ i j - A x i j) := by
      simp only [cutoffCoefficient, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    rw [he, abs_mul]
    exact (mul_le_mul (hχ x) (hA x hx i j) (abs_nonneg _) zero_le_one).trans_eq (one_mul ε)
  · rw [cutoffCoefficient_eq_of_zero (hsupp x hx), sub_self, abs_zero]
    exact hε

lemma cutoffCoefficient_holder {A₀ : Matrix (Fin n) (Fin n) ℝ}
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} {χ : KernelSpace n → ℝ}
    {S : Set (KernelSpace n)} {ε K L α : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hχ : ∀ x, |χ x| ≤ 1) (hχH : ∀ x y, |χ x - χ y| ≤ L * ‖x-y‖ ^ α)
    (hsupp : ∀ x ∉ S, χ x = 0)
    (hA : ∀ x ∈ S, ∀ i j, |A₀ i j - A x i j| ≤ ε)
    (hAH : ∀ x ∈ S, ∀ y ∈ S, ∀ i j, |A x i j - A y i j| ≤ K * ‖x-y‖ ^ α) :
    ∀ x y i j, |cutoffCoefficient A₀ A χ x i j - cutoffCoefficient A₀ A χ y i j| ≤
      (K + ε * L) * ‖x-y‖ ^ α := by
  intro x y i j
  have hb := global_holder_cutoff_product (f := fun z => A z i j - A₀ i j)
    zero_le_one hε hL hK hχ
    (fun z hz => by simpa only [abs_sub_comm] using hA z hz i j) hχH
    (fun z hz w hw => by simpa only [sub_sub_sub_cancel_right] using hAH z hz w hw i j) hsupp x y
  have he : cutoffCoefficient A₀ A χ x i j - cutoffCoefficient A₀ A χ y i j =
      χ x * (A x i j - A₀ i j) - χ y * (A y i j - A₀ i j) := by
    simp only [cutoffCoefficient, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  rw [he]
  simpa only [one_mul] using hb

/-- Altering the coefficients only outside the closed support of a potential
does not change the literal operator, because the actual second derivative
vanishes there. -/
theorem euclideanEllipticOperator_cutoffCoefficient {A₀ : Matrix (Fin n) (Fin n) ℝ}
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} {χ u : KernelSpace n → ℝ}
    (hχ : ∀ x ∈ tsupport u, χ x = 1) (x : KernelSpace n) :
    euclideanEllipticOperator (cutoffCoefficient A₀ A χ x) u x = euclideanEllipticOperator (A x) u x := by
  by_cases hx : x ∈ tsupport u
  · rw [cutoffCoefficient_eq_of_one (hχ x hx)]
  · have he : u =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hx
    have hzero : fderiv ℝ (fderiv ℝ u) x = 0 := by
      rw [he.fderiv.fderiv_eq]
      simp
    simp only [euclideanEllipticOperator, hzero, ContinuousLinearMap.zero_apply, mul_zero, Finset.sum_const_zero]

end GaussianTilt.MomentMapSchauder
