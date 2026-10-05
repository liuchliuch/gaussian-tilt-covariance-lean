import GaussianTilt.MomentMapSchauderInteriorFirstJet
import GaussianTilt.MomentMapSchauderVectorDifferences
import GaussianTilt.MomentMapSchauderSourceCoefficients

/-! # Genuine Euclidean source quotient equation and compact coefficient bounds -/
noncomputable section
open Matrix MeasureTheory Set
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma continuous_euclideanHessianMatrix {φ : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Continuous (euclideanHessianMatrix φ) := by
  have hh := ((hφ.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  exact continuous_pi (fun i => continuous_pi (fun j =>
    (hh.clm_apply continuous_const).clm_apply continuous_const))

lemma euclideanHessianMatrix_isSymm {φ : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ) (x : KernelSpace n) :
    (euclideanHessianMatrix φ x).IsSymm := by
  ext i j
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by norm_num)) _ _

lemma euclideanHessianMatrix_vectorDifferenceQuotient {φ : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (h x : KernelSpace n) (s : ℝ) :
    euclideanHessianMatrix (vectorDifferenceQuotient φ h s) x =
      s⁻¹ • (euclideanHessianMatrix φ (x+h)-euclideanHessianMatrix φ x) := by
  ext i j
  simp only [euclideanHessianMatrix, secondFrechet_vectorDifferenceQuotient hφ,
    vectorDifferenceQuotient, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]

def euclideanSourceCoefficient (φ : KernelSpace n → ℝ) (h x : KernelSpace n) :
    Matrix (Fin n) (Fin n) ℝ := averagedInverse (euclideanHessianMatrix φ x) (euclideanHessianMatrix φ (x+h))

/-- The actual finite-difference PDE requires only C² source regularity.
The coefficient is exactly the integral of inverse interpolated Hessians. -/
theorem euclidean_source_quotient_equation {φ g : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (euclideanHessianMatrix φ x).det=g x)
    (h x : KernelSpace n) (s : ℝ) :
    euclideanEllipticOperator (euclideanSourceCoefficient φ h x) (vectorDifferenceQuotient φ h s) x =
      vectorDifferenceQuotient g h s x := by
  have htrace : Matrix.trace (euclideanSourceCoefficient φ h x *
      euclideanHessianMatrix (vectorDifferenceQuotient φ h s) x) =
      vectorDifferenceQuotient g h s x := by
    rw [euclideanHessianMatrix_vectorDifferenceQuotient hφ, Matrix.mul_smul, Matrix.trace_smul]
    change s⁻¹*Matrix.trace (averagedInverse (euclideanHessianMatrix φ x) (euclideanHessianMatrix φ (x+h)) *
      (euclideanHessianMatrix φ (x+h)-euclideanHessianMatrix φ x)) = _
    rw [← logdet_sub_eq_trace_averagedInverse (hpos x) (hpos (x+h)), hMA (x+h), hMA x]
    rfl
  have hsym := euclideanHessianMatrix_isSymm (contDiff_vectorDifferenceQuotient hφ h s) x
  convert htrace using 1
  simp only [euclideanEllipticOperator, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hsym.apply i j]
  rfl

lemma abs_averagedInverse_entry_le {A B : Matrix (Fin n) (Fin n) ℝ} {M : ℝ}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j, |(matrixSegment A B t)⁻¹ i j| ≤ M) (i j : Fin n) :
    |averagedInverse A B i j| ≤ M := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := M) (f := fun t => (matrixSegment A B t)⁻¹ i j) (fun t ht => by
      rw [Real.norm_eq_abs]
      exact hb t (Ioc_subset_Icc_self (by simpa only [uIoc_of_le (show (0 : ℝ)≤1 by norm_num)] using ht)) i j)
  simpa only [averagedInverse, Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hh

/-- All coefficient constants are consequences of an actual positive C²,α
Hessian on one compact set. They are uniform over every admissible step. -/
theorem exists_euclidean_source_coefficient_bounds {φ : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    {S : Set (KernelSpace n)} (hS : IsCompact S) {H α : ℝ} (hH : 0 ≤ H)
    (hh : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ ≤ H*‖x-y‖^α) :
    ∃ lam Λ M K : ℝ, 0 < lam ∧ 0 < Λ ∧ 0 < M ∧ 0 < K ∧
      (∀ h x : KernelSpace n, x ∈ S → x+h ∈ S →
        (euclideanSourceCoefficient φ h x).PosDef ∧
        (∀ i j, |euclideanSourceCoefficient φ h x i j| ≤ M) ∧
        (∀ v, lam*‖v‖^2 ≤ euclideanQuadratic (euclideanSourceCoefficient φ h x) v ∧
          euclideanQuadratic (euclideanSourceCoefficient φ h x) v ≤ Λ*‖v‖^2)) ∧
      (∀ h x y : KernelSpace n, x ∈ S → x+h ∈ S → y ∈ S → y+h ∈ S → ∀ i j,
        |euclideanSourceCoefficient φ h x i j-euclideanSourceCoefficient φ h y i j| ≤ K*‖x-y‖^α) := by
  have hcont : ContinuousOn (euclideanHessianMatrix φ) S := (continuous_euclideanHessianMatrix hφ).continuousOn
  obtain ⟨M, hM, hMb⟩ := exists_bound_inv_segments_on_compact hS hcont (fun x _ => hpos x)
  obtain ⟨lam, Λ, hlam, hΛ, hell⟩ := exists_uniform_ellipticity_averagedInverse_on_compact hS hcont (fun x _ => hpos x)
  let K := (n : ℝ)^2*M^2*H+1
  refine ⟨lam, Λ, M, K, hlam, hΛ, hM, by dsimp [K]; positivity, ?_, ?_⟩
  · intro h x hx hxh
    exact ⟨averagedInverse_posDef (hpos x) (hpos (x+h)),
      abs_averagedInverse_entry_le (hMb x hx (x+h) hxh), hell x hx (x+h) hxh⟩
  · intro h x y hx hxh hy hyh i j
    have hp := Real.rpow_nonneg (norm_nonneg (x-y)) α
    have he : (x+h)-(y+h)=x-y := by abel
    have hh' : ∀ a ∈ S, ∀ b ∈ S, ∀ i j,
        |euclideanHessianMatrix φ a i j-euclideanHessianMatrix φ b i j| ≤ H*‖a-b‖^α := by
      intro a ha b hb i j
      exact (abs_euclidean_bilinear_entry_le_norm
        (fderiv ℝ (fderiv ℝ φ) a-fderiv ℝ (fderiv ℝ φ) b) i j).trans (hh a ha b hb)
    have hb := abs_averagedInverse_entry_sub_le (hpos x) (hpos (x+h)) (hpos y) (hpos (y+h))
      hM.le (mul_nonneg hH hp) (hMb x hx (x+h) hxh) (hMb y hy (y+h) hyh)
      (hh' x hx y hy) (by simpa only [he] using hh' (x+h) hxh (y+h) hyh) i j
    change |euclideanSourceCoefficient φ h x i j-euclideanSourceCoefficient φ h y i j| ≤ _ at hb
    apply hb.trans
    simp only [Fintype.card_fin]
    dsimp [K]
    nlinarith

end GaussianTilt.MomentMapSchauder
