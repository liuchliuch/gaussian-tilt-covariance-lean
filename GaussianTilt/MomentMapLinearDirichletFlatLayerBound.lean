import GaussianTilt.MomentMapLinearDirichletFlatTestBounds

/-! # Uniform actual boundary-layer integrand bounds -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma flat_layer_product_bound {a b l p s d₁ d₂ t C D M M₁ M₂ R : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (ht : 0 ≤ t) (htR : t ≤ R) (ha : |a| ≤ C*t) (hb : |b| ≤ D*t)
    (hl : |l| ≤ M) (hp : |p| ≤ D) (hs : |s| ≤ 1)
    (hd₁ : t*|d₁| ≤ 2*M₁) (hd₂ : t^2*|d₂| ≤ 4*M₂) :
    |a * (s*l + b*d₂ + 2*d₁*p)| ≤ C*R*M + 4*C*D*M₂ + 4*C*M₁*D := by
  have hR : 0 ≤ R := ht.trans htR
  have haR : |a| ≤ C*R := ha.trans (mul_le_mul_of_nonneg_left htR hC)
  have h1 : |a*s*l| ≤ C*R*M := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (C*R)*1*M := mul_le_mul (mul_le_mul haR hs (abs_nonneg _) (by positivity)) hl
        (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have h2 : |a*b*d₂| ≤ 4*C*D*M₂ := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (C*t)*(D*t)*|d₂| := mul_le_mul_of_nonneg_right
        (mul_le_mul ha hb (abs_nonneg _) (by positivity)) (abs_nonneg _)
      _ = (C*D)*(t^2*|d₂|) := by ring
      _ ≤ (C*D)*(4*M₂) := mul_le_mul_of_nonneg_left hd₂ (mul_nonneg hC hD)
      _ = _ := by ring
  have h3 : |2*a*d₁*p| ≤ 4*C*M₁*D := by
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 2*(C*t)*|d₁| * D := mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha (by norm_num)) (abs_nonneg _)) hp
        (abs_nonneg _) (by positivity)
      _ = (2*C)*(t*|d₁|)*D := by ring
      _ ≤ (2*C)*(2*M₁)*D := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd₁ (by positivity)) hD
      _ = _ := by ring
  have he : a*(s*l+b*d₂+2*d₁*p) = a*s*l+a*b*d₂+2*a*d₁*p := by ring
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)).trans (add_le_add (add_le_add h1 h2) h3)

/-- The cutoff error is uniformly bounded even though its first and
second derivatives grow like ε⁻¹ and ε⁻²; the genuine two boundary zeros
supply exactly the missing powers of height. -/
theorem flat_boundary_layer_integrand_bound (j : Fin n) {u ψ : KernelSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {C D M M₁ M₂ R ε : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hR : 0 ≤ R) (hε : 0 < ε)
    (hu0 : ∀ x, x j ≤ 0 → u x = 0)
    (hug : ∀ x ∈ tsupport ψ, |u x| ≤ C * |x j|)
    (hψg : ∀ x, |ψ x| ≤ D * |x j|)
    (hψd : ∀ x, |kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ j) ψ x| ≤ D)
    (hψlap : ∀ x, |kernelLaplacian ψ x| ≤ M)
    (hM₁b : ∀ t, |deriv flatBoundaryStep t| ≤ M₁)
    (hM₂b : ∀ t, |deriv (deriv flatBoundaryStep) t| ≤ M₂)
    (hRψ : ∀ x ∈ tsupport ψ, |x j| ≤ R) (x : KernelSpace n) (hx : x ∈ tsupport ψ) :
    |u x * kernelLaplacian (fun y => scaledFlatBoundaryStep ε (y j) * ψ y) x| ≤
      C*R*M + 4*C*D*M₂ + 4*C*M₁*D := by
  by_cases hxt : x j ≤ 0
  · rw [hu0 x hxt, zero_mul, abs_zero]
    positivity
  · have ht : 0 ≤ x j := (lt_of_not_ge hxt).le
    rw [kernelLaplacian_coordinate_cutoff (scaledFlatBoundaryStep_contDiff ε) hψ j]
    apply flat_layer_product_bound hC hD hM hM₁ hM₂ ht
      (by simpa only [abs_of_nonneg ht] using hRψ x hx)
      (by simpa only [abs_of_nonneg ht] using hug x hx)
      (by simpa only [abs_of_nonneg ht] using hψg x) (hψlap x) (hψd x)
      (by unfold scaledFlatBoundaryStep; rw [abs_of_nonneg (flatBoundaryStep_nonneg _)]; exact flatBoundaryStep_le_one _)
      (scaledFlatBoundaryStep_weighted_deriv_bound hε ht hM₁ hM₁b)
      (scaledFlatBoundaryStep_weighted_second_deriv_bound hε ht hM₂ hM₂b)

end GaussianTilt.MomentMapLinearDirichlet
