import GaussianTilt.MomentMapBoundaryRegularityBernsteinCalculus
import GaussianTilt.MomentMapBernsteinAlgebra

/-! # The genuine logarithmic-gradient differential inequality -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Constants are fixed before the smooth fields. All differential terms
come from the actual variable-coefficient equation. -/
theorem exists_bernstein_log_gradient_inequality {lam Λ K G : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) (hG : 0 ≤ G) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ (φ h : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ∞ φ → (∀ i j, Differentiable ℝ (fun y => A y i j)) →
      ∀ x : CoordinateSpace n, (A x).IsSymm →
      (∀ v : CoordinateSpace n, lam * (∑ i, v i ^ 2) ≤ v ⬝ᵥ (A x *ᵥ v)) →
      (∀ i j, |A x i j| ≤ Λ) → (∀ k i j, |matrixCoordinateDerivative A k x i j| ≤ K) →
      |h x| ≤ G → (∀ k, |coordinateDerivative k h x| ≤ G * (1 + |coordinateDerivative k φ x|)) →
      (∀ᶠ y in 𝓝 x, linearizedMA (A y) φ y +
        coordinateGradient φ y ⬝ᵥ (A y *ᵥ coordinateGradient φ y) = h y) →
      c * (gradientSquare φ x)^2 ≤ linearizedMA (A x) (gradientSquare φ) x +
        2 * (coordinateGradient φ x ⬝ᵥ (A x *ᵥ coordinateGradient (gradientSquare φ) x)) +
        C * (gradientSquare φ x + 1) := by
  obtain ⟨c, C, hc, hC, hfin⟩ := bernstein_log_gradient_coercivity (n := n) hlam hΛ hK hG
  refine ⟨c, C, hc, hC, ?_⟩
  intro φ h A hφ hA x hs hlo hAb hDb hh hdh heq
  have hHs := coordinateHessian_isSymm (contDiff_infty.mp hφ 2) x
  have htrace (M : Matrix (Fin n) (Fin n) ℝ) :
      (M * coordinateHessian φ x).trace = ∑ i, ∑ j, M i j * coordinateHessian φ x i j := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hHs.apply j i]
  have hquad (M : Matrix (Fin n) (Fin n) ℝ) (v : CoordinateSpace n) :
      v ⬝ᵥ (M *ᵥ v) = ∑ i, ∑ j, M i j * v i * v j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hP : (∑ i, ∑ j, A x i j * coordinateHessian φ x i j) +
      (∑ i, ∑ j, A x i j * coordinateGradient φ x i * coordinateGradient φ x j) = h x := by
    have hp := heq.self_of_nhds
    simpa only [linearizedMA, htrace, hquad] using hp
  have hbound := hfin (A x) (coordinateHessian φ x) (fun k => matrixCoordinateDerivative A k x)
    (coordinateGradient φ x) (coordinateGradient h x) (h x)
    (fun v => by simpa only [hquad] using hlo v) hAb hDb hh hdh hP
  have hrow (k : Fin n) : coordinateGradient (coordinateDerivative k φ) x =
      fun i => coordinateHessian φ x i k := by
    ext i
    exact hHs.apply i k
  rw [bernstein_log_gradient_identity hφ hA hs heq]
  simp_rw [hrow, htrace, hquad]
  convert hbound using 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul, coordinateGradient, gradientSquare]
  ring_nf
  simp only [mul_comm, mul_left_comm, mul_assoc]
  <;> ring

end GaussianTilt.MomentMapRegularity
