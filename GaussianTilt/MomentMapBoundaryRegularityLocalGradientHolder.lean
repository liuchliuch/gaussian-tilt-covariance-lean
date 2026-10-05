import GaussianTilt.MomentMapBoundaryRegularityLocalResidualGradient

/-!
# Genuine approach of the interior gradient to the boundary jet

The actual quotient Hölder decay controls the affine residual. A signed
interior gradient estimate then controls its true derivatives. All smooth
representatives are constructed strictly inside the domain.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

theorem exists_local_flat_interior_gradient_holder [NeZero n] {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ (j : Fin n) (u f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (M B : ℝ) (D : CoordinateSpace n →L[ℝ] ℝ),
      0 ≤ M → 0 ≤ B → LocalFlatEllipticSystem j u f A lam Λ K M →
      HasFDerivWithinAt u D (flatClosedHalfBall j) 0 →
      (∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → 0 ≤ y j → |u y| ≤ B*y j) →
      ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1/4 → 0 < x j →
      ∀ i, |coordinateDerivative i u x-D (Pi.single j 1)*(if i=j then 1 else 0)| ≤
        C*(B+M)*‖(coordinateEquiv n).symm x‖^α := by
  obtain ⟨α,ε₀,hα,hα1,hε,hholder⟩ := exists_local_flat_boundary_quotient_holder (n := n) hlam hΛ hK
  obtain ⟨C₀,hC₀,hres⟩ := exists_local_boundary_residual_gradient_bound (n := n) hlam hΛ hK
  let L := 33+16/ε₀
  have hL : 0 < L := by dsimp only [L]; positivity
  refine ⟨α,(C₀+1)*L,hα,hα1,by positivity,?_⟩
  intro j u f A M B D hM hB hs hD hb x hx ht i
  let d := ‖(coordinateEquiv n).symm x‖
  have htd : x j ≤ d := (le_abs_self _).trans (abs_coordinate_le_euclidean_norm x j)
  have hd : 0 < d := ht.trans_le htd
  have hd1 : d ≤ 1 := by dsimp only [d]; linarith
  have h2d : 2*d ∈ Ioc (0:ℝ) 1 := ⟨by positivity,by dsimp only [d]; linarith⟩
  have hosc := hholder j u f A M B hM hB hs hb (2*d) h2d
  have htwo : (2:ℝ)^α ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hα1
    simpa only [Real.rpow_one] using h
  have hW : boundaryQuotientOscillation u j (2*d) ≤ 16*(2*B+M/ε₀)*d^α := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hd.le] at hosc
    have hh := mul_le_mul_of_nonneg_left htwo (show 0 ≤ 8*(2*B+M/ε₀)*d^α by positivity)
    nlinarith
  have htα : x j ≤ d^α := htd.trans (Real.self_le_rpow_of_le_one hd.le hd1 hα1)
  have hMα := mul_le_mul_of_nonneg_left htα hM
  have hsum : boundaryQuotientOscillation u j (2*d)+M*x j ≤ (16*(2*B+M/ε₀)+M)*d^α := by
    nlinarith
  have hcoef : 16*(2*B+M/ε₀)+M ≤ L*(B+M) := by
    have hn : 0 ≤ (16/ε₀)*B := by positivity
    dsimp only [L]
    simp only [div_eq_mul_inv] at hn ⊢
    nlinarith
  have hcoef2 : C₀*(16*(2*B+M/ε₀)+M) ≤ (C₀+1)*L*(B+M) := by
    have h1 := mul_le_mul_of_nonneg_left hcoef hC₀.le
    have hn : 0 ≤ L*(B+M) := by positivity
    nlinarith
  have hg := hres j u f A M B D hM hB hs hD hb x hx ht i
  apply hg.trans
  have h1 := mul_le_mul_of_nonneg_left hsum hC₀.le
  have h2 := mul_le_mul_of_nonneg_right hcoef2 (Real.rpow_nonneg hd.le α)
  change C₀*(boundaryQuotientOscillation u j (2*d)+M*x j) ≤ (C₀+1)*L*(B+M)*d^α
  nlinarith

end GaussianTilt.MomentMapRegularity
