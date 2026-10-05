import GaussianTilt.MomentMapBoundaryRegularityQuotientContraction

/-! # Boundary slope-interval contraction with the forcing error retained -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

theorem exists_flat_boundary_slope_contraction [NeZero n] {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ δ ε₀ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ 0 < ε₀ ∧
      ∀ (j : Fin n) (u f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ∞ u → Differentiable ℝ f → (∀ i k, Differentiable ℝ (fun y => A y i k)) →
      (∀ y ∈ flatHalfBall j, (A y).PosDef) →
      (∀ y ∈ flatHalfBall j, ∀ w : CoordinateSpace n,
        lam*‖(coordinateEquiv n).symm w‖^2 ≤ w ⬝ᵥ (A y *ᵥ w) ∧
        w ⬝ᵥ (A y *ᵥ w) ≤ Λ*‖(coordinateEquiv n).symm w‖^2) →
      (∀ y ∈ flatHalfBall j, ∀ k a b, y j*|matrixCoordinateDerivative A k y a b| ≤ K) →
      ∀ M a b : ℝ, 0 ≤ M → a ≤ b →
      (∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → 0 ≤ y j → a*y j ≤ u y ∧ u y ≤ b*y j) →
      (∀ y ∈ flatHalfBall j, |f y| ≤ M) →
      (∀ y ∈ flatHalfBall j, ∀ k, y j*|coordinateDerivative k f y| ≤ M) →
      (∀ y ∈ flatHalfBall j, linearizedMA (A y) u y = f y) →
      ∃ a' b' : ℝ, a ≤ a' ∧ a' ≤ b' ∧ b' ≤ b ∧ b'-a' ≤ (1-δ)*(b-a)+M/ε₀ ∧
        ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1/8 → 0 ≤ x j → a'*x j ≤ u x ∧ u x ≤ b'*x j := by
  obtain ⟨δ,ε₀,hδ,hδ1,hε,hcontract⟩ := exists_flat_boundary_quotient_contraction (n := n) hlam hΛ hK
  refine ⟨δ,ε₀,hδ,hδ1,hε,?_⟩
  intro j u f A hu hf hAd hA hEll hDA M a b hM hab hrange hfb hDfb hP
  have hcoord : ContDiff ℝ ∞ (fun y : CoordinateSpace n => y j) := by fun_prop
  have hcoord2 : ContDiff ℝ 2 (fun y : CoordinateSpace n => y j) := contDiff_infty.mp hcoord 2
  by_cases hsmall : b-a ≤ M/ε₀
  · refine ⟨a,b,le_rfl,hab,le_rfl,?_,?_⟩
    · nlinarith
    · intro x hx hj
      exact hrange x (by linarith) hj
  · let W := b-a
    have hW : 0 < W := lt_of_le_of_lt (div_nonneg hM hε.le) (lt_of_not_ge hsmall)
    have hMW : M/W ≤ ε₀ := by
      apply (div_le_iff₀ hW).mpr
      have hh := (div_lt_iff₀ hε).mp (lt_of_not_ge hsmall)
      dsimp [W]
      linarith
    let v : CoordinateSpace n → ℝ := fun y => W⁻¹*(u y-a*y j)
    let g : CoordinateSpace n → ℝ := fun y => W⁻¹*f y
    have hv : ContDiff ℝ ∞ v := contDiff_const.mul (hu.sub (contDiff_const.mul hcoord))
    have hg : Differentiable ℝ g := hf.const_mul _
    have hvbound (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y‖ ≤ 1) (hj : 0 ≤ y j) :
        0 ≤ v y ∧ v y ≤ y j := by
      have h := hrange y hy hj
      have he : W*v y = u y-a*y j := by dsimp [v]; field_simp
      have hWj : W*y j = b*y j-a*y j := by dsimp [W]; ring
      constructor <;> nlinarith
    have hgb (y : CoordinateSpace n) (hy : y ∈ flatHalfBall j) : |g y| ≤ ε₀ := by
      dsimp [g]
      rw [abs_mul,abs_of_pos (inv_pos.mpr hW)]
      calc
        _ ≤ W⁻¹*M := mul_le_mul_of_nonneg_left (hfb y hy) (inv_nonneg.mpr hW.le)
        _ = M/W := by ring
        _ ≤ ε₀ := hMW
    have hDgb (y : CoordinateSpace n) (hy : y ∈ flatHalfBall j) (k : Fin n) :
        y j*|coordinateDerivative k g y| ≤ ε₀ := by
      rw [coordinateDerivative_const_mul hf,abs_mul,abs_of_pos (inv_pos.mpr hW)]
      have hh := mul_le_mul_of_nonneg_left (hDfb y hy k) (inv_nonneg.mpr hW.le)
      have he : W⁻¹*M = M/W := by ring
      rw [he] at hh
      nlinarith
    have hgP (y : CoordinateSpace n) (hy : y ∈ flatHalfBall j) : linearizedMA (A y) v y = g y := by
      rw [linearizedMA_const_mul_at _ ((contDiff_infty.mp hu 2).sub
        (contDiff_const.mul hcoord2)).contDiffAt,
        linearizedMA_sub_at _ (contDiff_infty.mp hu 2).contDiffAt
          (contDiffAt_const.mul hcoord2.contDiffAt),
        linearizedMA_const_mul_at _ hcoord2.contDiffAt]
      have hz : linearizedMA (A y) (fun z => z j) y = 0 := by
        simp only [linearizedMA,coordinateHessian_coordinate,Matrix.mul_zero,Matrix.trace_zero]
      rw [hz,mul_zero,sub_zero,hP y hy]
    obtain ⟨α,β,hα,hαβ,hβ,hwidth,hbound⟩ := hcontract j v g A hv hg hAd hvbound hA hEll hDA hgb hDgb hgP
    refine ⟨a+W*α,a+W*β,by nlinarith,by nlinarith,?_,?_,?_⟩
    · dsimp [W]
      nlinarith
    · have hh := mul_le_mul_of_nonneg_left hwidth hW.le
      have hnon := div_nonneg hM hε.le
      dsimp [W] at hh ⊢
      nlinarith
    · intro x hx hj
      have hb := hbound x hx hj
      have he : W*v x = u x-a*x j := by dsimp [v]; field_simp
      have hlo := mul_le_mul_of_nonneg_left hb.1 hW.le
      have hup := mul_le_mul_of_nonneg_left hb.2 hW.le
      constructor <;> nlinarith

end GaussianTilt.MomentMapRegularity
