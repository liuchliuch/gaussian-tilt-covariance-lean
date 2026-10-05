import GaussianTilt.MomentMapBoundaryRegularityFlatPositivity

/-!
# Genuine one-step contraction of the boundary normal quotient

The two nonnegative functions `v` and `x_j-v` satisfy opposite forcings.
One is large at the corkscrew point, and the proved boundary positivity
lemma then removes a fixed part of the slope interval.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

theorem exists_flat_boundary_quotient_contraction [NeZero n] {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ δ ε₀ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ 0 < ε₀ ∧
      ∀ (j : Fin n) (v f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ∞ v → Differentiable ℝ f → (∀ i k, Differentiable ℝ (fun y => A y i k)) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → 0 ≤ y j → 0 ≤ v y ∧ v y ≤ y j) →
      (∀ y ∈ flatHalfBall j, (A y).PosDef) →
      (∀ y ∈ flatHalfBall j, ∀ w : CoordinateSpace n,
        lam*‖(coordinateEquiv n).symm w‖^2 ≤ w ⬝ᵥ (A y *ᵥ w) ∧
        w ⬝ᵥ (A y *ᵥ w) ≤ Λ*‖(coordinateEquiv n).symm w‖^2) →
      (∀ y ∈ flatHalfBall j, ∀ k a b, y j*|matrixCoordinateDerivative A k y a b| ≤ K) →
      (∀ y ∈ flatHalfBall j, |f y| ≤ ε₀) →
      (∀ y ∈ flatHalfBall j, ∀ k, y j*|coordinateDerivative k f y| ≤ ε₀) →
      (∀ y ∈ flatHalfBall j, linearizedMA (A y) v y = f y) →
      ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ b-a ≤ 1-δ ∧
        ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1/8 → 0 ≤ x j → a*x j ≤ v x ∧ v x ≤ b*x j := by
  obtain ⟨δ,ε₀,hδ,hδ1,hε,hpos⟩ := exists_flat_boundary_positivity (n := n) hlam hΛ hK
  refine ⟨δ,ε₀,hδ,hδ1,hε,?_⟩
  intro j v f A hv hf hAd hrange hA hEll hDA hfb hDfb hP
  have hcoord : ContDiff ℝ ∞ (fun y : CoordinateSpace n => y j) := by fun_prop
  have hcoord2 : ContDiff ℝ 2 (fun y : CoordinateSpace n => y j) := contDiff_infty.mp hcoord 2
  by_cases hcorn : 1/8 ≤ v (Pi.single j (1/4))
  · have hlower := hpos j v f A hv hf hAd (fun y hy hj => (hrange y hy hj).1)
      hA hEll hDA hfb hDfb hP hcorn
    refine ⟨δ,1,hδ.le,by linarith,le_rfl,le_rfl,?_⟩
    intro x hx hj
    exact ⟨hlower x hx hj, by simpa only [one_mul] using (hrange x (by linarith) hj).2⟩
  · let w : CoordinateSpace n → ℝ := fun y => y j-v y
    have hw : ContDiff ℝ ∞ w := hcoord.sub hv
    have hn (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y‖ ≤ 1) (hj : 0 ≤ y j) : 0 ≤ w y :=
      sub_nonneg.mpr (hrange y hy hj).2
    have hfw (y : CoordinateSpace n) (hy : y ∈ flatHalfBall j) : |(-f) y| ≤ ε₀ := by
      simpa only [Pi.neg_apply,abs_neg] using hfb y hy
    have hDfw (y : CoordinateSpace n) (hy : y ∈ flatHalfBall j) (k : Fin n) :
        y j*|coordinateDerivative k (-f) y| ≤ ε₀ := by
      change y j*|coordinateDerivative k (fun z => -f z) y| ≤ ε₀
      rw [coordinateDerivative_neg,abs_neg]
      exact hDfb y hy k
    have hPw (y : CoordinateSpace n) (hy : y ∈ flatHalfBall j) : linearizedMA (A y) w y = (-f) y := by
      rw [linearizedMA_sub_at _ hcoord2.contDiffAt (contDiff_infty.mp hv 2).contDiffAt]
      have hz : linearizedMA (A y) (fun z => z j) y = 0 := by
        simp only [linearizedMA,coordinateHessian_coordinate,Matrix.mul_zero,Matrix.trace_zero]
      rw [hz,hP y hy]
      simp
    have hwcorn : 1/8 ≤ w (Pi.single j (1/4)) := by
      dsimp [w]
      simp only [Pi.single_eq_same]
      linarith
    have hlower := hpos j w (-f) A hw hf.neg hAd hn hA hEll hDA hfw hDfw hPw hwcorn
    refine ⟨0,1-δ,le_rfl,by linarith,by linarith,by simp,?_⟩
    intro x hx hj
    have hl := hlower x hx hj
    change δ*x j ≤ x j-v x at hl
    exact ⟨by simpa only [zero_mul] using (hrange x (by linarith) hj).1, by nlinarith⟩

end GaussianTilt.MomentMapRegularity
