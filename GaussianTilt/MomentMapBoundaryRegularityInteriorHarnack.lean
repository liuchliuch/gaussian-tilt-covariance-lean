import GaussianTilt.MomentMapBoundaryRegularityLogarithm

/-!
# Genuine interior Harnack from rescaled coefficient derivative bounds

The logarithm is constructed only near the ball. The original function
need not be positive away from that neighborhood. No Harnack inequality or
log-gradient estimate is assumed.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Quantitative Harnack under relative source and source-gradient bounds.
For a nonnegative solution with bounded forcing, adding its forcing scale
supplies these relative bounds. -/
theorem exists_interior_harnack_of_coefficient_derivative_bounds {lam Λ K G : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) (hG : 0 ≤ G) :
    ∃ H : ℝ, 0 < H ∧
      ∀ (v f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ∞ v → Differentiable ℝ f →
      (∀ i j, Differentiable ℝ (fun y => A y i j)) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 2 → 0 < v y) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → (A y).PosSemidef) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → ∀ w : CoordinateSpace n,
        lam * ‖(coordinateEquiv n).symm w‖^2 ≤ w ⬝ᵥ (A y *ᵥ w) ∧
        w ⬝ᵥ (A y *ᵥ w) ≤ Λ * ‖(coordinateEquiv n).symm w‖^2) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 →
        ∀ k i j, |matrixCoordinateDerivative A k y i j| ≤ K) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → |f y| ≤ G * v y) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → ∀ k, |coordinateDerivative k f y| ≤ G * v y) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → linearizedMA (A y) v y = f y) →
      ∀ x y, ‖(coordinateEquiv n).symm x‖ ≤ 1/2 → ‖(coordinateEquiv n).symm y‖ ≤ 1/2 →
        v x ≤ H * v y := by
  obtain ⟨L,hL,hosc⟩ := exists_bernstein_unit_ball_oscillation (n := n) hlam hΛ hK hG
  refine ⟨Real.exp L, Real.exp_pos _, ?_⟩
  intro v f A hv hf hAd hpos hA hEll hDA hfb hDfb hP
  obtain ⟨φ,hφ,heq⟩ := exists_smooth_logarithm_near_unit_ball hv hpos
  let h := fun y => f y / v y
  have hpoint (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y‖ < 1) : 0 < v y :=
    hpos y (by linarith)
  have hdφ (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y‖ ≤ 1) (k : Fin n) :
      coordinateDerivative k φ y = coordinateDerivative k (fun z => Real.log (v z)) y :=
    coordinateDerivative_congr_nhds (heq y hy) k
  have hgφ (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y‖ ≤ 1) :
      coordinateGradient φ y = coordinateGradient (fun z => Real.log (v z)) y := by
    ext k
    exact hdφ y hy k
  have hquot (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y‖ < 1) :=
    logarithmic_forcing_bounds (hf y) (hv.differentiable (by simp) y) (hpoint y hy) hG (hfb y hy) (hDfb y hy)
  have hψP (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y‖ < 1) :
      linearizedMA (A y) φ y + coordinateGradient φ y ⬝ᵥ (A y *ᵥ coordinateGradient φ y) = h y := by
    have hHφ := coordinateHessian_congr_nhds (heq y hy.le)
    rw [linearizedMA, hHφ, hgφ y hy.le]
    change linearizedMA (A y) (fun z => Real.log (v z)) y + _ = _
    rw [logarithmic_equation_of_linear_equation hv _ (hpoint y hy).ne', hP y hy]
  have hψosc := hosc φ h A hφ hAd hA hEll hDA (fun y hy => (hquot y hy).1)
    (fun y hy k => by rw [hdφ y hy.le k]; exact (hquot y hy).2 k) hψP
  intro x y hx hy
  have hx1 : ‖(coordinateEquiv n).symm x‖ ≤ 1 := by linarith
  have hy1 : ‖(coordinateEquiv n).symm y‖ ≤ 1 := by linarith
  have hxpos := hpos x (by linarith)
  have hypos := hpos y (by linarith)
  have hxyraw : ‖x-y‖ ≤ 1 := by
    have hraw (z : CoordinateSpace n) : ‖z‖ ≤ ‖(coordinateEquiv n).symm z‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      exact PiLp.norm_apply_le ((coordinateEquiv n).symm z) i
    have htri := norm_sub_le x y
    linarith [hraw x, hraw y]
  have hl : Real.log (v x) - Real.log (v y) ≤ L := by
    have ho := hψosc x y hx hy
    rw [(heq x hx1).self_of_nhds, (heq y hy1).self_of_nhds] at ho
    exact (le_abs_self _).trans (ho.trans (by nlinarith))
  have hexp := Real.exp_le_exp.mpr (show Real.log (v x) ≤ L + Real.log (v y) by linarith)
  rwa [Real.exp_add, Real.exp_log hxpos, Real.exp_log hypos] at hexp

/-- Additive Harnack for a genuinely nonnegative function with bounded
forcing and bounded first forcing derivatives. Positivity is obtained by
adding a vanishing constant, and the limit is proved here. -/
theorem exists_interior_harnack_with_bounded_forcing {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ H : ℝ, 0 < H ∧
      ∀ (v f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ∞ v → Differentiable ℝ f →
      (∀ i j, Differentiable ℝ (fun y => A y i j)) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 2 → 0 ≤ v y) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → (A y).PosSemidef) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → ∀ w : CoordinateSpace n,
        lam * ‖(coordinateEquiv n).symm w‖^2 ≤ w ⬝ᵥ (A y *ᵥ w) ∧
        w ⬝ᵥ (A y *ᵥ w) ≤ Λ * ‖(coordinateEquiv n).symm w‖^2) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 →
        ∀ k i j, |matrixCoordinateDerivative A k y i j| ≤ K) →
      ∀ F : ℝ, 0 ≤ F →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → |f y| ≤ F) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → ∀ k, |coordinateDerivative k f y| ≤ F) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → linearizedMA (A y) v y = f y) →
      ∀ x y, ‖(coordinateEquiv n).symm x‖ ≤ 1/2 → ‖(coordinateEquiv n).symm y‖ ≤ 1/2 →
        v x ≤ H * (v y + F) := by
  obtain ⟨H,hH,harnack⟩ := exists_interior_harnack_of_coefficient_derivative_bounds (n := n)
    hlam hΛ hK (show 0 ≤ (1:ℝ) by norm_num)
  refine ⟨H,hH,?_⟩
  intro v f A hv hf hAd hn hA hEll hDA F hF hfb hDfb hP x y hx hy
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/H
  have hδ : 0 < δ := div_pos hε hH
  let w : CoordinateSpace n → ℝ := fun z => v z + (F+δ)
  have hw : ContDiff ℝ ∞ w := hv.add contDiff_const
  have hwp (z : CoordinateSpace n) (hz : ‖(coordinateEquiv n).symm z‖ < 2) : 0 < w z := by
    dsimp [w]
    linarith [hn z hz]
  have hFw (z : CoordinateSpace n) (hz : ‖(coordinateEquiv n).symm z‖ < 1) : F ≤ w z := by
    dsimp [w]
    linarith [hn z (by linarith)]
  have hwP (z : CoordinateSpace n) (hz : ‖(coordinateEquiv n).symm z‖ < 1) :
      linearizedMA (A z) w z = f z := by
    rw [linearizedMA_add_at _ (contDiff_infty.mp hv 2).contDiffAt contDiffAt_const,
      linearizedMA_const, add_zero]
    exact hP z hz
  have hh := harnack w f A hw hf hAd hwp hA hEll hDA
    (fun z hz => by simpa only [one_mul] using (hfb z hz).trans (hFw z hz))
    (fun z hz k => by simpa only [one_mul] using (hDfb z hz k).trans (hFw z hz)) hwP x y hx hy
  have he : H*δ = ε := mul_div_cancel₀ ε hH.ne'
  dsimp [w] at hh
  nlinarith

end GaussianTilt.MomentMapRegularity
