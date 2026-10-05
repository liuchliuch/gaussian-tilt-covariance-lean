import GaussianTilt.MomentMapBoundaryRegularityInteriorHarnack

/-! # Genuine interior gradient estimates for signed elliptic solutions -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

theorem exists_positive_solution_gradient_bound {lam Λ K G : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 < C ∧
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
      ∀ i, |coordinateDerivative i v 0| ≤ C*v 0 := by
  obtain ⟨B,hB,hgrad⟩ := exists_bernstein_ball_gradient_bound (n := n) hlam hΛ hK hG zero_lt_one
  refine ⟨Real.sqrt B,Real.sqrt_pos.mpr hB,?_⟩
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
  have hb : gradientSquare φ 0 ≤ B := hgrad φ h A 0 hφ hAd
    (fun y hy => hA y (by simpa only [map_zero,sub_zero] using hy))
    (fun y hy => hEll y (by simpa only [map_zero,sub_zero] using hy))
    (fun y hy => hDA y (by simpa only [map_zero,sub_zero] using hy))
    (fun y hy => (hquot y (by simpa only [map_zero,sub_zero] using hy)).1)
    (fun y hy k => by
      have hy1 : ‖(coordinateEquiv n).symm y‖ < 1 := by simpa only [map_zero,sub_zero] using hy
      rw [hdφ y hy1.le k]
      exact (hquot y hy1).2 k)
    (fun y hy => hψP y (by simpa only [map_zero,sub_zero] using hy))
  intro i
  have hd := abs_coordinateDerivative_le_sqrt_gradient_bound hB.le hb i
  have hp : 0 < v 0 := hpos 0 (by simp)
  rw [hdφ 0 (by simp) i,coordinateDerivative_log_at (hv.differentiable (by simp) 0) hp.ne',
    abs_mul,abs_of_pos (inv_pos.mpr hp)] at hd
  have hh := mul_le_mul_of_nonneg_left hd hp.le
  have he : v 0*((v 0)⁻¹*|coordinateDerivative i v 0|)=|coordinateDerivative i v 0| := by field_simp
  rw [he] at hh
  nlinarith

/-- Actual signed interior gradient estimate, with no logarithm,
positivity, or derivative estimate among the hypotheses. -/
theorem exists_signed_interior_gradient_bound {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (U F : ℝ),
      0 ≤ U → 0 ≤ F → ContDiff ℝ ∞ u → Differentiable ℝ f →
      (∀ i j, Differentiable ℝ (fun y => A y i j)) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 2 → |u y| ≤ U) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → (A y).PosSemidef) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → ∀ v : CoordinateSpace n,
        lam*‖(coordinateEquiv n).symm v‖^2 ≤ v ⬝ᵥ (A y *ᵥ v) ∧
        v ⬝ᵥ (A y *ᵥ v) ≤ Λ*‖(coordinateEquiv n).symm v‖^2) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 →
        ∀ k i j, |matrixCoordinateDerivative A k y i j| ≤ K) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → |f y| ≤ F) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → ∀ k, |coordinateDerivative k f y| ≤ F) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 1 → linearizedMA (A y) u y = f y) →
      ∀ i, |coordinateDerivative i u 0| ≤ C*(U+F) := by
  obtain ⟨C,hC,hgrad⟩ := exists_positive_solution_gradient_bound (n := n) hlam hΛ hK
    (show 0 ≤ (1:ℝ) by norm_num)
  refine ⟨2*C,by positivity,?_⟩
  intro u f A U F hU hF hu hf hAd hub hA hEll hDA hfb hDfb hP i
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/C
  have hδ : 0 < δ := div_pos hε hC
  let v := fun y => u y+(U+F+δ)
  have hv : ContDiff ℝ ∞ v := hu.add contDiff_const
  have hvp (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y‖ < 2) : 0 < v y := by
    have hh := (abs_le.mp (hub y hy)).1
    dsimp only [v]
    linarith
  have hFv (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y‖ < 1) : F ≤ v y := by
    have hh := (abs_le.mp (hub y (by linarith))).1
    dsimp only [v]
    linarith
  have hvP (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y‖ < 1) : linearizedMA (A y) v y=f y := by
    rw [linearizedMA_add_at _ (contDiff_infty.mp hu 2).contDiffAt contDiffAt_const,
      linearizedMA_const,add_zero]
    exact hP y hy
  have hh := hgrad v f A hv hf hAd hvp hA hEll hDA
    (fun y hy => by simpa only [one_mul] using (hfb y hy).trans (hFv y hy))
    (fun y hy k => by simpa only [one_mul] using (hDfb y hy k).trans (hFv y hy)) hvP i
  have he : coordinateDerivative i v 0=coordinateDerivative i u 0 := by
    simp only [coordinateDerivative,v,fderiv_add_const]
  rw [he] at hh
  have hzero := (abs_le.mp (hub 0 (by simp))).2
  have hCδ : C*δ=ε := mul_div_cancel₀ ε hC.ne'
  dsimp only [v] at hh
  nlinarith

end GaussianTilt.MomentMapRegularity
