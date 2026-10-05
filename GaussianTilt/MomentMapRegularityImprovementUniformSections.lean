import GaussianTilt.MomentMapRegularityImprovementCoordinateBounds
import GaussianTilt.MomentMapRegularityInteriorUniform

/-! # Uniform centered source-section coordinates from the proved first-order theory -/
noncomputable section
open Set Metric MeasureTheory
open scoped NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def improvementInnerRadius (n : ℕ) (lam Lam : ℝ) : ℝ :=
  sectionBalanceFactor n lam Lam/(2*(1+sectionBalanceFactor n lam Lam))

def improvementOuterRadius (n : ℕ) : ℝ := 6*((n:ℝ)+1)^2

lemma improvementInnerRadius_pos (n : ℕ) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 < Lam) :
    0 < improvementInnerRadius n lam Lam := by
  have hh := sectionBalanceFactor_pos (n:=n) hlam hLam
  unfold improvementInnerRadius
  positivity

/-- For every compact set of source centers, a single positive section
height supplies centered affine normalizations with uniform forward and
inverse bounds. The inverse norm becomes small with the requested physical
section radius. -/
theorem exists_uniform_centered_source_sections [NeZero n]
    {φ : E n → ℝ} {L : ℝ≥0} (hL : LipschitzWith L φ)
    (hc : StrictConvexOn ℝ univ φ) (x₀ : E n) {r ε lam Lam : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεr : ε≤r/2) (hlam : 0 < lam) (hLam : 0 < Lam)
    (hmass : ∀ B : Set (E n), IsCompact B → B⊆closedBall x₀ r →
      ENNReal.ofReal lam*volume B≤volume (subgradientImage φ B) ∧
      volume (subgradientImage φ B)≤ENNReal.ofReal Lam*volume B) :
    ∃ h : ℝ, 0 < h ∧ ∀ x∈closedBall x₀ (r/2), ∀ p, SupportsAt φ p x →
      ∃ T : E n ≃L[ℝ] E n,
        IsCompact (supportSection φ p x h) ∧
        supportSection φ p x h⊆closedBall x ε ∧
        closedBall (0:E n) (improvementInnerRadius n lam Lam)⊆
          interior ((fun y=>T (y-x)) '' supportSection φ p x h) ∧
        (fun y=>T (y-x)) '' supportSection φ p x h⊆closedBall 0 (improvementOuterRadius n) ∧
        ‖(T.symm : E n →L[ℝ] E n)‖≤ε/improvementInnerRadius n lam Lam ∧
        ‖(T : E n →L[ℝ] E n)‖≤ improvementOuterRadius n/(h/(2*(L:ℝ)+1)) := by
  obtain ⟨h₀,hh₀,hsmall⟩ := uniform_small_supportSection_subset_ball hL hc
    (isCompact_closedBall x₀ (r/2)) hε
  let h := h₀/2
  have hh : 0 < h := half_pos hh₀
  have hhsmall : h<h₀ := half_lt_self hh₀
  have hinnerpos := improvementInnerRadius_pos n hlam hLam
  refine ⟨h,hh,?_⟩
  intro x hx p hp
  let S := supportSection φ p x h
  have hS : IsCompact S := isCompact_supportSection_of_strictConvexOn hc hp h
  have hSball : S⊆closedBall x ε := (hsmall x hx p hp h hhsmall).trans ball_subset_closedBall
  have hSK : S⊆closedBall x₀ r := by
    intro y hy
    have hd := dist_triangle y x x₀
    have hyx : dist y x≤ε := hSball hy
    have hxx : dist x x₀≤r/2 := hx
    exact le_trans hd (by linarith)
  have hreflection := supportSection_reflection_balance hc.convexOn hp hh hlam hLam hS
    (fun B hB hBS => hmass B hB (hBS.trans hSK))
  obtain ⟨T,hTin,hTout⟩ := exists_centered_affine_normalization hS (convex_supportSection hc.convexOn p x h)
    (center_mem_interior_supportSection hL.continuous p x hh)
    (sectionBalanceFactor_pos (n:=n) hlam hLam) hreflection
  have hTin' : closedBall (0:E n) (improvementInnerRadius n lam Lam)⊆interior ((fun y=>T (y-x)) '' S) := hTin
  have hTout' : (fun y=>T (y-x)) '' S⊆closedBall 0 (improvementOuterRadius n) := hTout
  have hsourceInner : closedBall x (h/(2*(L:ℝ)+1))⊆S := by
    intro y hy
    have hnorm : ‖y-x‖≤h/(2*(L:ℝ)+1) := hy
    have hden : 0 < 2*(L:ℝ)+1 := by positivity
    have hhbound : (2*(L:ℝ)+1)*‖y-x‖≤h := by
      have ht := (le_div_iff₀ hden).mp hnorm
      nlinarith
    have hres := supportResidual_le_lipschitz hL hp y
    change supportResidual φ p x y≤h
    nlinarith [norm_nonneg (y-x)]
  refine ⟨T,hS,hSball,hTin',hTout',?_,?_⟩
  · exact inverse_coordinate_norm_from_section_balls T hinnerpos hε.le
      (hTin'.trans interior_subset) hSball
  · exact coordinate_norm_from_section_balls T (div_pos hh (by positivity))
      (by unfold improvementOuterRadius; positivity) hsourceInner hTout'

end GaussianTilt.MomentMapRegularity
