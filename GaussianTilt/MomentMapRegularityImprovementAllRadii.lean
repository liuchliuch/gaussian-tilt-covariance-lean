import GaussianTilt.MomentMapRegularityImprovementIteration
import GaussianTilt.MomentMapRegularityImprovementStageTaylor

/-! # All-radius quadratic approximation from the actual adaptive iteration -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000

theorem quadratic_approximations_at_all_small_radii [NeZero n] {U f : E n → ℝ}
    (hUc : Continuous U) (hUconv : ConvexOn ℝ univ U) (hfc : Continuous f)
    (hMA : ∀ A, IsCompact A → volume (subgradientImage U A)=
      (volume.withDensity (fun x=>ENNReal.ofReal (f x))) A)
    (href : ∀ S : Set (E n), IsCompact S → Convex ℝ S → (interior S).Nonempty →
      ∃ w : E n → ℝ, Continuous w ∧ ContDiffOn ℝ ∞ w (interior S) ∧ ConvexOn ℝ S w ∧
        (∀ y∈frontier S, w y=0) ∧
        ∀ A, IsCompact A → A⊆interior S → volume (subgradientImageOn S w A)=volume A)
    {R₀ α c γ d A B F K : ℝ}
    (hR : 0 < R₀) (hR1 : R₀<1) (hα : 0 < α) (hc : 0 < c) (hγ : 0 < γ) (hd : 0 < d)
    (hγα : γ≤α) (hαc : 3*c≤α) (hscale : (1+c)*γ=c) (hγd : γ=3*d)
    (hF : 0≤F) (hB : 0 < B) (hFB : F*2^α≤B)
    (hA : B+8*improvementReferenceConstant n≤A)
    (hK : K=4*(A+B/2+improvementReferenceConstant n))
    (hsmallσ : A*R₀^γ≤1/16) (hsmallδ : B*R₀^α<1)
    (hsmallr : R₀^d≤1/8) (hsmallθ : K*R₀^d≤1/2) (hsmallρ : R₀^c≤1/16)
    (hbudget : 2*K*R₀^d/(1-R₀^(c*d))≤Real.log 2)
    (hHolder : ∀ y, ‖y‖≤2*R₀ → |f y-1|≤F*‖y‖^α)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β≤1)
    (hgapD : (1+c)^2*(2+β)≤2+α) (hgapT : 1≤(1+c)*(1-β))
    (hseed : ∀ x, ‖x‖≤1 →
      |improvementRescale U 0 (ContinuousLinearMap.id ℝ (E n)) R₀ x-‖x‖^2/2|≤A*R₀^γ) :
    ∀ s : ℝ, 0 < s → s≤adaptiveRadius R₀ c 1 →
      ∃ a : ℝ, ∃ p : E n, ∃ H : E n →L[ℝ] E n,
        (∀ v w, inner ℝ (H v) w=inner ℝ v (H w)) ∧
        ∀ x, ‖x‖≤s → |U x-quadraticJet a p 0 H x|≤
          (B/2+8*improvementReferenceConstant n)*s^(2+β) := by
  have hC : 0 ≤ improvementReferenceConstant n := referenceTaylorConstant_nonneg _ _ _
  have hA0 : 0≤A := by linarith
  have hK0 : 0≤K := by rw [hK]; positivity
  have hstages := exists_improvement_stages hUc hUconv hfc hMA href hR hR1 hα hc hγ hd
    hγα hαc hscale hγd hF hB hFB hA hK hsmallσ hsmallδ hsmallr hsmallθ hsmallρ hbudget hHolder hseed
  intro s hs hsR
  obtain ⟨k,hlo,hhi⟩ := exists_adaptiveRadius_gap hR hR1 hc hs hsR
  obtain ⟨P,b,hPdet,hPn,hPin,hnear⟩ := hstages k
  let R := adaptiveRadius R₀ c k
  have hRp : 0 < R := adaptiveRadius_pos hR k
  have hRR : R≤R₀ := adaptiveRadius_le_initial hR hR1.le hc.le k
  have hRone : R≤1 := hRR.trans hR1.le
  have hpow (e : ℝ) (he : 0≤e) : R^e≤R₀^e := Real.rpow_le_rpow hRp.le hRR he
  have hnorm := improvementDistortionBudget_exp_le_two hR hR1 hc hd hK0 hbudget k
  have hδ1 : B*R^α<1 := (mul_le_mul_of_nonneg_left (hpow α hα.le) hB.le).trans_lt hsmallδ
  have hσsmall : A*R^γ≤1/16 := (mul_le_mul_of_nonneg_left (hpow γ hγ.le) hA0).trans hsmallσ
  obtain ⟨a,p,H,hH,happrox⟩ := physical_reference_approximation_of_stage hUc hUconv hfc hMA href P b
    hRp hRR hα hF hB hFB hδ1 hσsmall hPdet (hPn.trans hnorm) (hPin.trans hnorm) hHolder hnear
  have hupper : s≤R^(1+c) := hhi
  have hlower : R^((1+c)^2)≤s := by
    rw [← adaptiveRadius_two_step hR k]
    exact hlo.le
  have hsbound : s≤R/16 := by
    have hp : R^c≤1/16 := (hpow c hc.le).trans hsmallρ
    have he : R^(1+c)=R*R^c := by rw [Real.rpow_add hRp,Real.rpow_one]
    rw [he] at hupper
    nlinarith
  have hgap := adaptive_gap_remainder_bound hRp hRone hs hc.le hβ.le hβ1
    (by positivity : 0≤B/2) (by positivity : 0≤8*improvementReferenceConstant n)
    hlower hupper hgapD hgapT
  refine ⟨a,p,H,hH,?_⟩
  intro x hx
  apply (happrox x (hx.trans hsbound)).trans
  apply le_trans _ hgap
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 3)
    (by positivity : 0≤8*improvementReferenceConstant n)
  exact add_le_add_left (div_le_div_of_nonneg_right hh hRp.le) _

end GaussianTilt.MomentMapRegularity
