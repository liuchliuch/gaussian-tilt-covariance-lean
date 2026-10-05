import GaussianTilt.MomentMapRegularityImprovementUniformSeeds
import GaussianTilt.MomentMapRegularityImprovementAllRadii
import GaussianTilt.MomentMapRegularityImprovementInitialRadius
import GaussianTilt.MomentMapRegularityImprovementAffineComposition

/-! # Uniform quadratic approximations of the actual original weak source -/
noncomputable section
open Set Metric MeasureTheory
open scoped NNReal ENNReal ContDiff
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 1000

 theorem uniform_quadratic_approximations_of_classical_references [NeZero n]
    {φ f : E n → ℝ} {Lip : ℝ≥0} (hLip : LipschitzWith Lip φ)
    (hc : StrictConvexOn ℝ univ φ) (hfc : Continuous f)
    (hMA : ∀ A, IsCompact A → volume (subgradientImage φ A)=
      (volume.withDensity (fun y=>ENNReal.ofReal (f y))) A)
    (href : ∀ S : Set (E n), IsCompact S → Convex ℝ S → (interior S).Nonempty →
      ∃ w : E n → ℝ, Continuous w ∧ ContDiffOn ℝ ∞ w (interior S) ∧ ConvexOn ℝ S w ∧
        (∀ y∈frontier S, w y=0) ∧
        ∀ A, IsCompact A → A⊆interior S → volume (subgradientImageOn S w A)=volume A)
    (x₀ : E n) {r m M F α : ℝ} (hr : 0 < r) (hm : 0 < m) (hM : 0 < M)
    (hF : 0≤F) (hα : 0 < α) (hα1 : α≤1)
    (hfrange : ∀ y∈closedBall x₀ r, m≤f y ∧ f y≤M)
    (hfHolder : ∀ y∈closedBall x₀ r, ∀ z∈closedBall x₀ r, |f y-f z|≤F*‖y-z‖^α) :
    ∃ s₀ C₀ : ℝ, 0 < s₀ ∧ 0≤C₀ ∧ ∀ x∈closedBall x₀ (r/2), ∀ s : ℝ, 0 < s → s≤s₀ →
      ∃ a : ℝ, ∃ p : E n, ∃ H : E n →L[ℝ] E n,
        (∀ v w, inner ℝ (H v) w=inner ℝ v (H w)) ∧
        ∀ z, ‖z-x‖≤s → |φ z-quadraticJet a p x H z|≤C₀*s^(2+improvementRemainderExponent α) := by
  let c := improvementScaleExponent α
  let γ := c/(1+c)
  let d := γ/3
  let β := improvementRemainderExponent α
  obtain ⟨hcp,hγp,hdp,hγα,hαc,hscale,hγd⟩ := improvement_numeric_exponents hα hα1
  obtain ⟨_,hβ,hβ1,hgapD,hgapT⟩ := improvement_exponents hα hα1
  let C := improvementReferenceConstant n
  have hC : 0≤C := referenceTaylorConstant_nonneg _ _ _
  let B : ℝ := 2^α+1
  have hB : 0 < B := by dsimp [B]; positivity
  let A := B+8*C+1
  have hA : 0 < A := by dsimp [A]; positivity
  let K := 4*(A+B/2+C)
  obtain ⟨R,hR,hR1,hsmallσ,hsmallδ,hsmallr,hsmallθ,hsmallρ,hbudget⟩ :=
    exists_improvement_initial_radius (A:=A) (B:=B) (K:=K) hα hcp hγp hdp
  obtain ⟨ρ,h,hρ,hh,hSeeds⟩ := exists_uniform_recurrence_seeds hLip hc hfc hMA href x₀
    hr hm hM hF hα hR (mul_pos hA (Real.rpow_pos_of_pos hR γ)) hfrange hfHolder
  let rin := improvementInnerRadius n m M
  let rout := improvementOuterRadius n
  let ML := initialForwardNormalizationBound n rin rout
  let BT := rout/(h/(2*(Lip:ℝ)+1))
  let σ := ρ/R
  let Q := σ⁻¹*ML*BT
  let CN := B/2+8*C
  have hrin : 0 < rin := improvementInnerRadius_pos n hm hM
  have hML : 0 < ML := (by norm_num : (0:ℝ)<1).trans_le (le_max_right _ _)
  have hrout : 0 < rout := by dsimp [rout,improvementOuterRadius]; positivity
  have hBT : 0 < BT := by dsimp [BT]; positivity
  have hσ : 0 < σ := div_pos hρ hR
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hCN : 0≤CN := by dsimp [CN]; positivity
  obtain ⟨Amp,hAmp,hAmpbound⟩ := exists_uniform_inverse_amplitude_bound (n:=n) (1/rin) M
  let s₀ := (adaptiveRadius R c 1)/Q
  let C₀ := CN*Q^(2+β)*σ^2*Amp
  refine ⟨s₀,C₀,div_pos (adaptiveRadius_pos hR 1) hQ,by dsimp [C₀]; positivity,?_⟩
  intro x hx s hs hss
  obtain ⟨p,q,T,L,hLdet,hT,hTi,hLi,hUc,hUconv,hgc,hUMA,hgHolder,hseed⟩ := hSeeds x hx
  let U := recurrenceSeedPotential φ f T L x p q h ρ R
  let g := recurrenceSeedDensity f T L x ρ R
  have happrox := quadratic_approximations_at_all_small_radii hUc hUconv hgc hUMA href
    hR hR1 hα hcp hγp hdp hγα hαc hscale hγd (by norm_num : (0:ℝ)≤1) hB
    (by dsimp [B]; linarith : (1:ℝ)*2^α≤B)
    (by dsimp [A]; linarith : B+8*improvementReferenceConstant n≤A) (rfl : K=4*(A+B/2+improvementReferenceConstant n))
    hsmallσ hsmallδ hsmallr hsmallθ hsmallρ hbudget (by simpa only [one_mul] using hgHolder)
    hβ hβ1 hgapD hgapT hseed
  have hxK : x∈closedBall x₀ r := closedBall_subset_closedBall (half_le_self hr.le) hx
  have hfx : 0 < f x := hm.trans_le (hfrange x hxK).1
  let t := densityNormalizationFactor n (|(T.symm : E n →L[ℝ] E n).det|^2*f x)
  have ht : 0 < t := densityNormalizationFactor_pos
    (mul_pos (sq_pos_of_pos (abs_pos.mpr T.symm.toLinearEquiv.isUnit_det'.ne_zero)) hfx)
  let e := rescaleAffineCoordinate T L hσ.ne'
  let p' := rescaleAffinePlane T t p q
  let b' := φ x-inner ℝ p' x
  have he : U=(fun y=>(t/σ^2)*affinePotential φ e x p' b' y) := by
    exact improvementRescale_affine_vertical φ T L x p q (φ x-inner ℝ p x+h) t ht.ne' hσ.ne'
  have henorm : ‖(e : E n →L[ℝ] E n)‖≤Q :=
    rescaleAffineCoordinate_norm_bound T L hσ hBT.le hML.le hT hLi
  have hnormalized : ∀ s:ℝ, 0 < s → s≤adaptiveRadius R c 1 →
      ∃ a : ℝ, ∃ q : E n, ∃ H : E n →L[ℝ] E n,
        (∀ v w, inner ℝ (H v) w=inner ℝ v (H w)) ∧
        ∀ y, ‖y‖≤s → |(t/σ^2)*affinePotential φ e x p' b' y-quadraticJet a q 0 H y|≤CN*s^(2+β) := by
    have happrox' : ∀ s:ℝ, 0 < s → s≤adaptiveRadius R c 1 →
      ∃ a : ℝ, ∃ q : E n, ∃ H : E n →L[ℝ] E n,
        (∀ v w, inner ℝ (H v) w=inner ℝ v (H w)) ∧
        ∀ y, ‖y‖≤s → |U y-quadraticJet a q 0 H y|≤CN*s^(2+β) := happrox
    rw [he] at happrox'
    exact happrox'
  obtain ⟨a,q',H,hH,herr⟩ := affine_quadratic_approximations_pullback e x p' b'
    (div_pos ht (sq_pos_of_pos hσ)) hQ hCN henorm hnormalized s hs hss
  have htbound : t⁻¹≤Amp := hAmpbound (T.symm : E n →L[ℝ] E n) hTi (f x) hfx.le (hfrange x hxK).2
  have hfactor : CN*Q^(2+β)/(t/σ^2)≤C₀ := by
    have heq : CN*Q^(2+β)/(t/σ^2)=(CN*Q^(2+β)*σ^2)*t⁻¹ := by field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left htbound (by positivity)
  refine ⟨a,q',H,hH,?_⟩
  intro z hz
  exact (herr z hz).trans (mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hs.le _))

end GaussianTilt.MomentMapRegularity
