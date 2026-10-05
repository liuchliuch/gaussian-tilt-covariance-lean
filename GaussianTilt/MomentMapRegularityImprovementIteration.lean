import GaussianTilt.MomentMapRegularityImprovementSectionStep
import GaussianTilt.MomentMapRegularityImprovementBudget

/-! # Actual affine improvement iteration on rough Alexandrov sources

The only reference input is classical Dirichlet existence, kept explicit
until its independent analytic construction is complete. Every section,
normalization, affine distortion and source approximation in the recurrence
is derived from the literal source data.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000

 theorem exists_improvement_stages [NeZero n] {U f : E n → ℝ}
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
    (hseed : ∀ x, ‖x‖≤1 →
      |improvementRescale U 0 (ContinuousLinearMap.id ℝ (E n)) R₀ x-‖x‖^2/2|≤A*R₀^γ) :
    ∀ k : ℕ, ∃ P : E n ≃L[ℝ] E n, ∃ b : E n,
      (P : E n →L[ℝ] E n).det=1 ∧
      ‖(P : E n →L[ℝ] E n)‖≤Real.exp (improvementDistortionBudget R₀ c d K k) ∧
      ‖(P.symm : E n →L[ℝ] E n)‖≤Real.exp (improvementDistortionBudget R₀ c d K k) ∧
      ∀ x, ‖x‖≤1 →
        |improvementRescale U b P (adaptiveRadius R₀ c k) x-‖x‖^2/2|≤
          A*(adaptiveRadius R₀ c k)^γ := by
  have hC : 0 ≤ improvementReferenceConstant n := referenceTaylorConstant_nonneg _ _ _
  have hA0 : 0≤A := by linarith
  have hK0 : 0≤K := by rw [hK]; positivity
  intro k
  induction k with
  | zero =>
    refine ⟨ContinuousLinearEquiv.refl ℝ (E n),0,?_,?_,?_,?_⟩
    · exact map_one _
    · simpa using (ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=E n))
    · simpa using (ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=E n))
    · exact hseed
  | succ k ih =>
    obtain ⟨P,b,hPdet,hPn,hPin,hnear⟩ := ih
    let R := adaptiveRadius R₀ c k
    let u := improvementRescale U b P R
    let g : E n → ℝ := fun x=>f (R • P x)
    have hRp : 0 < R := adaptiveRadius_pos hR k
    have hRR : R≤R₀ := adaptiveRadius_le_initial hR hR1.le hc.le k
    have hRone : R≤1 := hRR.trans hR1.le
    have hpow (e : ℝ) (he : 0≤e) : R^e≤R₀^e := Real.rpow_le_rpow hRp.le hRR he
    have hPtwo : ‖(P : E n →L[ℝ] E n)‖≤2 := hPn.trans
      (improvementDistortionBudget_exp_le_two hR hR1 hc hd hK0 hbudget k)
    have huc : Continuous u := improvementRescale_continuous hUc b P R
    have huconv : ConvexOn ℝ univ u := improvementRescale_convex hUconv b P R
    have hu0 : u 0=0 := improvementRescale_zero U b P R
    have hgc : Continuous g := by dsimp [g]; fun_prop
    have hσ : 0≤A*R^γ := mul_nonneg hA0 (Real.rpow_nonneg hRp.le _)
    have hσsmall : A*R^γ≤1/16 := (mul_le_mul_of_nonneg_left (hpow γ hγ.le) hA0).trans hsmallσ
    have hδp : 0 < B*R^α := mul_pos hB (Real.rpow_pos_of_pos hRp _)
    have hδ1 : B*R^α<1 := (mul_le_mul_of_nonneg_left (hpow α hα.le) hB.le).trans_lt hsmallδ
    have hθ0 : 0≤K*R^d := mul_nonneg hK0 (Real.rpow_nonneg hRp.le _)
    have hθhalf : K*R^d≤1/2 := (mul_le_mul_of_nonneg_left (hpow d hd.le) hK0).trans hsmallθ
    have hρp : 0 < R^c := Real.rpow_pos_of_pos hRp _
    have hregion : R^c*(1+2*(K*R^d))≤1/8 := by
      have hh : R^c≤1/16 := (hpow c hc.le).trans hsmallρ
      nlinarith
    have hrp : 0 < R^d := Real.rpow_pos_of_pos hRp _
    have hrsmall : R^d≤1/8 := (hpow d hd.le).trans hsmallr
    have hcoef : 4*(A*R^γ+(B*R^α)/2)/(R^d)^2+4*improvementReferenceConstant n*R^d≤K*R^d := by
      rw [hK]
      exact improvement_coefficient_budget hRp hRone hγα hγd hA0 hB.le hC
    have hshape := near_quadratic_section_geometry huc huconv hu0 (ρ:=1/2) (η:=1/2)
      (R:=1) (ε:=A*R^γ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num; exact hσsmall) hnear
    have hS : IsCompact (improvementSection u) := by
      convert hshape.1 using 1 <;> norm_num [improvementSection]
    have hSconv : Convex ℝ (improvementSection u) := by
      convert hshape.2.1 using 1 <;> norm_num [improvementSection]
    have hSinner : Metric.closedBall (0:E n) (1/4)⊆interior (improvementSection u) := by
      have hh := near_quadratic_section_contains_closedBall_interior huc (ρ:=1/2) (η:=1/2)
        (R:=1) (ε:=A*R^γ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num; exact hσsmall) hnear
      convert hh using 1 <;> norm_num [improvementSection]
    have hSouter : improvementSection u⊆Metric.ball (0:E n) 1 := by
      have hh := hshape.2.2.2.1
      norm_num at hh
      exact hh.trans (Metric.ball_subset_ball (by norm_num))
    have hgδ : ∀ x∈interior (improvementSection u), |g x-1|≤B*R^α := by
      intro x hx
      have hxnorm : ‖x‖≤1 := le_of_lt (by simpa using hSouter (interior_subset hx))
      have hnorm : ‖R • P x‖≤2*R := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hRp]
        have hh := ((P : E n →L[ℝ] E n).le_opNorm x).trans
          ((mul_le_mul_of_nonneg_right hPtwo (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left hxnorm (by norm_num)))
        simp only [ContinuousLinearEquiv.coe_apply] at hh
        nlinarith
      have hh := hHolder (R • P x) (hnorm.trans (by linarith))
      apply hh.trans
      calc
        F*‖R • P x‖^α ≤ F*(2*R)^α := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hnorm hα.le) hF
        _ = (F*2^α)*R^α := by rw [Real.mul_rpow (by norm_num) hRp.le]; ring
        _ ≤ B*R^α := mul_le_mul_of_nonneg_right hFB (Real.rpow_nonneg hRp.le _)
    have huMA : ∀ Q, IsCompact Q → Q⊆interior (improvementSection u) →
        volume (subgradientImage u Q)=(volume.withDensity (fun x=>ENNReal.ofReal (g x))) Q := by
      intro Q hQ _
      rw [withDensity_apply _ hQ.measurableSet]
      apply alexandrov_density_improvementRescale P hPdet b hRp hQ
      have himage : IsCompact ((fun x:E n=>R • P x) '' Q) := hQ.image (by fun_prop)
      rw [hMA _ himage,withDensity_apply _ himage.measurableSet]
    obtain ⟨w,hwc,hw,hwconv,hwb,hwMA⟩ := href (improvementSection u) hS hSconv
      ⟨0,hSinner (by simp)⟩
    obtain ⟨p,L,hLdet,hLn,hLin,_,_,_,herr⟩ := near_quadratic_source_reference_step
      huc huconv hu0 hgc hσ hσsmall hδp hδ1 hrp hrsmall hρp hθ0 hθhalf hcoef hregion
      hnear hgδ huMA hwc hw hwconv hwb hwMA
    have hRnext : adaptiveRadius R₀ c (k+1)=R*R^c := by
      rw [adaptiveRadius,Real.rpow_add hRp,Real.rpow_one]
    have heq : improvementRescale u p L (R^c)=
        improvementRescale U (improvementPlaneUpdate P R b p) (L.trans P) (adaptiveRadius R₀ c (k+1)) := by
      rw [hRnext]
      exact improvementRescale_comp U b p P L hRp.ne' hρp.ne'
    refine ⟨L.trans P,improvementPlaneUpdate P R b p,?_,?_,?_,?_⟩
    · change ((P : E n →L[ℝ] E n)*(L : E n →L[ℝ] E n)).det=1
      change LinearMap.det ((P : E n →ₗ[ℝ] E n).comp (L : E n →ₗ[ℝ] E n))=1
      rw [LinearMap.det_comp]
      change (P : E n →L[ℝ] E n).det*(L : E n →L[ℝ] E n).det=1
      rw [hPdet,hLdet,mul_one]
    · have hh := norm_le_exp_of_sub_identity_le (L : E n →L[ℝ] E n) hLn
      change ‖(P : E n →L[ℝ] E n)*(L : E n →L[ℝ] E n)‖≤_
      apply (norm_mul_le _ _).trans
      have hp := mul_le_mul hPn hh (norm_nonneg _) (Real.exp_pos _).le
      rw [← Real.exp_add] at hp
      simpa only [improvementDistortionBudget_succ,mul_assoc] using hp
    · have hh := norm_le_exp_of_sub_identity_le (L.symm : E n →L[ℝ] E n)
        (hLin.trans (show K*R^d≤2*(K*R^d) by nlinarith))
      change ‖(L.symm : E n →L[ℝ] E n)*(P.symm : E n →L[ℝ] E n)‖≤_
      apply (norm_mul_le _ _).trans
      have hp := mul_le_mul hh hPin (norm_nonneg _) (Real.exp_pos _).le
      rw [← Real.exp_add] at hp
      simpa only [improvementDistortionBudget_succ,mul_assoc,add_comm] using hp
    · intro x hx
      rw [← heq]
      exact (herr x hx).trans (improvement_next_error_budget hRp hRone hαc hscale hB.le hC hθ0 hθhalf hA)

end GaussianTilt.MomentMapRegularity
