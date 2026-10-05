import GaussianTilt.MomentMapRegularityImprovementUniformQuadratics
import GaussianTilt.MomentMapCampanatoLocalEndpoint

/-! # Genuine C²,α from the constructed all-radius quadratic approximations -/
noncomputable section
open Set InnerProductSpace
open scoped ContDiff Gradient
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000

lemma secondFrechet_of_gradient_derivative {u : E n → ℝ} {x : E n}
    {H : E n →L[ℝ] E n} (hH : HasFDerivAt (gradient u) H x) :
    fderiv ℝ (fderiv ℝ u) x=(toDual ℝ (E n)).toContinuousLinearEquiv.toContinuousLinearMap.comp H := by
  have hh := (toDual ℝ (E n)).hasFDerivAt.comp x hH
  have he : (fun y=>(toDual ℝ (E n)) (gradient u y))=fderiv ℝ u := by
    funext y
    exact (toDual ℝ (E n)).apply_symm_apply _
  change HasFDerivAt (fun y=>(toDual ℝ (E n)) (gradient u y))
    ((toDual ℝ (E n)).toContinuousLinearEquiv.toContinuousLinearMap.comp H) x at hh
  rw [he] at hh
  exact hh.fderiv

lemma norm_toDual_comp (H : E n →L[ℝ] E n) :
    ‖(toDual ℝ (E n)).toContinuousLinearEquiv.toContinuousLinearMap.comp H‖=‖H‖ := by
  let J := (toDual ℝ (E n)).toContinuousLinearEquiv.toContinuousLinearMap
  have he (v : E n) : ‖(J.comp H) v‖=‖H v‖ := (toDual ℝ (E n)).norm_map _
  apply le_antisymm
  · apply (J.comp H).opNorm_le_bound (norm_nonneg _)
    intro v
    rw [he]
    exact H.le_opNorm v
  · apply H.opNorm_le_bound (norm_nonneg (J.comp H))
    intro v
    rw [← he]
    exact (J.comp H).le_opNorm v

lemma secondFrechet_difference_norm_of_gradient_derivatives {u : E n → ℝ} {x y : E n}
    {H K : E n →L[ℝ] E n} (hH : HasFDerivAt (gradient u) H x) (hK : HasFDerivAt (gradient u) K y) :
    ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖=‖H-K‖ := by
  rw [secondFrechet_of_gradient_derivative hH,secondFrechet_of_gradient_derivative hK,
    ← ContinuousLinearMap.comp_sub,norm_toDual_comp]

/-- All-radius approximations identify both actual derivatives and give a
Hölder modulus for the true second Fréchet derivative, without an existing
source gradient or Hessian premise. -/
theorem contDiffOn_two_of_all_radius_quadratic_approximations {u : E n → ℝ}
    {U : Set (E n)} (hU : IsOpen U) {R C β : ℝ} (hR : 0 < R) (hC : 0≤C) (hβ : 0 < β)
    (happrox : ∀ x∈U, ∀ s : ℝ, 0 < s → s≤R →
      ∃ a : ℝ, ∃ p : E n, ∃ H : E n →L[ℝ] E n,
        (∀ v w, inner ℝ (H v) w=inner ℝ v (H w)) ∧
        ∀ z, ‖z-x‖≤s → |u z-quadraticJet a p x H z|≤C*s^(2+β)) :
    ContDiffOn ℝ 2 u U ∧ ∃ K : ℝ, 0≤K ∧
      ∀ x∈U, ∀ y∈U, 2*‖x-y‖≤R →
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖≤K*‖x-y‖^β := by
  let ρ : ℝ := 1/2
  let q := ρ^β
  have hρ : 0 < ρ := by norm_num [ρ]
  have hρ1 : ρ<1 := by norm_num [ρ]
  have hq : 0 < q := Real.rpow_pos_of_pos hρ _
  have hq1 : q<1 := Real.rpow_lt_one hρ.le hρ1 hβ
  have hcoeff : 0≤C*R^(2+β) := by positivity
  have hgeo : ∀ x∈U, ∃ a : ℕ→ℝ, ∃ p : ℕ→E n, ∃ H : ℕ→E n →L[ℝ] E n,
      (∀ k v w, inner ℝ (H k v) w=inner ℝ v (H k w)) ∧
      ∀ k, ∀ h:E n, ‖h‖≤R*ρ^k →
        |u (x+h)-quadraticJet (a k) (p k) 0 (H k) h|≤(C*R^(2+β))*(ρ^2*q)^k := by
    intro x hx
    have hex (k : ℕ) := happrox x hx (R*ρ^k) (mul_pos hR (pow_pos hρ _))
      (mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1.le))
    choose a p H hsym happ using hex
    refine ⟨a,p,H,hsym,?_⟩
    intro k h hh
    have ht := happ k (x+h) (by simpa only [add_sub_cancel_left] using hh)
    have he : C*(R*ρ^k)^(2+β)=(C*R^(2+β))*(ρ^2*q)^k := by
      rw [Real.mul_rpow hR.le (pow_nonneg hρ.le _),← Real.rpow_pow_comm hρ.le]
      have hp : ρ^(2+β)=ρ^2*q := by rw [Real.rpow_add hρ,Real.rpow_two]
      rw [hp]
      ring
    rw [he] at ht
    simpa only [quadraticJet,add_sub_cancel_left,sub_zero] using ht
  obtain ⟨hreg,H,hH,hholder⟩ := contDiffOn_two_of_geometric_quadratic_approximations_local
    hU hR hρ hρ1 hq hq1 hcoeff hgeo
  have he : oscillationExponent ρ q=β := by
    unfold oscillationExponent q
    rw [Real.log_rpow hρ]
    exact mul_div_cancel_right₀ β (Real.log_neg hρ hρ1).ne
  let K := 4*campanatoLimitConstant R ρ q (C*R^(2+β))*(1+(2:ℝ)^(2+β))
  refine ⟨hreg,max K 0,le_max_right _ _,?_⟩
  intro x hx y hy hxy
  rw [secondFrechet_difference_norm_of_gradient_derivatives (hH x hx) (hH y hy)]
  have hh := hholder x hx y hy hxy
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left K 0) (Real.rpow_nonneg (norm_nonneg _) _))

end GaussianTilt.MomentMapRegularity
