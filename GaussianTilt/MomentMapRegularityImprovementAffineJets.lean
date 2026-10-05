import GaussianTilt.MomentMapRegularityImprovementPhysical

/-! # Exact affine pullback of the constructed quadratic approximations -/
noncomputable section
open Set InnerProductSpace
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def affineJetHessian (T : E n ≃L[ℝ] E n) (t : ℝ) (H : E n →L[ℝ] E n) : E n →L[ℝ] E n :=
  t⁻¹ • (T : E n →L[ℝ] E n).adjoint.comp (H.comp (T : E n →L[ℝ] E n))

def affineJetGradient (T : E n ≃L[ℝ] E n) (t : ℝ) (p q : E n) : E n :=
  p+t⁻¹ • (T : E n →L[ℝ] E n).adjoint q

lemma affineJetHessian_symmetric (T : E n ≃L[ℝ] E n) (t : ℝ) {H : E n →L[ℝ] E n}
    (hH : ∀ v w, inner ℝ (H v) w=inner ℝ v (H w)) :
    ∀ v w, inner ℝ (affineJetHessian T t H v) w=inner ℝ v (affineJetHessian T t H w) := by
  intro v w
  simp only [affineJetHessian,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    real_inner_smul_left,real_inner_smul_right,ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right,hH]

lemma affinePotential_quadratic_difference (φ : E n → ℝ) (T : E n ≃L[ℝ] E n)
    (a p q : E n) (b c t : ℝ) (ht : t≠0) (H : E n →L[ℝ] E n) (z : E n) :
    φ z-quadraticJet (b+inner ℝ p a+c/t) (affineJetGradient T t p q) a (affineJetHessian T t H) z =
      (t*affinePotential φ T a p b (T (z-a))-quadraticJet c q 0 H (T (z-a)))/t := by
  have he : affineSource T a (T (z-a))=z := by simp [affineSource]
  simp only [affinePotential,he]
  simp only [quadraticJet,sub_zero,affineJetGradient,affineJetHessian,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,inner_add_left,
    real_inner_smul_left,real_inner_smul_right,ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearEquiv.coe_apply,map_sub,inner_sub_left,inner_sub_right]
  field_simp
  ring

/-- Actual all-radius quadratic approximations survive an arbitrary affine
source normalization with the quantitatively correct radius and remainder
constant. The pulled Hessians remain symmetric by actual congruence. -/
theorem affine_quadratic_approximations_pullback {φ : E n → ℝ}
    (T : E n ≃L[ℝ] E n) (a p : E n) (b : ℝ) {t B R C β : ℝ}
    (ht : 0 < t) (hB : 0 < B) (hC : 0≤C) (hT : ‖(T : E n →L[ℝ] E n)‖≤B)
    (happrox : ∀ s : ℝ, 0 < s → s≤R →
      ∃ c : ℝ, ∃ q : E n, ∃ H : E n →L[ℝ] E n,
        (∀ v w, inner ℝ (H v) w=inner ℝ v (H w)) ∧
        ∀ y, ‖y‖≤s → |t*affinePotential φ T a p b y-quadraticJet c q 0 H y|≤C*s^(2+β)) :
    ∀ s : ℝ, 0 < s → s≤R/B →
      ∃ c : ℝ, ∃ q : E n, ∃ H : E n →L[ℝ] E n,
        (∀ v w, inner ℝ (H v) w=inner ℝ v (H w)) ∧
        ∀ z, ‖z-a‖≤s → |φ z-quadraticJet c q a H z|≤(C*B^(2+β)/t)*s^(2+β) := by
  intro s hs hsR
  have hBR : B*s≤R := by have hh := (le_div_iff₀ hB).mp hsR; nlinarith
  obtain ⟨c,q,H,hH,herr⟩ := happrox (B*s) (mul_pos hB hs) hBR
  refine ⟨b+inner ℝ p a+c/t,affineJetGradient T t p q,affineJetHessian T t H,
    affineJetHessian_symmetric T t hH,?_⟩
  intro z hz
  have hn := ((T : E n →L[ℝ] E n).le_opNorm (z-a)).trans
    ((mul_le_mul_of_nonneg_right hT (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left hz hB.le))
  rw [affinePotential_quadratic_difference φ T a p q b c t ht.ne' H z,abs_div,abs_of_pos ht]
  have hh := div_le_div_of_nonneg_right (herr _ hn) ht.le
  rw [Real.mul_rpow hB.le hs.le] at hh
  convert hh using 1 <;> ring

end GaussianTilt.MomentMapRegularity
