import GaussianTilt.MomentMapSchauderSmallOscillation
import GaussianTilt.MomentMapSchauderCutoffInitialHolder
import GaussianTilt.MomentMapSchauderLocalization

/-! # An actual interior Schauder estimate with lower-order C¹,α data

This form is tailored to source difference quotients: their lower-order
norms are already step-uniform by FTC. Every initial second-derivative
bound is absorbed, including a possible reciprocal-step loss.
-/
noncomputable section
open Matrix Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- A genuine local a-priori estimate with explicit cutoff errors. The
constants are chosen before the coefficient field, function, and initial
Hessian modulus. The latter does not appear in the conclusion. -/
theorem exists_localized_small_oscillation_schauder [NeZero n]
    {α lam Λ K : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ A₀ : Matrix (Fin n) (Fin n) ℝ, A₀.PosDef →
      (∀ v : KernelSpace n, lam*‖v‖^2 ≤ euclideanQuadratic A₀ v) →
      (∀ v : KernelSpace n, euclideanQuadratic A₀ v ≤ Λ*‖v‖^2) →
      ∀ A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ,
      (∀ x, (A x).IsSymm) → (∀ x i j, |A₀ i j-A x i j| ≤ ε) →
      (∀ x y i j, |A x i j-A y i j| ≤ K*‖x-y‖^α) →
      ∀ χ u f : KernelSpace n → ℝ, ContDiff ℝ 2 u → ContDiff ℝ 2 χ → HasCompactSupport χ →
      ∀ S T : Set (KernelSpace n), IsOpen T → tsupport χ ⊆ S → (∀ x ∈ T, χ x=1) →
      ∀ M C₀ C₁ C₂ L₀ L₁ L₂ U D J HU HD HJ F H : ℝ,
      0 ≤ M → 0 ≤ C₀ → 0 ≤ C₁ → 0 ≤ C₂ → 0 ≤ L₀ → 0 ≤ L₁ → 0 ≤ L₂ →
      0 ≤ U → 0 ≤ D → 0 ≤ J → 0 ≤ HU → 0 ≤ HD → 0 ≤ HJ → 0 ≤ F → 0 ≤ H →
      (∀ x i j, |A x i j| ≤ M) →
      (∀ x, |χ x| ≤ C₀) → (∀ x, ‖fderiv ℝ χ x‖ ≤ C₁) →
      (∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ C₂) →
      (∀ x y, |χ x-χ y| ≤ L₀*‖x-y‖^α) →
      (∀ x y, ‖fderiv ℝ χ x-fderiv ℝ χ y‖ ≤ L₁*‖x-y‖^α) →
      (∀ x y, ‖fderiv ℝ (fderiv ℝ χ) x-fderiv ℝ (fderiv ℝ χ) y‖ ≤ L₂*‖x-y‖^α) →
      (∀ x ∈ S, |u x| ≤ U) → (∀ x ∈ S, ‖fderiv ℝ u x‖ ≤ D) →
      (∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ J) →
      (∀ x ∈ S, ∀ y ∈ S, |u x-u y| ≤ HU*‖x-y‖^α) →
      (∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ u x-fderiv ℝ u y‖ ≤ HD*‖x-y‖^α) →
      (∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ HJ*‖x-y‖^α) →
      (∀ x ∈ S, |f x| ≤ F) →
      (∀ x ∈ S, ∀ y ∈ S, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ S, euclideanEllipticOperator (A x) u x=f x) →
      let R := C₂*U+2*(C₁*D)
      let HR := C₂*HU+U*L₂+2*(C₁*HD+D*L₁)
      let B := C*(C₀*U+(C₀*F+(n : ℝ)^2*M*R)+
        (C₀*H+F*L₀+(n : ℝ)^2*(M*HR+K*R)))
      (∀ x ∈ T, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B) ∧
      (∀ x ∈ T, ∀ y ∈ T, ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ B*‖x-y‖^α) := by
  obtain ⟨ε, C, hε, hC, hbase⟩ := exists_small_oscillation_schauder (n := n) hα hα1 hlam hΛ hK
  refine ⟨ε, C, hε, hC, ?_⟩
  intro A₀ hA₀ hlower hupper A hAs hAc hAH χ u f hu hχ hχc S T hT hs hone
    M C₀ C₁ C₂ L₀ L₁ L₂ U D J HU HD HJ F H
    hM hC₀ hC₁ hC₂ hL₀ hL₁ hL₂ hU hD hJ hHU hHD hHJ hF hH
    hAb hχb hχ₁ hχ₂ hχH₀ hχH₁ hχH₂ hub hDu hD2u huH hDuH hD2uH hfb hfH heq
  dsimp only
  have hrem := euclideanCutoffRemainder_bounds hC₁ hC₂ hL₁ hL₂ hU hD hHU hHD
    hs hχ₁ hχ₂ hχH₁ hχH₂ hub hDu huH hDuH
  have hforce := euclidean_cutoff_forcing_bounds hu hχ hM hK hC₀ hL₀ hF hH
    (by positivity) (by positivity) hAs hs hAb hAH hχb hχH₀ hfb hfH heq hrem.1 hrem.2
  have hinit : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ x y,
      ‖fderiv ℝ (fderiv ℝ (fun z => χ z*u z)) x-fderiv ℝ (fderiv ℝ (fun z => χ z*u z)) y‖ ≤ Q*‖x-y‖^α := by
    refine ⟨(n : ℝ)^2*(C₀*HJ+J*L₀+C₂*HU+U*L₂+2*(C₁*HD+D*L₁)), by positivity, ?_⟩
    exact localized_secondFrechet_holder hu hχ hC₀ hC₁ hC₂ hL₀ hL₁ hL₂ hU hD hJ hHU hHD hHJ
      hs hχb hχ₁ hχ₂ hχH₀ hχH₁ hχH₂ hub hDu hD2u huH hDuH hD2uH
  have hvb : ∀ x, |χ x*u x| ≤ C₀*U := by
    intro x
    by_cases hx : x ∈ S
    · rw [abs_mul]; exact mul_le_mul (hχb x) (hub x hx) (abs_nonneg _) hC₀
    · rw [(cutoff_jets_zero_off hs hx).1, zero_mul, abs_zero]; positivity
  have hb := hbase A₀ hA₀ hlower hupper A hAc hAH (fun x => χ x*u x)
    (hχ.mul hu) hχc.mul_right hinit (C₀*U)
    (C₀*F+(n : ℝ)^2*M*(C₂*U+2*(C₁*D)))
    (C₀*H+F*L₀+(n : ℝ)^2*(M*(C₂*HU+U*L₂+2*(C₁*HD+D*L₁))+K*(C₂*U+2*(C₁*D))))
    (by positivity) (by positivity) (by positivity) hvb hforce.1 hforce.2
  constructor
  · intro x hx
    simpa only [(cutoff_mul_derivatives_eq (u := u) hT hone hx).2.2] using hb.1 x
  · intro x hx y hy
    simpa only [(cutoff_mul_derivatives_eq (u := u) hT hone hx).2.2,
      (cutoff_mul_derivatives_eq (u := u) hT hone hy).2.2] using hb.2 x y

end GaussianTilt.MomentMapSchauder
