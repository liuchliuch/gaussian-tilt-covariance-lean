import GaussianTilt.MomentMapLinearDirichletVariableEnergy

/-! # The genuine variable-coefficient weak inverse for arbitrary bounded loads -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Riesz and the proved coercive energy construct the actual solution of
any bounded load, including scalar forcing and divergence-form forcing. -/
def variableWeakSolution {Ω : Set (CoordinateSpace n)} (i : Fin n) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K lam : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K) (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, ∀ z : Fin n → ℝ, lam * (∑ i, (z i)^2) ≤ z ⬝ᵥ (A x *ᵥ z))
    (F : dirichletSobolev Ω →L[ℝ] ℝ) : dirichletSobolev Ω :=
  (variableDirichletEnergy_isCoercive i hR hΩ A hAm hK hAb hlam hell).continuousLinearEquivOfBilin.symm
    ((InnerProductSpace.toDual ℝ (dirichletSobolev Ω)).symm F)

theorem variableWeakSolution_equation {Ω : Set (CoordinateSpace n)} (i : Fin n) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K lam : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K) (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, ∀ z : Fin n → ℝ, lam * (∑ i, (z i)^2) ≤ z ⬝ᵥ (A x *ᵥ z))
    (F : dirichletSobolev Ω →L[ℝ] ℝ) (v : dirichletSobolev Ω) :
    variableDirichletEnergy Ω A hAm hK hAb
      (variableWeakSolution i hR hΩ A hAm hK hAb hlam hell F) v = F v := by
  let c := variableDirichletEnergy_isCoercive i hR hΩ A hAm hK hAb hlam hell
  let g := (InnerProductSpace.toDual ℝ (dirichletSobolev Ω)).symm F
  change variableDirichletEnergy Ω A hAm hK hAb (c.continuousLinearEquivOfBilin.symm g) v = F v
  rw [← c.continuousLinearEquivOfBilin_apply, c.continuousLinearEquivOfBilin.apply_symm_apply]
  exact InnerProductSpace.toDual_symm_apply

theorem variableWeakSolution_unique {Ω : Set (CoordinateSpace n)} (i : Fin n) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K lam : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K) (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, ∀ z : Fin n → ℝ, lam * (∑ i, (z i)^2) ≤ z ⬝ᵥ (A x *ᵥ z))
    (F : dirichletSobolev Ω →L[ℝ] ℝ) (u : dirichletSobolev Ω)
    (hu : ∀ v, variableDirichletEnergy Ω A hAm hK hAb u v = F v) :
    u = variableWeakSolution i hR hΩ A hAm hK hAb hlam hell F := by
  let c := variableDirichletEnergy_isCoercive i hR hΩ A hAm hK hAb hlam hell
  apply c.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [c.continuousLinearEquivOfBilin_apply, c.continuousLinearEquivOfBilin_apply, hu,
    variableWeakSolution_equation]

/-- Quantitative boundedness is derived from the actual energy identity,
not from a supplied inverse estimate. -/
theorem norm_variableWeakSolution_le {Ω : Set (CoordinateSpace n)} (i : Fin n) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K lam : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K) (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, ∀ z : Fin n → ℝ, lam * (∑ i, (z i)^2) ≤ z ⬝ᵥ (A x *ᵥ z))
    (F : dirichletSobolev Ω →L[ℝ] ℝ) :
    ‖variableWeakSolution i hR hΩ A hAm hK hAb hlam hell F‖ ≤ ((1+4*R^2)/lam) * ‖F‖ := by
  let u := variableWeakSolution i hR hΩ A hAm hK hAb hlam hell F
  have hl := variableDirichletEnergy_lower Ω A hAm hK hAb hell u
  have he := variableWeakSolution_equation i hR hΩ A hAm hK hAb hlam hell F u
  have hb := dirichlet_norm_sq_le_energy i hR hΩ u
  have hF : F u ≤ ‖F‖*‖u‖ := (le_abs_self _).trans (F.le_opNorm u)
  have hd : 0 < 1+4*R^2 := by positivity
  have hs : lam*‖u‖^2 ≤ (1+4*R^2)*‖F‖*‖u‖ := by
    have h1 := mul_le_mul_of_nonneg_left hb hlam.le
    have h2 := mul_le_mul_of_nonneg_left (hl.trans (he ▸ hF)) hd.le
    nlinarith
  change ‖u‖ ≤ ((1+4*R^2)/lam)*‖F‖
  by_cases hz : ‖u‖ = 0
  · rw [hz]; positivity
  · have hp : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hlam).mpr
    have ht : lam*‖u‖ ≤ (1+4*R^2)*‖F‖ := by nlinarith
    nlinarith

end GaussianTilt.MomentMapLinearDirichlet
