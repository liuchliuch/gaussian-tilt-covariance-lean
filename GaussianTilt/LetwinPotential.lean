import GaussianTilt.LetwinCutoff
import GaussianTilt.ConvexIntegrability

/-!
# Properness and normalization of the actual moment potential

The compact-sublevel theorem is transferred from EuclideanSpace to the finite
product coordinates used for integration by parts. No coercivity or attained
minimum is assumed.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ContDiff

namespace GaussianTilt.Letwin

lemma coordinatePotential_compact_sublevel {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ)
    (hi : Integrable (fun x => Real.exp (-φ x))) (a : ℝ) :
    IsCompact {x | φ x ≤ a} := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have hc' : ConvexOn ℝ univ (φ ∘ e) := by
    simpa only [preimage_univ] using hc.comp_linearMap e.toLinearMap
  have hi' : Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-φ (e x))) :=
    ((PiLp.volume_preserving_ofLp (Fin n)).integrable_comp_emb
      (EuclideanSpace.measurableEquiv (Fin n)).measurableEmbedding).mpr hi
  have hk := GaussianTilt.ConvexIntegrability.convexPotential_compact_sublevel
    (hφ.comp e.continuous) hc' hi' a
  have heq : e '' {x | φ (e x) ≤ a} = {x | φ x ≤ a} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx
      exact ⟨e.symm x, by simpa using hx, e.apply_symm_apply x⟩
  rw [← heq]
  exact hk.image e.continuous

lemma coordinatePotential_attains_minimum {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ)
    (hi : Integrable (fun x => Real.exp (-φ x))) :
    ∃ x : CoordinateSpace n, ∀ y : CoordinateSpace n, φ x ≤ φ y := by
  obtain ⟨x, hx, hmin⟩ := (coordinatePotential_compact_sublevel hφ hc hi (φ 0)).exists_isMinOn
    ⟨(0 : CoordinateSpace n), show φ 0 ≤ φ 0 from le_rfl⟩ hφ.continuousOn
  refine ⟨x, fun y => ?_⟩
  by_cases hy : φ y ≤ φ 0
  · exact hmin hy
  · exact (show φ x ≤ φ 0 from hx).trans (le_of_not_ge hy)

lemma coordinateDerivative_shift {n : ℕ} (φ : CoordinateSpace n → ℝ) (c : ℝ)
    (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => φ y - c + 1) x = coordinateDerivative i φ x := by
  simp only [coordinateDerivative, fderiv_add_const, fderiv_sub_const]

lemma divergenceDiffusion_shift {n : ℕ} (φ f : CoordinateSpace n → ℝ)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : CoordinateSpace n) :
    divergenceDiffusion φ A (fun y => f y - c + 1) x = divergenceDiffusion φ A f x := by
  have he (i : Fin n) : diffusionFlux A (fun y => f y - c + 1) i = diffusionFlux A f i := by
    funext y
    simp only [diffusionFlux, coordinateDerivative_shift]
  simp only [divergenceDiffusion, he]

/-- A4 with properness and attainment of a minimum removed from the hypotheses:
these follow from convexity and integrability of the actual exponential density. -/
theorem exists_diffusion_cutoffs_of_convexPotential {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : ConvexOn ℝ univ φ)
    (hi : Integrable (fun x => Real.exp (-φ x)))
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) (hApos : ∀ x, (A x).PosSemidef)
    (D : ℝ) (hD : ∀ x, |divergenceDiffusion φ A φ x| ≤ D) :
    ∃ χ : ℕ → CoordinateSpace n → ℝ, ∃ C : ℝ, 0 ≤ C ∧
      (∀ k, ContDiff ℝ ∞ (χ k) ∧ HasCompactSupport (χ k)) ∧
      (∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) ∧
      (∀ x, Monotone (fun k => χ k x)) ∧
      (∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
      (∀ k, (∫ x, ‖divergenceDiffusion φ A (χ k) x‖ ∂potentialMeasure φ) ≤ C / ((k : ℝ) + 1)) := by
  obtain ⟨x₀, hx₀⟩ := coordinatePotential_attains_minimum hφ.continuous hc hi
  let W := fun x => φ x - φ x₀ + 1
  have hW : ContDiff ℝ ∞ W := (hφ.sub contDiff_const).add contDiff_const
  have hproper : ∀ a : ℝ, IsCompact {x | W x ≤ a} := by
    intro a
    have heq : {x | W x ≤ a} = {x | φ x ≤ a + φ x₀ - 1} := by
      ext x
      dsimp [W]
      constructor <;> intro h <;> linarith
    rw [heq]
    exact coordinatePotential_compact_sublevel hφ.continuous hc hi _
  have hW0 : ∀ x, 0 ≤ W x := by intro x; dsimp [W]; linarith [hx₀ x]
  have hDW : ∀ x, |divergenceDiffusion φ A W x| ≤ D := by
    intro x
    change |divergenceDiffusion φ A (fun y => φ y - φ x₀ + 1) x| ≤ D
    rw [divergenceDiffusion_shift]
    exact hD x
  exact exists_diffusion_cutoffs (hφ.of_le (by simp)) hA hW hproper hW0 hApos D hDW

end GaussianTilt.Letwin
