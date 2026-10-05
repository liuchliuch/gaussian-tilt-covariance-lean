import GaussianTilt.MomentMapCalabiAffine

/-! # Reducing the actual Calabi inequality to identity Hessian

Every derivative and metric transformation is proved. The input here is only
the still-to-be-assembled normalized differential calculation, not an axiom.
-/
noncomputable section
open Matrix Filter Set
open scoped BigOperators ContDiff Topology
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- An actual identity-Hessian differential estimate implies the arbitrary
positive-Hessian estimate by the constructed unimodular normalization. -/
theorem calabi_inequality_of_identity_hessian
    (hn : 0 < n)
    (hidentity : ∀ (v : CoordinateSpace n → ℝ), ContDiff ℝ ∞ v →
      ∀ y : CoordinateSpace n, coordinateHessian v y = 1 →
      (∀ᶠ z in 𝓝 y, (coordinateHessian v z).det = 1) →
      calabiAdjugateEnergy v y ^ 2 / (2 * n) ≤ linearizedMA 1 (calabiAdjugateEnergy v) y)
    {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) (x : CoordinateSpace n)
    (hH : (coordinateHessian u x).PosDef)
    (hMA : ∀ᶠ z in 𝓝 x, (coordinateHessian u z).det = 1) :
    calabiAdjugateEnergy u x ^ 2 / (2 * n) ≤
      linearizedMA (coordinateHessian u x)⁻¹ (calabiAdjugateEnergy u) x := by
  let R := Whitening.inverseRoot (coordinateHessian u x)
  obtain ⟨hRdet, hRH, hRR⟩ := inverseRoot_normalizes_unit_hessian hH hMA.self_of_nhds
  change R.det = 1 at hRdet
  let y := R⁻¹ *ᵥ x
  have hRy : R *ᵥ y = x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv R (isUnit_iff_ne_zero.mpr (by rw [hRdet]; norm_num)),
      Matrix.one_mulVec]
  let v := u ∘ coordinateMatrixMap R
  have hv : ContDiff ℝ ∞ v := hu.comp (coordinateMatrixMap R).contDiff
  have hHv : coordinateHessian v y = 1 := by
    rw [coordinateHessian_comp_matrix (contDiff_infty.mp hu 2), hRy]
    exact hRH
  have hdetv : ∀ᶠ z in 𝓝 y, (coordinateHessian v z).det = 1 := by
    have ht : Tendsto (coordinateMatrixMap R) (𝓝 y) (𝓝 x) := by
      simpa only [coordinateMatrixMap_apply, hRy] using (coordinateMatrixMap R).continuous.tendsto y
    filter_upwards [ht.eventually hMA] with z hz
    rw [coordinateHessian_comp_matrix (contDiff_infty.mp hu 2), Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose, hRdet]
    simpa only [one_mul, mul_one, coordinateMatrixMap_apply] using hz
  have he := hidentity v hv y hHv hdetv
  have henergy : calabiAdjugateEnergy v y = calabiAdjugateEnergy u x := by
    rw [calabiAdjugateEnergy_comp_matrix hu R hRdet]
    change calabiAdjugateEnergy u (R *ᵥ y) = _
    rw [hRy]
  have hmetric : R * (1 : Matrix (Fin n) (Fin n) ℝ) * Rᵀ = (coordinateHessian u x)⁻¹ := by
    simpa only [Matrix.mul_one] using hRR
  have hlin := linearized_calabiAdjugateEnergy_comp_matrix hu (coordinateHessian u x)⁻¹ 1 R hRdet hmetric y
  rw [hRy] at hlin
  rwa [henergy, hlin] at he

end GaussianTilt.MomentMapRegularity
