import GaussianTilt.MomentMapSchauderBoundaryVariableNormalizedMap

/-! # Genuine variable-coefficient elliptic boundary first-jet estimate -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000
open Set Matrix
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- General frozen SPD coefficients are normalized by the constructed
boundary-preserving square root. Radius and constants are uniform over the
ellipticity and coefficient Hölder data, and independent of the unknown
initial Hessian bounds. -/
theorem exists_elliptic_boundary_first_jet_bound [NeZero n]
    {α K R lam Λ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hK : 0 ≤ K) (hR : 0 < R)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 2*ρ ≤ R ∧ 0 < C ∧ ∀ (j : Fin n)
      (u f : KernelSpace n → ℝ) (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
      (D : KernelSpace n → KernelSpace n →L[ℝ] ℝ)
      (B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ),
      (∀ x, x j ≤ 0 → u x=0) → ContDiffOn ℝ 2 u (flatUpperBall j R) →
      (∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.ball (0 : KernelSpace n) R, |u x| ≤ L*|x j|) →
      (∀ x ∈ flatUpperBall j R, D x=fderiv ℝ u x) →
      (∀ x ∈ flatUpperBall j R, B x=fderiv ℝ (fderiv ℝ u) x) →
      BoundedHolderOn α B (flatClosedPatch j R) → (A 0).PosDef →
      (∀ v : KernelSpace n, lam*‖v‖^2 ≤ euclideanQuadratic (A 0) v) →
      (∀ v : KernelSpace n, euclideanQuadratic (A 0) v ≤ Λ*‖v‖^2) →
      (∀ x ∈ flatClosedPatch j R, (A x).IsSymm) →
      (∀ x ∈ flatClosedPatch j R, ∀ y ∈ flatClosedPatch j R, ∀ i k, |A x i k-A y i k| ≤ K*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j R, matrixContraction (A x) (bilinearEntryMatrix (B x))=f x) →
      ∀ U V HU HD F H : ℝ, 0 ≤ U → 0 ≤ V → 0 ≤ HU → 0 ≤ HD → 0 ≤ F → 0 ≤ H →
      (∀ x ∈ flatClosedPatch j R, |u x| ≤ U) → (∀ x ∈ flatClosedPatch j R, ‖D x‖ ≤ V) →
      (∀ x ∈ flatClosedPatch j R, ∀ y ∈ flatClosedPatch j R, |u x-u y| ≤ HU*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j R, ∀ y ∈ flatClosedPatch j R, ‖D x-D y‖ ≤ HD*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j R, |f x| ≤ F) →
      (∀ x ∈ flatClosedPatch j R, ∀ y ∈ flatClosedPatch j R, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j ρ, ‖B x‖ ≤ C*(U+V+HU+HD+F+H)) ∧
      (∀ x ∈ flatClosedPatch j ρ, ∀ y ∈ flatClosedPatch j ρ,
        ‖B x-B y‖ ≤ C*(U+V+HU+HD+F+H)*‖x-y‖^α) := by
  let M := Real.sqrt Λ+1
  let I := (Real.sqrt lam)⁻¹
  have hM : 0 < M := by dsimp [M]; positivity
  have hI : 0 < I := inv_pos.mpr (Real.sqrt_pos.mpr hlam)
  obtain ⟨ρ,C,hρ,hρR,hC,hbound⟩ := exists_boundary_first_jet_bound_of_normalization (n := n) hα hα1 hK hR hM hI
  refine ⟨ρ,C,hρ,hρR,hC,?_⟩
  intro j u f A D B hu0 hu hgrowth hD hB hBH hA0 hlower hupper hAs hAH heq U V HU HD F H hU hV hHU hHD hF hH huB hDB huH hDH hfB hfH
  obtain ⟨P,c,hc,hplane,_,hP,hPi,_,hPP⟩ := exists_quantitative_boundary_normalization j hA0 hlam hΛ hlower hupper
  have hPM : ‖P.toContinuousLinearMap‖ ≤ M := hP.trans (by dsimp [M]; linarith)
  exact hbound j P c hc hplane hPM hPi u f A D B hu0 hu hgrowth hD hB hBH hPP hAs hAH heq
    U V HU HD F H hU hV hHU hHD hF hH huB hDB huH hDH hfB hfH

end GaussianTilt.MomentMapSchauder
