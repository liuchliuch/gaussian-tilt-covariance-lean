import GaussianTilt.LetwinMomentJacobianInjective
import GaussianTilt.MomentMapSchauderDifferences
import GaussianTilt.MomentMapSchauderUniformEllipticity

/-!
# Local Hölder control of the actual source difference coefficients

The inverse bound is derived uniformly on a compact source set from C²
regularity and positive definiteness. The Hölder modulus follows from the
literal Hessian Hölder modulus, and is uniform in the difference step.
-/
noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.Letwin

/-- Once first C²,α regularity is established, the linearized difference
coefficients have a common α-Hölder bound for every admissible displacement.
The compact inverse bound is derived, not an additional input. -/
theorem exists_sourceDifferenceCoefficient_holder_bound {n : ℕ}
    {φ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    {C α : ℝ} (hC : 0 ≤ C)
    (hholder : ∀ x ∈ S, ∀ y ∈ S, ∀ i j,
      |coordinateHessian φ x i j - coordinateHessian φ y i j| ≤ C * ‖x - y‖ ^ α) :
    ∃ D : ℝ, 0 < D ∧ ∀ h x y : CoordinateSpace n,
      x ∈ S → x + h ∈ S → y ∈ S → y + h ∈ S → ∀ i j,
      |sourceDifferenceCoefficient φ h x i j - sourceDifferenceCoefficient φ h y i j| ≤
        D * ‖x - y‖ ^ α := by
  obtain ⟨M, hM, hbound⟩ := exists_bound_inv_segments_on_compact hS
    (continuous_coordinateHessian hφ).continuousOn (fun x _ => hpos x)
  let D : ℝ := (n : ℝ) ^ 2 * M ^ 2 * C + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro h x y hx hxh hy hyh i j
  have hpow : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have hshift : x + h - (y + h) = x - y := by abel
  have hb := abs_averagedInverse_entry_sub_le
    (hpos x) (hpos (x + h)) (hpos y) (hpos (y + h)) hM.le (mul_nonneg hC hpow)
    (hbound x hx (x + h) hxh) (hbound y hy (y + h) hyh)
    (hholder x hx y hy)
    (by simpa only [hshift] using hholder (x + h) hxh (y + h) hyh) i j
  change |sourceDifferenceCoefficient φ h x i j - sourceDifferenceCoefficient φ h y i j| ≤ _ at hb
  apply hb.trans
  simp only [Fintype.card_fin]
  dsimp [D]
  nlinarith

/-- Positivity of each actual finite-difference coefficient follows from
positive definite source Hessians, without a separate ellipticity premise. -/
theorem sourceDifferenceCoefficient_posDef {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) (h x : CoordinateSpace n) :
    (sourceDifferenceCoefficient φ h x).PosDef :=
  averagedInverse_posDef (hpos x) (hpos (x + h))

/-- Compact uniform ellipticity for every sufficiently local source
finite-difference coefficient, derived from C² regularity and positivity. -/
theorem exists_sourceDifferenceCoefficient_uniform_ellipticity {n : ℕ}
    {φ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    {S : Set (CoordinateSpace n)} (hS : IsCompact S) :
    ∃ lam Λ : ℝ, 0 < lam ∧ 0 < Λ ∧ ∀ h x : CoordinateSpace n,
      x ∈ S → x + h ∈ S → ∀ v : EuclideanSpace ℝ (Fin n),
        lam * ‖v‖ ^ 2 ≤ euclideanQuadratic (sourceDifferenceCoefficient φ h x) v ∧
          euclideanQuadratic (sourceDifferenceCoefficient φ h x) v ≤ Λ * ‖v‖ ^ 2 := by
  obtain ⟨lam, Λ, hlam, hΛ, hb⟩ := exists_uniform_ellipticity_averagedInverse_on_compact hS
    (continuous_coordinateHessian hφ).continuousOn (fun x _ => hpos x)
  exact ⟨lam, Λ, hlam, hΛ, fun h x hx hxh v => hb x hx (x + h) hxh v⟩

/-- The finite-difference equation follows from the literal transport law
once C² regularity has been established.  Neither the classical Monge--Ampère
equation nor positive definiteness is an additional hypothesis. -/
theorem sourceDifferenceQuotient_equation_of_transport {n : ℕ}
    {φ V f : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : StrictConvexOn ℝ univ φ)
    (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hVc : Continuous (fun x => V (coordinateGradient φ x)))
    (hvalue : ∀ x, f (coordinateGradient φ x) = Real.exp (-V (coordinateGradient φ x)))
    (hmap : momentMeasure φ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (h : CoordinateSpace n) (s : ℝ) (x : CoordinateSpace n) :
    (sourceDifferenceCoefficient φ h x).PosDef ∧
      (∑ i, ∑ j, sourceDifferenceCoefficient φ h x i j *
        coordinateDerivative j (coordinateDerivative i (sourceDifferenceQuotient φ h s)) x) =
        -sourceDifferenceQuotient φ h s x +
          sourceDifferenceQuotient (fun y => V (coordinateGradient φ y)) h s x := by
  obtain ⟨hpos, hMA⟩ := posDef_and_mongeAmpere_of_strictConvex_transport hφ hc hfm hfn hVc hvalue hmap
  exact ⟨sourceDifferenceCoefficient_posDef hpos h x,
    sourceDifferenceQuotient_elliptic_equation hφ hpos hMA h s x⟩

end GaussianTilt.MomentMapSchauder
