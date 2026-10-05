import GaussianTilt.MomentMapRegularityConstantDensityThirdDerivative

/-!
# The actual Alexandrov mass bound from the smooth determinant equation

Local supporting slopes coincide with the actual gradient. The area
inequality and the literal determinant of its derivative then bound the
subgradient image by the source volume; no classical/Alexandrov conversion
is assumed.
-/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators Topology ContDiff Gradient ENNReal NNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma contDiff_gradient_of_smooth {u : E n → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (gradient u) := by
  exact (InnerProductSpace.toDual ℝ (E n)).symm.contDiff.comp
    (hu.fderiv_right (m := ∞) (by simp))

lemma matrix_fderiv_coordinateGradient {f : CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : CoordinateSpace n) :
    LinearMap.toMatrix' (fderiv ℝ (coordinateGradient f) x).toLinearMap = coordinateHessian f x := by
  ext i j
  change (fderiv ℝ (fun y a => coordinateDerivative a f y) x (Pi.single j 1)) i = _
  rw [fderiv_pi (fun a => (smooth_coordinateDerivative hf a).differentiable (by simp) x)]
  rfl

/-- The classical gradient Jacobian determinant is exactly the determinant
of the coordinate Hessian used in the a priori estimates. -/
theorem determinant_fderiv_gradient_eq_coordinateHessian {u : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : E n) :
    (fderiv ℝ (gradient u) x).det =
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det := by
  let e := coordinateEquiv n
  have hg := (contDiff_gradient_of_smooth hu).differentiable (by simp)
  have hU : ContDiff ℝ ∞ (coordinatePullback u) := hu.comp e.symm.contDiff
  have he : coordinateGradient (coordinatePullback u) = fun y => e (gradient u (e.symm y)) :=
    funext (coordinateGradient_pullback (hu.differentiable (by simp)))
  have hd : fderiv ℝ (coordinateGradient (coordinatePullback u)) (e x) =
      e.toContinuousLinearMap.comp ((fderiv ℝ (gradient u) x).comp e.symm.toContinuousLinearMap) := by
    rw [he]
    have hinner := (hg (e.symm (e x))).hasFDerivAt.comp (e x) e.symm.hasFDerivAt
    have houter := e.hasFDerivAt.comp (e x) hinner
    simpa only [Function.comp_def, e.symm_apply_apply] using houter.fderiv
  have hmat := matrix_fderiv_coordinateGradient hU (e x)
  rw [← hmat, LinearMap.det_toMatrix', hd]
  exact (LinearMap.det_conj (fderiv ℝ (gradient u) x).toLinearMap e.toLinearEquiv).symm

/-- Every local supporting slope at an interior differentiability point is
the actual gradient; this needs no global convex extension. -/
lemma supportsOn_eq_gradient {S : Set (E n)} {u : E n → ℝ} {x p : E n}
    (hx : x ∈ interior S) (hu : DifferentiableAt ℝ u x) (hp : SupportsOn S u p x) :
    p = gradient u x := by
  apply (supporting_vector_eq_gradient_of_eventually hu ?_).symm
  filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
  exact hp y hy

/-- The smooth unit-determinant equation bounds the literal Alexandrov
image on every measurable interior test set. Injectivity is not needed for
the area upper bound. -/
theorem subgradientImageOn_volume_le_of_smooth_unit_det
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u) {S A : Set (E n)}
    (hA : MeasurableSet A) (hAS : A ⊆ interior S)
    (hMA : ∀ y ∈ A, (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).det = 1) :
    volume (subgradientImageOn S u A) ≤ volume A := by
  have hg := (contDiff_gradient_of_smooth hu).differentiable (by simp)
  have him : subgradientImageOn S u A ⊆ gradient u '' A := by
    rintro p ⟨x, hx, hp⟩
    exact ⟨x, hx, (supportsOn_eq_gradient (hAS hx) (hu.differentiable (by simp) x) hp).symm⟩
  have harea := addHaar_image_le_lintegral_abs_det_fderiv volume hA
    (fun x _ => (hg x).hasFDerivAt.hasFDerivWithinAt)
  have hint : (∫⁻ x in A, ENNReal.ofReal |(fderiv ℝ (gradient u) x).det|) = volume A := by
    calc
      (∫⁻ x in A, ENNReal.ofReal |(fderiv ℝ (gradient u) x).det|) = ∫⁻ _x in A, (1 : ℝ≥0∞) := by
        apply setLIntegral_congr_fun hA
        intro x hx
        change ENNReal.ofReal |(fderiv ℝ (gradient u) x).det| = 1
        rw [determinant_fderiv_gradient_eq_coordinateHessian hu, hMA x hx]
        simp
      _ = _ := by simp
  exact (measure_mono him).trans (harea.trans_eq hint)

/-- In particular the total interior Alexandrov mass is controlled by the
volume of the compact domain, directly from the classical equation. -/
theorem subgradientImageOn_interior_volume_le_of_smooth_unit_det
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u) {S : Set (E n)}
    (hMA : ∀ y ∈ interior S,
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).det = 1) :
    volume (subgradientImageOn S u (interior S)) ≤ volume S :=
  (subgradientImageOn_volume_le_of_smooth_unit_det hu isOpen_interior.measurableSet Subset.rfl hMA).trans
    (measure_mono interior_subset)

end GaussianTilt.MomentMapRegularity
