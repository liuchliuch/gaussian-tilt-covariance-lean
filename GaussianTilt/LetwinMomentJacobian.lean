import GaussianTilt.LetwinMomentDiffeomorphism

/-! # Deriving the Monge–Ampère density identity from genuine transport -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ContDiff Topology ENNReal
namespace GaussianTilt.Letwin

lemma continuous_coordinateHessian {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) : Continuous (coordinateHessian φ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (contDiff_coordinateDerivative
    (contDiff_coordinateDerivative hφ (m := 1) (by norm_num) i) (m := 0) (by norm_num) j).continuous

/-- The actual Jacobian change of variables for the smooth moment gradient. -/
theorem map_hessianDet_density_eq_volume_range {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hH : ∀ x, (coordinateHessian φ x).PosDef) :
    Measure.map (coordinateGradient φ)
      (volume.withDensity (fun x => ENNReal.ofReal (coordinateHessian φ x).det)) =
      volume.restrict (Set.range (coordinateGradient φ)) := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure (CoordinateSpace n))
    (s := Set.univ) (f := coordinateGradient φ) (f' := fun x => coordinateMatrixMap (coordinateHessian φ x))
    MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (hasFDerivAt_coordinateGradient hφ x).hasFDerivWithinAt)
    (coordinateGradient_injective_of_posDef hφ hH).injOn
  simpa only [Measure.restrict_univ, image_univ, det_coordinateMatrixMap,
    abs_of_pos (hH _).det_pos] using h

lemma momentMeasure_restrict_gradient_range {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hH : ∀ x, (coordinateHessian φ x).PosDef) :
    (momentMeasure φ).restrict (Set.range (coordinateGradient φ)) = momentMeasure φ := by
  have hp : coordinateGradient φ ⁻¹' Set.range (coordinateGradient φ) = univ := by
    ext x
    simp only [mem_preimage, mem_range, mem_univ, iff_true]
    exact ⟨x,rfl⟩
  rw [momentMeasure, Measure.restrict_map (continuous_coordinateGradient (hφ.of_le (by norm_num))).measurable
    (coordinateGradient_range_open hφ hH).measurableSet, hp, Measure.restrict_univ]

set_option maxHeartbeats 800000 in
/-- The source Gibbs density is the actual pullback of the target density
multiplied by the actual Hessian determinant. The equality is obtained from
injective measure transport and the proved Jacobian theorem. -/
theorem potentialMeasure_eq_hessian_density_pullback {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hH : ∀ x, (coordinateHessian φ x).PosDef)
    {f : CoordinateSpace n → ℝ} (hfm : Measurable f)
    (hmap : momentMeasure φ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    potentialMeasure φ = volume.withDensity (fun x => ENNReal.ofReal
      ((coordinateHessian φ x).det * f (coordinateGradient φ x))) := by
  let D := fun x => ENNReal.ofReal (coordinateHessian φ x).det
  let G := fun x => ENNReal.ofReal (f x)
  have he := coordinateGradient_measurableEmbedding hφ hH
  have hDm : Measurable D := (continuous_coordinateHessian hφ).matrix_det.measurable.ennreal_ofReal
  have hGm : Measurable G := hfm.ennreal_ofReal
  have hweight : volume.withDensity (fun x => ENNReal.ofReal
        ((coordinateHessian φ x).det * f (coordinateGradient φ x))) =
      (volume.withDensity D).withDensity (fun x => G (coordinateGradient φ x)) := by
    rw [← withDensity_mul volume hDm (g := fun x => G (coordinateGradient φ x)) (hGm.comp he.measurable)]
    congr 1
    funext x
    exact ENNReal.ofReal_mul (hH x).det_pos.le
  have hpush : Measure.map (coordinateGradient φ)
      (volume.withDensity (fun x => ENNReal.ofReal ((coordinateHessian φ x).det * f (coordinateGradient φ x)))) =
      momentMeasure φ := by
    rw [hweight, GaussianTilt.map_withDensity_comp he, map_hessianDet_density_eq_volume_range hφ hH,
      ← restrict_withDensity (coordinateGradient_range_open hφ hH).measurableSet]
    change (volume.withDensity G).restrict _ = _
    rw [← hmap]
    exact momentMeasure_restrict_gradient_range hφ hH
  have heq : Measure.map (coordinateGradient φ) (potentialMeasure φ) =
      Measure.map (coordinateGradient φ) (volume.withDensity (fun x => ENNReal.ofReal
        ((coordinateHessian φ x).det * f (coordinateGradient φ x)))) := hpush.symm
  have h := congrArg (Measure.comap (coordinateGradient φ)) heq
  simpa only [he.comap_map] using h

/-- Continuous pullback densities turn the actual almost-everywhere
Jacobian identity into a pointwise identity on the whole source space. -/
theorem moment_transport_density_identity {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hH : ∀ x, (coordinateHessian φ x).PosDef)
    {f : CoordinateSpace n → ℝ} (hfm : Measurable f) (hfn : ∀ z, 0≤f z)
    (hfc : Continuous (fun x => f (coordinateGradient φ x)))
    (hmap : momentMeasure φ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (x : CoordinateSpace n) :
    Real.exp (-φ x) = (coordinateHessian φ x).det * f (coordinateGradient φ x) := by
  have heq := potentialMeasure_eq_hessian_density_pullback hφ hH hfm hmap
  have hsrc : Continuous (fun x => Real.exp (-φ x)) := Real.continuous_exp.comp hφ.continuous.neg
  have hdst : Continuous (fun x => (coordinateHessian φ x).det * f (coordinateGradient φ x)) :=
    (continuous_coordinateHessian hφ).matrix_det.mul hfc
  have hae : (fun x => Real.exp (-φ x)) =ᵐ[volume]
      (fun x => (coordinateHessian φ x).det * f (coordinateGradient φ x)) := by
    have h := (withDensity_eq_iff_of_sigmaFinite hsrc.measurable.ennreal_ofReal.aemeasurable
      hdst.measurable.ennreal_ofReal.aemeasurable).mp heq
    filter_upwards [h] with y hy
    have hreal := congrArg ENNReal.toReal hy
    simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _),
      ENNReal.toReal_ofReal (mul_nonneg (hH y).det_pos.le (hfn _))] using hreal
  exact congrFun (Measure.eq_of_ae_eq hae hsrc hdst) x

/-- The Monge–Ampère log-determinant equation is derived from actual
transport whenever the target density agrees with exp(-V) on the gradient
image. No pointwise density or PDE identity is assumed. -/
theorem mongeAmpere_of_moment_transport {n : ℕ} {φ V f : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hH : ∀ x, (coordinateHessian φ x).PosDef)
    (hfm : Measurable f) (hfn : ∀ z, 0≤f z)
    (hVc : Continuous (fun x => V (coordinateGradient φ x)))
    (hvalue : ∀ x, f (coordinateGradient φ x)=Real.exp (-V (coordinateGradient φ x)))
    (hmap : momentMeasure φ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (x : CoordinateSpace n) :
    Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x) := by
  have hfc : Continuous (fun x => f (coordinateGradient φ x)) := by
    have he : (fun x => f (coordinateGradient φ x)) = (fun x => Real.exp (-V (coordinateGradient φ x))) := funext hvalue
    rw [he]
    exact Real.continuous_exp.comp hVc.neg
  have h := moment_transport_density_identity hφ hH hfm hfn hfc hmap x
  rw [hvalue x] at h
  have hl := congrArg Real.log h
  rw [Real.log_exp, Real.log_mul (hH x).det_pos.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  linarith

end GaussianTilt.Letwin
