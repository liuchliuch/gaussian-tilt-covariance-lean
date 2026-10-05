import GaussianTilt.LetwinMomentJacobian

/-! # Positivity of the source Hessian derived from actual injective transport

The Jacobian formula permits singular derivatives. Positivity of the source
density forces the Jacobian to be nonzero, and convexity upgrades this to a
positive-definite Hessian. Thus positive definiteness is a conclusion here.
-/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ContDiff Topology ENNReal
namespace GaussianTilt.Letwin

lemma coordinateGradient_measurableEmbedding_of_injective {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hi : Function.Injective (coordinateGradient φ)) :
    MeasurableEmbedding (coordinateGradient φ) := (continuous_coordinateGradient hφ).measurableEmbedding hi

lemma coordinateGradient_range_measurable_of_injective {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hi : Function.Injective (coordinateGradient φ)) :
    MeasurableSet (Set.range (coordinateGradient φ)) := by
  simpa only [image_univ] using (coordinateGradient_measurableEmbedding_of_injective hφ hi).measurableSet_image' MeasurableSet.univ

theorem map_absHessianDet_density_eq_volume_range {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hi : Function.Injective (coordinateGradient φ)) :
    Measure.map (coordinateGradient φ)
      (volume.withDensity (fun x => ENNReal.ofReal |(coordinateHessian φ x).det|)) =
      volume.restrict (Set.range (coordinateGradient φ)) := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure (CoordinateSpace n))
    (s := univ) (f := coordinateGradient φ) (f' := fun x => coordinateMatrixMap (coordinateHessian φ x))
    MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (hasFDerivAt_coordinateGradient hφ x).hasFDerivWithinAt) hi.injOn
  simpa only [Measure.restrict_univ,image_univ,det_coordinateMatrixMap] using h

set_option maxHeartbeats 800000 in
theorem potentialMeasure_eq_absHessian_density_pullback {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hi : Function.Injective (coordinateGradient φ))
    {f : CoordinateSpace n → ℝ} (hfm : Measurable f)
    (hmap : momentMeasure φ=volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    potentialMeasure φ=volume.withDensity (fun x => ENNReal.ofReal
      (|(coordinateHessian φ x).det| *f (coordinateGradient φ x))) := by
  have hφ1 := hφ.of_le (show (1 : WithTop ℕ∞)≤2 by norm_num)
  let D := fun x => ENNReal.ofReal |(coordinateHessian φ x).det|
  let G := fun x => ENNReal.ofReal (f x)
  have he := coordinateGradient_measurableEmbedding_of_injective hφ1 hi
  have hR := coordinateGradient_range_measurable_of_injective hφ1 hi
  have hDm : Measurable D := (continuous_coordinateHessian hφ).matrix_det.abs.measurable.ennreal_ofReal
  have hGm : Measurable G := hfm.ennreal_ofReal
  have hweight : volume.withDensity (fun x => ENNReal.ofReal
      (|(coordinateHessian φ x).det| *f (coordinateGradient φ x))) =
      (volume.withDensity D).withDensity (fun x => G (coordinateGradient φ x)) := by
    rw [← withDensity_mul volume hDm (g := fun x => G (coordinateGradient φ x)) (hGm.comp he.measurable)]
    congr 1
    funext x
    exact ENNReal.ofReal_mul (abs_nonneg _)
  have hrestr : (momentMeasure φ).restrict (Set.range (coordinateGradient φ))=momentMeasure φ := by
    have hp : coordinateGradient φ ⁻¹' Set.range (coordinateGradient φ)=univ := by
      ext x
      simp only [mem_preimage,mem_range,mem_univ,iff_true]
      exact ⟨x,rfl⟩
    rw [momentMeasure,Measure.restrict_map he.measurable hR,hp,Measure.restrict_univ]
  have hpush : Measure.map (coordinateGradient φ)
      (volume.withDensity (fun x => ENNReal.ofReal (|(coordinateHessian φ x).det| *f (coordinateGradient φ x)))) =
      momentMeasure φ := by
    rw [hweight,GaussianTilt.map_withDensity_comp he,map_absHessianDet_density_eq_volume_range hφ hi,
      ← restrict_withDensity hR]
    change (volume.withDensity G).restrict _ = _
    rw [← hmap]
    exact hrestr
  have h := congrArg (Measure.comap (coordinateGradient φ)) hpush
  simpa only [he.comap_map,momentMeasure] using h.symm

theorem injective_moment_transport_density_identity {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hi : Function.Injective (coordinateGradient φ))
    {f : CoordinateSpace n → ℝ} (hfm : Measurable f) (hfn : ∀ z, 0≤f z)
    (hfc : Continuous (fun x => f (coordinateGradient φ x)))
    (hmap : momentMeasure φ=volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (x : CoordinateSpace n) :
    Real.exp (-φ x)=|(coordinateHessian φ x).det| *f (coordinateGradient φ x) := by
  have heq := potentialMeasure_eq_absHessian_density_pullback hφ hi hfm hmap
  have hsrc : Continuous (fun x => Real.exp (-φ x)) := Real.continuous_exp.comp hφ.continuous.neg
  have hdst : Continuous (fun x => |(coordinateHessian φ x).det| *f (coordinateGradient φ x)) :=
    (continuous_coordinateHessian hφ).matrix_det.abs.mul hfc
  have hae : (fun x => Real.exp (-φ x)) =ᵐ[volume]
      (fun x => |(coordinateHessian φ x).det| *f (coordinateGradient φ x)) := by
    have h := (withDensity_eq_iff_of_sigmaFinite hsrc.measurable.ennreal_ofReal.aemeasurable
      hdst.measurable.ennreal_ofReal.aemeasurable).mp heq
    filter_upwards [h] with y hy
    have hr := congrArg ENNReal.toReal hy
    simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _),
      ENNReal.toReal_ofReal (mul_nonneg (abs_nonneg _) (hfn _))] using hr
  exact congrFun (Measure.eq_of_ae_eq hae hsrc hdst) x

lemma posDef_of_posSemidef_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (hdet : M.det≠0) : M.PosDef := by
  apply hM.isHermitian.posDef_iff_eigenvalues_pos.mpr
  intro i
  exact lt_of_le_of_ne (hM.eigenvalues_nonneg i)
    (Ne.symm (eigenvalues_ne_zero_of_det_ne hM.isHermitian hdet i))

/-- Positive source density forces a nondegenerate Jacobian. Convexity then
makes the actual Hessian positive definite, without assuming it. -/
theorem hessian_posDef_of_injective_moment_transport {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : ConvexOn ℝ univ φ)
    (hi : Function.Injective (coordinateGradient φ))
    {f : CoordinateSpace n → ℝ} (hfm : Measurable f) (hfn : ∀ z, 0≤f z)
    (hfc : Continuous (fun x => f (coordinateGradient φ x)))
    (hmap : momentMeasure φ=volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (x : CoordinateSpace n) : (coordinateHessian φ x).PosDef := by
  have hid := injective_moment_transport_density_identity hφ hi hfm hfn hfc hmap x
  have hdet : (coordinateHessian φ x).det≠0 := by
    intro hz
    simp only [hz,abs_zero,zero_mul] at hid
    exact (Real.exp_pos (-φ x)).ne' hid
  exact posDef_of_posSemidef_det_ne_zero
    (coordinateHessian_posSemidef_of_convex isOpen_univ hc hφ.contDiffOn (mem_univ x)) hdet

/-- Strict convexity, C² regularity and the actual moment transport imply
both a positive Hessian and the pointwise Monge–Ampère equation. -/
theorem posDef_and_mongeAmpere_of_strictConvex_transport {n : ℕ}
    {φ V f : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : StrictConvexOn ℝ univ φ)
    (hfm : Measurable f) (hfn : ∀ z, 0≤f z)
    (hVc : Continuous (fun x => V (coordinateGradient φ x)))
    (hvalue : ∀ x, f (coordinateGradient φ x)=Real.exp (-V (coordinateGradient φ x)))
    (hmap : momentMeasure φ=volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    (∀ x, (coordinateHessian φ x).PosDef) ∧
      (∀ x, Real.log (coordinateHessian φ x).det = -φ x+V (coordinateGradient φ x)) := by
  have hinj := coordinateGradient_injective_of_strictConvex (hφ.differentiable (by norm_num)) hc
  have hfc : Continuous (fun x => f (coordinateGradient φ x)) := by
    have heq : (fun x => f (coordinateGradient φ x)) =
        (fun x => Real.exp (-V (coordinateGradient φ x))) := funext hvalue
    rw [heq]
    exact Real.continuous_exp.comp hVc.neg
  have hH := hessian_posDef_of_injective_moment_transport hφ hc.convexOn hinj hfm hfn hfc hmap
  exact ⟨hH,mongeAmpere_of_moment_transport hφ hH hfm hfn hVc hvalue hmap⟩

end GaussianTilt.Letwin
