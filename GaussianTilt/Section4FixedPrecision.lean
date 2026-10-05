import GaussianTilt.LowerOriginalResults

/-! # Actual axial variance for every fixed sufficiently large precision multiple

The same numerical Gaussian-window constant works for the c₁/t bound.
The dimension-scale constant is c₂=c₁/A. They are deliberately distinct:
the printed same-c inequality is not asserted by this module.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Real
open scoped BigOperators Topology Matrix.Norms.L2Operator
namespace GaussianTilt
open LowerProbability LowerFubini LowerMarginal LowerScales LowerConclusion

/-- Full arbitrary-fixed-A scope, including the exact density and exact
conversion between Gaussian and dimension scales. The dimension threshold
may depend on A, whereas the window constant does not. -/
theorem every_fixed_precision_axial_variance :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A ≥ A₀, 0 < windowConstant/A ∧ ∀ᶠ d : ℕ in atTop,
      ∀ i₀ : Fin d,
        0 < A/(d : ℝ)^(2/5 : ℝ) ∧
        Measure.map (fun x : Reference.Space (d+1) => x 0)
          (Reference.gaussianTilt (Reference.uniform (euclideanBody (deviationScale d) i₀))
            (A/(d : ℝ)^(2/5 : ℝ))) =
          axialLaw (A/(d : ℝ)^(2/5 : ℝ))
            (tiltedSlice d ((A/(d : ℝ)^(2/5 : ℝ))/rawTransverseVariance (deviationScale d) i₀)
              (deviationScale d) (rawAxialVariance d (deviationScale d))) ∧
        windowConstant/(A/(d : ℝ)^(2/5 : ℝ)) ≤
          variance (fun x : Reference.Space (d+1) => x 0)
            (Reference.gaussianTilt (Reference.uniform (euclideanBody (deviationScale d) i₀))
              (A/(d : ℝ)^(2/5 : ℝ))) ∧
        windowConstant/(A/(d : ℝ)^(2/5 : ℝ))=(windowConstant/A)*(d : ℝ)^(2/5 : ℝ) := by
  obtain ⟨A₀,hA₀,hacc⟩ := original4_9
  refine ⟨A₀,hA₀,?_⟩
  intro A hAA
  have hA : 0 < A := hA₀.trans_le hAA
  refine ⟨div_pos windowConstant_pos hA,?_⟩
  filter_upwards [hacc A hAA,eventually_rawBody_parameters,eventually_gt_atTop 0]
    with d haccd hpar hd
  intro i₀
  let t := A/(d : ℝ)^(2/5 : ℝ)
  have ht : 0 < t := div_pos hA (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)
  have hL : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr ht)
  have htL : t*((Real.sqrt t)⁻¹)^2=1 := by
    rw [inv_pow,Real.sq_sqrt ht.le]
    field_simp
  have hvar : windowConstant/t ≤ Reference.covariance
      (Reference.gaussianTilt (Reference.uniform (euclideanBody (deviationScale d) i₀)) t) 0 0 := by
    rw [euclideanBody_tilt_covariance_eq_axialLaw hpar.1 hpar.2 i₀ ht]
    apply gaussian_window_variance ht hL htL (tiltedSlice_measurable _ _ _ _)
      (tiltedSlice_mem_Icc _ _ _ _) (tiltedSlice_even _ _ _ _)
    intro z hz
    exact (haccd i₀ z hz).2.trans (haccd i₀ z hz).1
  rw [← euclideanBody_tilt_axial_variance_eq_covariance hpar.1 hpar.2 i₀ ht] at hvar
  refine ⟨ht,euclideanBody_tilt_axial_marginal hpar.1 hpar.2 i₀ ht,hvar,?_⟩
  field_simp

end GaussianTilt
