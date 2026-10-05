import GaussianTilt.StandardizedTilt

/-! # Exact Gaussian tail/Laplace identities and scaling -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal Topology
namespace GaussianTilt.GaussianLaplace
open LaplaceCutoff LaplaceComparison StandardizedTilt TiltedCubeComparison

lemma oneSidedLaplace_map_mul (μ : Measure ℝ) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    oneSidedLaplace (μ.map (fun x ↦ c * x)) t = oneSidedLaplace μ (t * c) := by
  rw [oneSidedLaplace, oneSidedLaplace, ← integral_indicator measurableSet_Ici,
    ← integral_indicator measurableSet_Ici,
    integral_map (by fun_prop)
      ((show Measurable (fun x : ℝ ↦ Real.exp (-t * x)) by fun_prop).aestronglyMeasurable.indicator measurableSet_Ici)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : 0 ≤ x
  · have hcx : 0 ≤ c * x := mul_nonneg hc.le hx
    rw [Set.indicator_of_mem (show c * x ∈ Set.Ici (0 : ℝ) from hcx),
      Set.indicator_of_mem (show x ∈ Set.Ici (0 : ℝ) from hx)]
    congr 1
    ring
  · have hcx : ¬ 0 ≤ c * x := by nlinarith
    rw [Set.indicator_of_notMem (show c * x ∉ Set.Ici (0 : ℝ) from hcx),
      Set.indicator_of_notMem (show x ∉ Set.Ici (0 : ℝ) from hx)]

lemma gaussian_laplace_scale {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    oneSidedLaplace (gaussianReal 0 v) t =
      oneSidedLaplace (gaussianReal 0 1) (t * Real.sqrt (v : ℝ)) := by
  have hvp : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hmap : (gaussianReal 0 1).map (fun x ↦ Real.sqrt (v : ℝ) * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt hvp.le]
  rw [← hmap]
  exact oneSidedLaplace_map_mul _ (Real.sqrt_pos.mpr hvp) t

lemma gaussian_tilt (t : ℝ) :
    (gaussianReal 0 1).tilted (fun x ↦ t * x) = gaussianReal t 1 := by
  have hi : Integrable (fun x : ℝ ↦ Real.exp (t * x)) (gaussianReal 0 1) :=
    integrable_exp_mul_gaussianReal t
  haveI := isProbabilityMeasure_tilted hi
  have hM : mgf id ((gaussianReal 0 1).tilted (fun x ↦ t * x)) = mgf id (gaussianReal t 1) := by
    funext u
    rw [mgf_id_exponential_tilt]
    simp only [mgf_id_gaussianReal]
    simp only [NNReal.coe_one, zero_mul, zero_add, one_mul]
    rw [← Real.exp_sub]
    congr 1
    ring
  have h0 : (0 : ℝ) ∈ interior
      (integrableExpSet id ((gaussianReal 0 1).tilted (fun x ↦ t * x))) :=
    cramer_tilt (by simp)
  have hh := map_eq_of_mgf aemeasurable_id aemeasurable_id h0 hM
  simpa only [Measure.map_id] using hh

lemma gaussian_right_tail_eq_laplace (z : ℝ) :
    (gaussianReal 0 1).real (Set.Ici z) =
      Real.exp (-(z ^ 2) / 2) * oneSidedLaplace (gaussianReal 0 1) z := by
  have h := tail_eq_tilted_laplace (gaussianReal 0 1) id measurable_id z z
    (integrable_exp_mul_gaussianReal z)
  simp only [id_eq] at h
  rw [gaussian_tilt, gaussianReal_map_sub_const] at h
  have hc : cgf id (gaussianReal 0 1) z = z ^ 2 / 2 := by
    simp [cgf, mgf_id_gaussianReal]
  rw [hc] at h
  simpa only [sub_self, id_eq, show z ^ 2 / 2 - z * z = -(z ^ 2) / 2 by ring] using h

/-- Standard normal upper-tail notation matching the paper. -/
def normalTail (z : ℝ) : ℝ := 1 - cdf (gaussianReal 0 1) z

lemma normalTail_eq_measure (z : ℝ) : normalTail z = (gaussianReal 0 1).real (Set.Ici z) := by
  letI := noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hc := measureReal_compl (μ := gaussianReal 0 1) (s := Set.Iic z) measurableSet_Iic
  simp only [Set.compl_Iic, measureReal_univ_eq_one] at hc
  rw [normalTail, cdf_eq_real, ← hc]
  exact congrArg ENNReal.toReal (measure_congr (Ioi_ae_eq_Ici (μ := gaussianReal 0 1) (a := z)))

lemma normalTail_laplace (z : ℝ) :
    normalTail z = Real.exp (-(z ^ 2) / 2) * oneSidedLaplace (gaussianReal 0 1) z := by
  rw [normalTail_eq_measure, gaussian_right_tail_eq_laplace]

lemma normalTail_pos {z : ℝ} (hz : 0 ≤ z) : 0 < normalTail z := by
  rw [normalTail_laplace]
  apply mul_pos (Real.exp_pos _)
  apply lt_of_lt_of_le _ (gaussian_laplace_lower hz)
  positivity

end GaussianTilt.GaussianLaplace
