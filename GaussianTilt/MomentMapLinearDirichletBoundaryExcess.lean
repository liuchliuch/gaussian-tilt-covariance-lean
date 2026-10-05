import GaussianTilt.MomentMapLinearDirichletEnergyConstants

/-! # The actual least-square normal affine boundary excess -/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Boundary affine comparisons preserve zero flat trace precisely when
their gradients are normal. Their scalar coefficient is an actual average. -/
def normalMean {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (j : Fin n) (G : X → KernelSpace n) : ℝ := ⨍ x, G x j ∂μ

lemma normal_error_integral_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] (j : Fin n) {G : X → KernelSpace n} (hG : MemLp G 2 μ) (t : ℝ) :
    (∫ x, ‖G x-t • EuclideanSpace.basisFun (Fin n) ℝ j‖^2 ∂μ) =
      (∫ x, ‖G x‖^2 ∂μ)-2*t*(∫ x, G x j ∂μ)+t^2*μ.real univ := by
  have hI : Integrable (fun x => ‖G x‖^2) μ := hG.integrable_norm_pow (p := 2) (by norm_num)
  have hj : MemLp (fun x => G x j) 2 μ := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).comp_memLp' hG
  have hjI : Integrable (fun x => G x j) μ := hj.integrable (by norm_num)
  have he (x : X) : ‖G x-t • EuclideanSpace.basisFun (Fin n) ℝ j‖^2 =
      ‖G x‖^2-(2*t)*(G x j)+t^2 := by
    rw [norm_sub_sq_real,real_inner_smul_right,EuclideanSpace.inner_basisFun_real,
      norm_smul,Real.norm_eq_abs,(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one,sq_abs]
    ring
  simp_rw [he]
  have hI1 : Integrable (fun x => ‖G x‖^2-(2*t)*G x j) μ := hI.sub (hjI.const_mul (2*t))
  have hI2 : Integrable (fun _ : X => t^2) μ := integrable_const _
  rw [integral_add hI1 hI2,
    integral_sub hI (hjI.const_mul (2*t)),integral_const_mul,integral_const]
  simp only [smul_eq_mul]
  ring

/-- The true scalar average minimizes the actual boundary-normal quadratic
error, with an exact nonnegative variance defect. -/
theorem normalMean_error_variance {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] [NeZero μ] (j : Fin n) {G : X → KernelSpace n}
    (hG : MemLp G 2 μ) (t : ℝ) :
    (∫ x, ‖G x-t • EuclideanSpace.basisFun (Fin n) ℝ j‖^2 ∂μ) =
      (∫ x, ‖G x-normalMean μ j G • EuclideanSpace.basisFun (Fin n) ℝ j‖^2 ∂μ)+
        μ.real univ*(t-normalMean μ j G)^2 := by
  have hmass : 0 < μ.real univ := measureReal_univ_pos
  have hm : normalMean μ j G * μ.real univ = ∫ x, G x j ∂μ := by
    rw [normalMean,average_eq,smul_eq_mul]
    field_simp
  rw [normal_error_integral_eq j hG t,normal_error_integral_eq j hG (normalMean μ j G)]
  rw [← hm]
  ring

theorem normalMean_minimizes_error {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] [NeZero μ] (j : Fin n) {G : X → KernelSpace n}
    (hG : MemLp G 2 μ) (t : ℝ) :
    (∫ x, ‖G x-normalMean μ j G • EuclideanSpace.basisFun (Fin n) ℝ j‖^2 ∂μ) ≤
      ∫ x, ‖G x-t • EuclideanSpace.basisFun (Fin n) ℝ j‖^2 ∂μ := by
  rw [normalMean_error_variance j hG t]
  exact le_add_of_nonneg_right (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))

end GaussianTilt.MomentMapLinearDirichlet
