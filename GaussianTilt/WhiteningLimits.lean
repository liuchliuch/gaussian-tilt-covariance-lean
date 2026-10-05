import GaussianTilt.Whitening
import GaussianTilt.MomentMapApproximation
import GaussianTilt.MomentBridge

/-! # Finite-second-moment truncations and covariance control

The convergence statements concern the explicitly constructed normalized
compact truncations. Their first and second moments, hence covariance,
converge by the proved dominated-convergence theorem.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace GaussianTilt.Whitening
open MomentMapApproximation

variable {n : ℕ}

lemma coordinate_second_growth (i : Fin n) (x : Reference.Space n) :
    ‖x i‖ ≤ 1 * (1 + ‖x‖ ^ 2) := by
  have h := PiLp.norm_apply_le x i
  nlinarith [sq_nonneg (‖x‖ - 1)]

lemma coordinate_product_second_growth (i j : Fin n) (x : Reference.Space n) :
    ‖x i * x j‖ ≤ 1 * (1 + ‖x‖ ^ 2) := by
  rw [norm_mul, one_mul]
  have h := mul_le_mul (PiLp.norm_apply_le x i) (PiLp.norm_apply_le x j)
    (norm_nonneg _) (norm_nonneg _)
  nlinarith

lemma meanVector_perturbedTruncation_tendsto (μ ν : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ)
    (hν : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) ν) :
    Tendsto (fun k ↦ meanVector (perturbedTruncation μ ν k) coordinates)
      atTop (𝓝 (meanVector μ coordinates)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact tendsto_integral_perturbedTruncation μ ν hμ hν
    (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i) (by norm_num)
    (coordinate_second_growth i)

lemma secondMoment_perturbedTruncation_tendsto (μ ν : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ)
    (hν : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) ν) :
    Tendsto (fun k ↦ secondMomentMatrix (perturbedTruncation μ ν k) coordinates)
      atTop (𝓝 (secondMomentMatrix μ coordinates)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_integral_perturbedTruncation μ ν hμ hν
    (by fun_prop) (by norm_num) (coordinate_product_second_growth i j)

lemma reference_covariance_perturbedTruncation_tendsto (μ ν : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ)
    (hν : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) ν) :
    Tendsto (fun k ↦ Reference.covariance (perturbedTruncation μ ν k))
      atTop (𝓝 (Reference.covariance μ)) := by
  have hm := meanVector_perturbedTruncation_tendsto μ ν hμ hν
  have hs := secondMoment_perturbedTruncation_tendsto μ ν hμ hν
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hs i)) j).sub
    ((tendsto_pi_nhds.mp hm i).mul (tendsto_pi_nhds.mp hm j))

lemma compact_coordinates_memLp {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (i : Fin n) :
    MemLp (fun x : Reference.Space n ↦ x i) 2 μ := by
  obtain ⟨P, rfl⟩ := exists_compactProbability_of_compactlySupported μ hc
  simpa only [P.tilt_zero] using P.memLp_continuous_tilt
    (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i) 0 2

lemma eventually_perturbedTruncation_covariance_posSemidef
    (μ ν : Measure (Reference.Space n)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∀ᶠ k in atTop, (Reference.covariance (perturbedTruncation μ ν k)).PosSemidef := by
  filter_upwards [eventually_perturbedTruncation_probability μ ν] with k hk
  letI := hk
  exact Reference.covariance_posSemidef
    (compact_coordinates_memLp (perturbedTruncation_compactlySupported μ ν k))

section MatrixLimits
variable {ι α : Type*} [Fintype ι] [DecidableEq ι]
  {l : Filter α} {C : α → Matrix ι ι ℝ}

lemma eventually_posDef_of_tendsto_one
    (hC : Tendsto C l (𝓝 1)) (hp : ∀ᶠ k in l, (C k).PosSemidef) :
    ∀ᶠ k in l, (C k).PosDef := by
  have hdet : Tendsto (fun k ↦ (C k).det) l (𝓝 (1 : ℝ)) := by
    simpa using (show Continuous (fun A : Matrix ι ι ℝ ↦ A.det) by fun_prop).continuousAt.tendsto.comp hC
  filter_upwards [hp, hdet.eventually (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))] with k hk hd
  exact hk.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))

lemma eventually_root_norm_le_two [Nonempty ι]
    (hC : Tendsto C l (𝓝 1)) (hp : ∀ᶠ k in l, (C k).PosSemidef) :
    ∀ᶠ k in l, ‖root (C k)‖ ≤ 2 := by
  have hn : Tendsto (fun k ↦ ‖C k‖) l (𝓝 (1 : ℝ)) := by simpa using hC.norm
  filter_upwards [hp, hn.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 4))] with k hk hn
  exact root_norm_le hk (by norm_num) (by norm_num; exact hn.le)

end MatrixLimits

lemma eventually_perturbedTruncation_covariance_posDef
    (μ ν : Measure (Reference.Space n)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ)
    (hν : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) ν)
    (hiso : Reference.isotropic μ) :
    ∀ᶠ k in atTop, (Reference.covariance (perturbedTruncation μ ν k)).PosDef := by
  apply eventually_posDef_of_tendsto_one _ (eventually_perturbedTruncation_covariance_posSemidef μ ν)
  rw [← hiso.2]
  exact reference_covariance_perturbedTruncation_tendsto μ ν hμ hν

lemma eventually_perturbedTruncation_root_norm_le_two [Nonempty (Fin n)]
    (μ ν : Measure (Reference.Space n)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) μ)
    (hν : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 2) ν)
    (hiso : Reference.isotropic μ) :
    ∀ᶠ k in atTop, ‖root (Reference.covariance (perturbedTruncation μ ν k))‖ ≤ 2 := by
  apply eventually_root_norm_le_two _ (eventually_perturbedTruncation_covariance_posSemidef μ ν)
  rw [← hiso.2]
  exact reference_covariance_perturbedTruncation_tendsto μ ν hμ hν

end GaussianTilt.Whitening
