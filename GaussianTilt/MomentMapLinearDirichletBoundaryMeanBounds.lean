import GaussianTilt.MomentMapLinearDirichletCampanatoUniformCoefficients
import GaussianTilt.MomentMapLinearDirichletBoundaryExcess

/-! # Uniform actual normal means from excess decay and one energy bound -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma normalMean_abs_le_sqrt_energy {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] [NeZero μ] (j : Fin n)
    {G : X → KernelSpace n} (hG : MemLp G 2 μ) {v M : ℝ} (hv : 0 < v)
    (hvol : v ≤ μ.real univ) (hE : (∫ x, ‖G x‖^2 ∂μ) ≤ M) :
    |normalMean μ j G| ≤ Real.sqrt (M/v) := by
  have he := normalMean_error_variance j hG 0
  simp only [zero_smul,sub_zero,zero_sub,neg_sq] at he
  have hi : 0 ≤ ∫ x, ‖G x-normalMean μ j G • EuclideanSpace.basisFun (Fin n) ℝ j‖^2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  apply Real.abs_le_sqrt
  apply (le_div_iff₀ hv).mpr
  nlinarith [mul_le_mul_of_nonneg_right hvol (sq_nonneg (normalMean μ j G))]

lemma upperCampanatoBall_measure_ne_zero_of_nonneg_center [NeZero n]
    (j : Fin n) (x : KernelSpace n) (hx : 0 ≤ x j) {r : ℝ} (hr : 0 < r) :
    volume (upperCampanatoBall j x r) ≠ 0 := by
  have hm := upperCampanatoBall_volume_lower j x hx hr
  have hp : 0 < volume.real (upperCampanatoBall j x r) :=
    (mul_pos campanatoHalfBallVolume_pos (pow_pos hr _)).trans_le hm
  intro hz
  simp only [measureReal_def,hz,ENNReal.toReal_zero] at hp
  exact lt_irrefl 0 hp

/-- Constants are chosen before the center and the field. Positive decay of
the genuine minimizing excess prevents blowup of all normal means. -/
theorem exists_uniform_normalMean_bound [NeZero n]
    {R C β M : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hβ : 0 < β) (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (j : Fin n) (z : KernelSpace n), 0 ≤ z j →
      ∀ (G : KernelSpace n → KernelSpace n),
      MemLp G 2 (volume.restrict (upperCampanatoBall j z R)) →
      (∫ x in upperCampanatoBall j z R, ‖G x‖^2) ≤ M →
      (∀ r, 0 < r → r ≤ R →
        (∫ x in upperCampanatoBall j z r,
          ‖G x-normalMean (volume.restrict (upperCampanatoBall j z r)) j G •
            EuclideanSpace.basisFun (Fin n) ℝ j‖^2) ≤ C*r^((n:ℝ)+β)) →
      ∀ r, 0 < r → r ≤ R →
        |normalMean (volume.restrict (upperCampanatoBall j z r)) j G| ≤ L := by
  let B := Real.sqrt (M/(campanatoHalfBallVolume n*R^n))
  obtain ⟨L,hL,hbound⟩ := exists_uniform_campanato_coefficient_bound
    (n := n) (F := KernelSpace n) hR hC (half_pos hβ) (Real.sqrt_nonneg (M/(campanatoHalfBallVolume n*R^n)))
  refine ⟨L,hL,?_⟩
  intro j z hz G hG hEnergy hExcess
  let p := fun r => normalMean (volume.restrict (upperCampanatoBall j z r)) j G •
    EuclideanSpace.basisFun (Fin n) ℝ j
  have hp (r : ℝ) : ‖p r‖ = |normalMean (volume.restrict (upperCampanatoBall j z r)) j G| := by
    dsimp [p]
    rw [norm_smul,Real.norm_eq_abs,(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one]
  have hsub {r : ℝ} (hrR : r ≤ R) : upperCampanatoBall j z r ⊆ upperCampanatoBall j z R :=
    upperCampanatoBall_mono (by simpa only [dist_self,zero_add] using hrR)
  have hpR : ‖p R‖ ≤ B := by
    haveI : Fact (volume (upperCampanatoBall j z R) < ∞) := ⟨(upperCampanatoBall_finite j z R).lt_top⟩
    haveI : NeZero (volume (upperCampanatoBall j z R)) :=
      ⟨upperCampanatoBall_measure_ne_zero_of_nonneg_center j z hz hR⟩
    rw [hp]
    apply normalMean_abs_le_sqrt_energy j hG (mul_pos campanatoHalfBallVolume_pos (pow_pos hR _))
    · simpa only [measureReal_restrict_apply_univ] using upperCampanatoBall_volume_lower j z hz hR
    · exact hEnergy
  have hI : ∀ r, 0 < r → r ≤ R → IntegrableOn (fun x => ‖G x-p r‖^2) (upperCampanatoBall j z r) := by
    intro r hr hrR
    haveI : Fact (volume (upperCampanatoBall j z r) < ∞) := ⟨(upperCampanatoBall_finite j z r).lt_top⟩
    exact ((hG.mono_measure (Measure.restrict_mono (hsub hrR) le_rfl)).sub (memLp_const (p r))).integrable_norm_pow (p := 2) (by norm_num)
  have hE : ∀ r, 0 < r → r ≤ R →
      (∫ x in upperCampanatoBall j z r, ‖G x-p r‖^2) ≤ C*r^((n:ℝ)+2*(β/2)) := by
    intro r hr hrR
    convert hExcess r hr hrR using 1 <;> congr 2 <;> ring
  intro r hr hrR
  rw [← hp]
  exact hbound j z hz G p hpR hI hE r hr hrR

end GaussianTilt.MomentMapLinearDirichlet
