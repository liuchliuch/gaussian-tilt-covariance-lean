import GaussianTilt.MomentMapLinearDirichletFrozenExcessGeometry

/-! # Exact local energy comparisons for the genuine affine gradient pullback -/
noncomputable section
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def fieldExcess (G : KernelSpace n → KernelSpace n) (S : Set (KernelSpace n)) (q : KernelSpace n) : ℝ :=
  ∫ x in S, ‖G x-q‖^2

lemma fieldExcess_nonneg (G : KernelSpace n → KernelSpace n) (S : Set (KernelSpace n)) (q : KernelSpace n) :
    0 ≤ fieldExcess G S q := integral_nonneg (fun _ => sq_nonneg _)

lemma integrableOn_fieldExcess {G : KernelSpace n → KernelSpace n} (hG : MemLp G 2 volume)
    {S : Set (KernelSpace n)} (hS : volume S < ⊤) (q : KernelSpace n) :
    IntegrableOn (fun x => ‖G x-q‖^2) S volume := by
  letI : Fact (volume S < ⊤) := ⟨hS⟩
  exact (((hG.mono_measure Measure.restrict_le_self).sub (memLp_const q)).norm).integrable_sq

lemma fieldExcess_mono_set {G : KernelSpace n → KernelSpace n} (hG : MemLp G 2 volume)
    {S T : Set (KernelSpace n)} (hT : volume T < ⊤) (hST : S ⊆ T) (q : KernelSpace n) :
    fieldExcess G S q ≤ fieldExcess G T q :=
  setIntegral_mono_set (integrableOn_fieldExcess hG hT q) (ae_of_all _ (fun _ => sq_nonneg _))
    (ae_of_all _ (fun _ hx => hST hx))

lemma affine_transformed_excess_bounds (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hP : ‖P.toContinuousLinearMap‖ ≤ M) (hI : ‖P.symm.toContinuousLinearMap‖ ≤ N)
    {G : KernelSpace n → KernelSpace n} (hG : MemLp G 2 volume)
    {S : Set (KernelSpace n)} (hSm : MeasurableSet S) (hSf : volume S < ⊤) (q : KernelSpace n) :
    fieldExcess (fun x => boundaryDualMap P (G x)) S (boundaryDualMap P q) ≤ M^2*fieldExcess G S q ∧
    fieldExcess G S q ≤ N^2*fieldExcess (fun x => boundaryDualMap P (G x)) S (boundaryDualMap P q) := by
  have hTG : MemLp (fun x => boundaryDualMap P (G x)) 2 volume := hG.continuousLinearMap_comp _
  have hGi := integrableOn_fieldExcess hG hSf q
  have hTGi := integrableOn_fieldExcess hTG hSf (boundaryDualMap P q)
  constructor
  · have hh := setIntegral_mono_on hTGi (hGi.const_mul (M^2)) hSm (fun x _ => by
      rw [← map_sub]
      have hb := (boundaryDualMap_norm_bounds P hP hI (G x-q)).1
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) hb 2])
    simpa only [integral_const_mul] using hh
  · have hh := setIntegral_mono_on hGi (hTGi.const_mul (N^2)) hSm (fun x _ => by
      rw [← map_sub]
      have hb := (boundaryDualMap_norm_bounds P hP hI (G x-q)).2
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) hb 2])
    simpa only [integral_const_mul] using hh

/-- The true Jacobian identity for the actual weak-gradient pullback on
any measurable subregion of the working chart. -/
lemma affine_fieldExcess_identity (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    {U V : KernelSpace n → KernelSpace n} {L : ℝ}
    (hVU : ∀ᵐ z ∂volume, z ∈ Metric.ball (0:KernelSpace n) L → V z=boundaryDualMap P (U (P z)))
    {S : Set (KernelSpace n)} (hS : MeasurableSet S)
    (hpre : P ⁻¹' S ⊆ Metric.ball (0:KernelSpace n) L) (q : KernelSpace n) :
    |P.toContinuousLinearMap.det| *fieldExcess V (P ⁻¹' S) (boundaryDualMap P q)=
      fieldExcess (fun x => boundaryDualMap P (U x)) S (boundaryDualMap P q) := by
  have hh := physical_affine_integral_preimage P hS (fun x => ‖boundaryDualMap P (U x)-boundaryDualMap P q‖^2)
  unfold fieldExcess
  rw [← hh]
  congr 1
  apply setIntegral_congr_ae (hS.preimage P.continuous.measurable)
  filter_upwards [hVU] with z hz hzS
  rw [hz (hpre hzS)]

end GaussianTilt.MomentMapLinearDirichlet
