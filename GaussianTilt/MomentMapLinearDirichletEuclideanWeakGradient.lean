import GaussianTilt.MomentMapLinearDirichletRestrictedEnergy
import GaussianTilt.MomentMapLinearDirichletHarmonicL2Decay

/-! # One actual Euclidean weak-gradient field and its exact local energy -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def euclideanWeakGradient (u : VolumeJet n) (x : KernelSpace n) : KernelSpace n :=
  WithLp.toLp 2 (fun i => u i.succ (dirichletCoordinateEquiv n x))

@[simp] lemma euclideanWeakGradient_apply (u : VolumeJet n) (x : KernelSpace n) (i : Fin n) :
    euclideanWeakGradient u x i=u i.succ (dirichletCoordinateEquiv n x) := rfl

lemma euclideanWeakGradient_coordinate_memLp (u : VolumeJet n) (i : Fin n) :
    MemLp (fun x => euclideanWeakGradient u x i) 2 volume :=
  (Lp.memLp (u i.succ)).comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin n))

lemma euclideanWeakGradient_memLp (u : VolumeJet n) : MemLp (euclideanWeakGradient u) 2 volume :=
  memLp_piLp_iff.mpr (euclideanWeakGradient_coordinate_memLp u)

lemma euclideanWeakGradient_ae_sub (u v : VolumeJet n) :
    euclideanWeakGradient (u-v) =ᵐ[volume] (fun x => euclideanWeakGradient u x-euclideanWeakGradient v x) := by
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have he : ∀ᵐ y ∂(volume : Measure (CoordinateSpace n)), ∀ i : Fin n,
      (u i.succ-v i.succ) y=u i.succ y-v i.succ y :=
    ae_all_iff.mpr (fun i => Lp.coeFn_sub (u i.succ) (v i.succ))
  filter_upwards [hμ.quasiMeasurePreserving.ae he] with x hx
  ext i
  exact hx i

lemma euclideanWeakGradient_norm_sq (u : VolumeJet n) (x : KernelSpace n) :
    ‖euclideanWeakGradient u x‖^2=∑ i : Fin n, (u i.succ (dirichletCoordinateEquiv n x))^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [euclideanWeakGradient_apply,Real.norm_eq_abs,sq_abs]

/-- Exact actual unit-Jacobian transport, valid for every measurable raw
region, identifies the local weak energy used in both proof lanes. -/
theorem euclideanWeakGradient_restricted_energy (u : VolumeJet n)
    (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω) :
    (∫ x in (dirichletCoordinateEquiv n) ⁻¹' Ω, ‖euclideanWeakGradient u x‖^2)=
      (restrictedJetGradientNorm Ω hΩ u)^2 := by
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  rw [restrictedJetGradientNorm_sq,← integral_indicator hΩ,
    ← integral_indicator (hΩ.preimage (dirichletCoordinateEquiv n).continuous.measurable)]
  have he : ((dirichletCoordinateEquiv n) ⁻¹' Ω).indicator (fun x => ‖euclideanWeakGradient u x‖^2)=
      (fun x => Ω.indicator (fun y => ∑ i : Fin n, (u i.succ y)^2) (dirichletCoordinateEquiv n x)) := by
    funext x
    by_cases hx : dirichletCoordinateEquiv n x ∈ Ω
    · rw [indicator_of_mem (show x ∈ (dirichletCoordinateEquiv n) ⁻¹' Ω from hx),indicator_of_mem hx,euclideanWeakGradient_norm_sq]
    · rw [indicator_of_notMem (show x ∉ (dirichletCoordinateEquiv n) ⁻¹' Ω from hx),indicator_of_notMem hx]
  rw [he,hμ.integral_comp (dirichletCoordinateEquiv n).toHomeomorph.measurableEmbedding]

lemma euclideanWeakGradient_halfBall_energy (u : VolumeJet n) (j : Fin n) (R : ℝ) :
    (∫ x in upperCampanatoBall j 0 R, ‖euclideanWeakGradient u x‖^2)=
      (restrictedJetGradientNorm (coordinateHalfBall j R) (isOpen_coordinateHalfBall j R).measurableSet u)^2 := by
  have he : (dirichletCoordinateEquiv n) ⁻¹' coordinateHalfBall j R=upperCampanatoBall j 0 R := by
    ext x
    simp only [mem_preimage,coordinateHalfBall,upperCampanatoBall,mem_inter_iff,mem_setOf_eq,
      Metric.mem_ball,dist_zero_right,ContinuousLinearEquiv.symm_apply_apply]
    rfl
  rw [← he]
  exact euclideanWeakGradient_restricted_energy u _ (isOpen_coordinateHalfBall j R).measurableSet

end GaussianTilt.MomentMapLinearDirichlet
