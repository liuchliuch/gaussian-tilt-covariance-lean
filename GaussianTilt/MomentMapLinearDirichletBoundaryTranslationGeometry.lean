import GaussianTilt.MomentMapLinearDirichletVariableEquationTranslation
import GaussianTilt.MomentMapLinearDirichletEnergyFields
import GaussianTilt.MomentMapLinearDirichletVariableWeakTangentialLoad

/-! # Actual boundary-centered weak-gradient integral transport -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma translated_upperCampanatoBall_preimage (j : Fin n) (a : KernelSpace n) (ha : a j=0) (r : ℝ) :
    (fun x : KernelSpace n=>x+a) ⁻¹' upperCampanatoBall j a r=upperCampanatoBall j 0 r := by
  ext x
  simp only [upperCampanatoBall,mem_preimage,mem_inter_iff,Metric.mem_ball,dist_eq_norm,
    add_sub_cancel_right,sub_zero,mem_setOf_eq,PiLp.add_apply,ha,add_zero]

lemma integral_translate_upperCampanatoBall {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : Fin n) (a : KernelSpace n) (ha : a j=0) (r : ℝ) (f : KernelSpace n → F) :
    (∫ x in upperCampanatoBall j 0 r,f (x+a))=∫ x in upperCampanatoBall j a r,f x := by
  have hμ := measurePreserving_add_right (volume : Measure (KernelSpace n)) a
  have hh := hμ.setIntegral_preimage_emb (Homeomorph.addRight a).measurableEmbedding
    f (upperCampanatoBall j a r)
  rwa [translated_upperCampanatoBall_preimage j a ha r] at hh

lemma euclideanWeakGradient_translate_upper_error (u : VolumeJet n) (j : Fin n)
    (a : KernelSpace n) (ha : a j=0) (r : ℝ) (p : KernelSpace n) :
    (∫ x in upperCampanatoBall j 0 r,
      ‖euclideanWeakGradient (volumeTranslateJet (dirichletCoordinateEquiv n a) u) x-p‖^2)=
    ∫ x in upperCampanatoBall j a r, ‖euclideanWeakGradient u x-p‖^2 := by
  calc
    _ = ∫ x in upperCampanatoBall j 0 r, ‖euclideanWeakGradient u (x+a)-p‖^2 := by
      apply setIntegral_congr_ae (isOpen_upperCampanatoBall j 0 r).measurableSet
      filter_upwards [euclideanWeakGradient_volumeTranslate_ae (dirichletCoordinateEquiv n a) u] with x hx hxs
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using congrArg (fun z => ‖z-p‖^2) hx
    _ = _ := integral_translate_upperCampanatoBall j a ha r (fun x=>‖euclideanWeakGradient u x-p‖^2)

lemma translated_halfBall_excess_bounds_original_mean [NeZero n] (u : VolumeJet n) (j : Fin n)
    (a : KernelSpace n) (ha : a j=0) {r : ℝ} (hr : 0 < r) :
    (∫ x in upperCampanatoBall j a r,
      ‖euclideanWeakGradient u x-normalMean (volume.restrict (upperCampanatoBall j a r)) j
        (euclideanWeakGradient u) • EuclideanSpace.basisFun (Fin n) ℝ j‖^2) ≤
      halfBallGradientExcess (volumeTranslateJet (dirichletCoordinateEquiv n a) u) j r := by
  have hpos : volume (upperCampanatoBall j a r) ≠ 0 := by
    have hm := upperCampanatoBall_volume_lower j a (by rw [ha]) hr
    have hp : 0 < volume.real (upperCampanatoBall j a r) :=
      (mul_pos campanatoHalfBallVolume_pos (pow_pos hr _)).trans_le hm
    intro hz
    simp only [measureReal_def,hz,ENNReal.toReal_zero] at hp
    exact lt_irrefl 0 hp
  haveI : Fact (volume (upperCampanatoBall j a r)<∞) := ⟨(upperCampanatoBall_finite j a r).lt_top⟩
  haveI : NeZero (volume (upperCampanatoBall j a r)) := ⟨hpos⟩
  have hh := normalMean_minimizes_error j ((euclideanWeakGradient_memLp u).restrict (upperCampanatoBall j a r))
    (halfBallMeanNormal (volumeTranslateJet (dirichletCoordinateEquiv n a) u) j r)
  rw [← euclideanWeakGradient_translate_upper_error u j a ha r
    (halfBallMeanNormal (volumeTranslateJet (dirichletCoordinateEquiv n a) u) j r • EuclideanSpace.basisFun (Fin n) ℝ j)] at hh
  exact hh

lemma dirichletEnergy_translated {Ω : Set (CoordinateSpace n)} (u : dirichletSobolev Ω)
    (a : CoordinateSpace n) :
    dirichletEnergy ((fun x=>x+a) ⁻¹' Ω)
      ⟨volumeTranslateJet a u.1,volumeTranslateJet_mem_dirichlet a u⟩
      ⟨volumeTranslateJet a u.1,volumeTranslateJet_mem_dirichlet a u⟩ = dirichletEnergy Ω u u := by
  rw [dirichletEnergy_eq_gradientNorm_sq,dirichletEnergy_eq_gradientNorm_sq,jetGradientNorm_volumeTranslateJet]

end GaussianTilt.MomentMapLinearDirichlet
