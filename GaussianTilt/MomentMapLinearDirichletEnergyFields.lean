import GaussianTilt.MomentMapLinearDirichletEuclideanWeakGradient
import GaussianTilt.MomentMapLinearDirichletBoundaryExcessComparison

/-! # Actual weak-gradient energy and minimizing normal excess on half-balls -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def halfBallGradientEnergy (u : VolumeJet n) (j : Fin n) (r : ℝ) : ℝ :=
  ∫ x in upperCampanatoBall j 0 r, ‖euclideanWeakGradient u x‖^2

def halfBallMeanNormal (u : VolumeJet n) (j : Fin n) (r : ℝ) : ℝ :=
  normalMean (volume.restrict (upperCampanatoBall j 0 r)) j (euclideanWeakGradient u)

def halfBallGradientExcess (u : VolumeJet n) (j : Fin n) (r : ℝ) : ℝ :=
  ∫ x in upperCampanatoBall j 0 r,
    ‖euclideanWeakGradient u x-halfBallMeanNormal u j r • EuclideanSpace.basisFun (Fin n) ℝ j‖^2

lemma halfBallGradientEnergy_nonneg (u : VolumeJet n) (j : Fin n) (r : ℝ) :
    0 ≤ halfBallGradientEnergy u j r := integral_nonneg (fun _ => sq_nonneg _)

lemma halfBallGradientExcess_nonneg (u : VolumeJet n) (j : Fin n) (r : ℝ) :
    0 ≤ halfBallGradientExcess u j r := integral_nonneg (fun _ => sq_nonneg _)

lemma halfBallGradientEnergy_eq_local (u : VolumeJet n) (j : Fin n) (r : ℝ) :
    halfBallGradientEnergy u j r = ∫ x in coordinateHalfBall j r, ∑ i : Fin n,(u i.succ x)^2 := by
  rw [halfBallGradientEnergy,euclideanWeakGradient_halfBall_energy,restrictedJetGradientNorm_sq]

lemma upperCampanatoBall_measure_ne_zero [NeZero n] (j : Fin n) {r : ℝ} (hr : 0 < r) :
    volume (upperCampanatoBall j 0 r) ≠ 0 := by
  have hm := upperCampanatoBall_volume_lower j 0 (by simp) hr
  have hp : 0 < volume.real (upperCampanatoBall j 0 r) :=
    (mul_pos campanatoHalfBallVolume_pos (pow_pos hr _)).trans_le hm
  intro hz
  simp only [measureReal_def,hz,ENNReal.toReal_zero] at hp
  exact lt_irrefl 0 hp

lemma halfBallGradientExcess_le_error [NeZero n] (u : VolumeJet n) (j : Fin n) {r : ℝ}
    (hr : 0 < r) (t : ℝ) :
    halfBallGradientExcess u j r ≤ ∫ x in upperCampanatoBall j 0 r,
      ‖euclideanWeakGradient u x-t • EuclideanSpace.basisFun (Fin n) ℝ j‖^2 := by
  haveI : Fact (volume (upperCampanatoBall j 0 r) < ∞) := ⟨(upperCampanatoBall_finite j 0 r).lt_top⟩
  haveI : NeZero (volume (upperCampanatoBall j 0 r)) := ⟨upperCampanatoBall_measure_ne_zero j hr⟩
  exact normalMean_minimizes_error j ((euclideanWeakGradient_memLp u).restrict _) t

lemma halfBallGradientExcess_le_energy [NeZero n] (u : VolumeJet n) (j : Fin n) {r : ℝ}
    (hr : 0 < r) : halfBallGradientExcess u j r ≤ halfBallGradientEnergy u j r := by
  simpa only [zero_smul,sub_zero,halfBallGradientEnergy] using halfBallGradientExcess_le_error u j hr 0

lemma euclideanWeakGradient_decomposition (u w : VolumeJet n) :
    ∀ᵐ x ∂volume, euclideanWeakGradient u x=euclideanWeakGradient (u-w) x+euclideanWeakGradient w x := by
  filter_upwards [euclideanWeakGradient_ae_sub u w] with x hx
  rw [hx]
  abel

lemma integral_euclideanWeakGradient_sq (u : VolumeJet n) :
    (∫ x, ‖euclideanWeakGradient u x‖^2) = (jetGradientNorm u)^2 := by
  rw [jetGradientNorm_sq]
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  simp_rw [euclideanWeakGradient_norm_sq]
  have hc := hμ.integral_comp (dirichletCoordinateEquiv n).toHomeomorph.measurableEmbedding
    (fun y : CoordinateSpace n => ∑ i : Fin n,(u i.succ y)^2)
  change (∫ x, ∑ i : Fin n,(u i.succ (dirichletCoordinateEquiv n x))^2) =
    (∫ y, ∑ i : Fin n,(u i.succ y)^2) at hc
  rw [hc]
  rw [integral_finset_sum _ (fun i _ => (Lp.memLp (u i.succ)).integrable_sq)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by simp only [RCLike.inner_apply,conj_trivial]; ring)

lemma halfBallGradientEnergy_le_dirichletEnergy {Ω : Set (CoordinateSpace n)}
    (w : dirichletSobolev Ω) (j : Fin n) (r : ℝ) :
    halfBallGradientEnergy w.1 j r ≤ dirichletEnergy Ω w w := by
  rw [dirichletEnergy_eq_gradientNorm_sq,← integral_euclideanWeakGradient_sq]
  have hI := (euclideanWeakGradient_memLp w.1).integrable_norm_pow (p := 2) (by norm_num)
  exact setIntegral_le_integral hI (ae_of_all _ (fun _ => sq_nonneg _))

end GaussianTilt.MomentMapLinearDirichlet
