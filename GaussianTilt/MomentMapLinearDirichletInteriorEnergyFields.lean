import GaussianTilt.MomentMapLinearDirichletEnergyFields
import GaussianTilt.MomentMapLinearDirichletInteriorExcess
import GaussianTilt.MomentMapLinearDirichletEnergyComparisonConstants

/-! # Genuine interior-ball weak energy, mean excess, and replacement comparison -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def ballGradientEnergy (u : VolumeJet n) (a : KernelSpace n) (r : ℝ) : ℝ :=
  ∫ x in Metric.ball a r, ‖euclideanWeakGradient u x‖^2

def ballMeanGradient (u : VolumeJet n) (a : KernelSpace n) (r : ℝ) : KernelSpace n :=
  ⨍ x in Metric.ball a r, euclideanWeakGradient u x

def ballGradientExcess (u : VolumeJet n) (a : KernelSpace n) (r : ℝ) : ℝ :=
  ∫ x in Metric.ball a r, ‖euclideanWeakGradient u x-ballMeanGradient u a r‖^2

lemma ballGradientEnergy_nonneg (u : VolumeJet n) (a : KernelSpace n) (r : ℝ) :
    0 ≤ ballGradientEnergy u a r := integral_nonneg (fun _ => sq_nonneg _)

lemma ballGradientExcess_nonneg (u : VolumeJet n) (a : KernelSpace n) (r : ℝ) :
    0 ≤ ballGradientExcess u a r := integral_nonneg (fun _ => sq_nonneg _)

lemma ballGradientEnergy_eq_local (u : VolumeJet n) (a : KernelSpace n) (r : ℝ) :
    ballGradientEnergy u a r =
      ∫ x in (dirichletCoordinateEquiv n).symm ⁻¹' Metric.ball a r, ∑ i : Fin n,(u i.succ x)^2 := by
  let Ω := (dirichletCoordinateEquiv n).symm ⁻¹' Metric.ball a r
  have hΩ : MeasurableSet Ω := Metric.isOpen_ball.measurableSet.preimage (dirichletCoordinateEquiv n).symm.continuous.measurable
  have he : (dirichletCoordinateEquiv n) ⁻¹' Ω=Metric.ball a r := by ext x; simp [Ω]
  have hh := euclideanWeakGradient_restricted_energy u Ω hΩ
  rw [he,restrictedJetGradientNorm_sq] at hh
  exact hh

lemma ballGradientExcess_le_error (u : VolumeJet n) (a : KernelSpace n) (r : ℝ) (p : KernelSpace n) :
    ballGradientExcess u a r ≤ ∫ x in Metric.ball a r, ‖euclideanWeakGradient u x-p‖^2 := by
  haveI : Fact (volume (Metric.ball a r) < ∞) := ⟨measure_ball_lt_top⟩
  exact average_minimizes_error ((euclideanWeakGradient_memLp u).restrict _) p

lemma ballGradientExcess_le_energy (u : VolumeJet n) (a : KernelSpace n) (r : ℝ) :
    ballGradientExcess u a r ≤ ballGradientEnergy u a r := by
  simpa only [sub_zero,ballGradientEnergy] using ballGradientExcess_le_error u a r 0

lemma ballGradientEnergy_mono (u : VolumeJet n) (a : KernelSpace n) {r R : ℝ} (hrR : r ≤ R) :
    ballGradientEnergy u a r ≤ ballGradientEnergy u a R := by
  apply setIntegral_mono_set ((euclideanWeakGradient_memLp u).integrable_norm_pow (p := 2) (by norm_num)).restrict
    (ae_of_all _ (fun x => sq_nonneg _))
  exact ae_of_all _ (fun x hx => Metric.ball_subset_ball hrR hx)

lemma ballGradientEnergy_le_dirichletEnergy {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (a : KernelSpace n) (r : ℝ) :
    ballGradientEnergy u.1 a r ≤ dirichletEnergy Ω u u := by
  rw [dirichletEnergy_eq_gradientNorm_sq,← integral_euclideanWeakGradient_sq]
  exact setIntegral_le_integral ((euclideanWeakGradient_memLp u.1).integrable_norm_pow (p := 2) (by norm_num))
    (ae_of_all _ (fun x => sq_nonneg _))

theorem ball_weak_jet_energy_excess_comparison
    {Ω : Set (CoordinateSpace n)} (u : VolumeJet n) (w : dirichletSobolev Ω) (a : KernelSpace n)
    {r R de dx : ℝ} (hrR : r ≤ R) (hde : 0 ≤ de) (hdx : 0 ≤ dx)
    (hEnergy : ballGradientEnergy (u-w.1) a r ≤ de*ballGradientEnergy (u-w.1) a R)
    (hExcess : ∃ p : KernelSpace n,
      (∫ x in Metric.ball a r, ‖euclideanWeakGradient (u-w.1) x-p‖^2) ≤
      dx*(∫ x in Metric.ball a R, ‖euclideanWeakGradient (u-w.1) x-ballMeanGradient u a R‖^2)) :
    ballGradientEnergy u a r ≤ 4*de*ballGradientEnergy u a R+(4*de+2)*dirichletEnergy Ω w w ∧
    ballGradientExcess u a r ≤ 4*dx*ballGradientExcess u a R+(4*dx+2)*dirichletEnergy Ω w w := by
  haveI : Fact (volume (Metric.ball a R) < ∞) := ⟨measure_ball_lt_top⟩
  haveI : Fact (volume (Metric.ball a r) < ∞) := ⟨measure_ball_lt_top⟩
  obtain ⟨he,hx⟩ := interior_energy_excess_comparison (Measure.restrict_mono_set volume (Metric.ball_subset_ball hrR))
    ((euclideanWeakGradient_memLp u).restrict (Metric.ball a R))
    ((euclideanWeakGradient_memLp (u-w.1)).restrict (Metric.ball a R))
    ((euclideanWeakGradient_memLp w.1).restrict (Metric.ball a R))
    (ae_restrict_of_ae (euclideanWeakGradient_decomposition u w.1)) hde hdx hEnergy hExcess
  change ballGradientEnergy u a r ≤ 4*de*ballGradientEnergy u a R+(4*de+2)*ballGradientEnergy w.1 a R at he
  change ballGradientExcess u a r ≤ 4*dx*ballGradientExcess u a R+(4*dx+2)*ballGradientEnergy w.1 a R at hx
  have hw := ballGradientEnergy_le_dirichletEnergy w a R
  exact ⟨he.trans (add_le_add_left (mul_le_mul_of_nonneg_left hw (by positivity)) _),
    hx.trans (add_le_add_left (mul_le_mul_of_nonneg_left hw (by positivity)) _)⟩

theorem ball_weak_jet_energy_excess_step
    {Ω : Set (CoordinateSpace n)} (u : VolumeJet n) (w : dirichletSobolev Ω) (a : KernelSpace n)
    {R θ Kh J δ F : ℝ} (hR : 0 < R) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hKh : 0 < Kh) (hJ : 0 ≤ J) (hF : 0 ≤ F)
    (hCorrector : dirichletEnergy Ω w w ≤ J*δ^2*ballGradientEnergy u a R+F)
    (hEnergy : ballGradientEnergy (u-w.1) a (θ*R) ≤ (Kh*θ^n)*ballGradientEnergy (u-w.1) a R)
    (hExcess : ∃ p : KernelSpace n,
      (∫ x in Metric.ball a (θ*R), ‖euclideanWeakGradient (u-w.1) x-p‖^2) ≤
      (Kh*θ^(n+2))*(∫ x in Metric.ball a R, ‖euclideanWeakGradient (u-w.1) x-ballMeanGradient u a R‖^2)) :
    let K := replacementIterationConstant Kh J
    ballGradientEnergy u a (θ*R) ≤ (K*θ^n+K*δ^2)*ballGradientEnergy u a R+(4*Kh+2)*F ∧
    ballGradientExcess u a (θ*R) ≤ K*θ^(n+2)*ballGradientExcess u a R+
      K*δ^2*ballGradientEnergy u a R+(4*Kh+2)*F := by
  have hh := ball_weak_jet_energy_excess_comparison u w a (by nlinarith : θ*R ≤ R)
    (by positivity) (by positivity) hEnergy hExcess
  exact absorb_energy_excess_replacement n (ballGradientEnergy_nonneg u a R)
    (ballGradientExcess_nonneg u a R) hKh hJ hθ.le hθ1 hF hCorrector hh.1 hh.2

end GaussianTilt.MomentMapLinearDirichlet
