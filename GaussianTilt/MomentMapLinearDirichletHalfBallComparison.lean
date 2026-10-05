import GaussianTilt.MomentMapLinearDirichletEnergyFields
import GaussianTilt.MomentMapLinearDirichletEnergyComparisonConstants

/-! # Actual weak-jet one-step energy and normal-excess comparisons -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Actual replacement fields give the two integral recurrences with the
correction's genuine H₀¹ energy. No gradient equality is postulated; it
comes from AE linearity of the weak-jet coordinate field. -/
theorem halfBall_weak_jet_energy_excess_comparison [NeZero n]
    {Ω : Set (CoordinateSpace n)} (u : VolumeJet n) (w : dirichletSobolev Ω) (j : Fin n)
    {r R de dx : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R) (hde : 0 ≤ de) (hdx : 0 ≤ dx)
    (hEnergy : halfBallGradientEnergy (u-w.1) j r ≤ de*halfBallGradientEnergy (u-w.1) j R)
    (hExcess : ∃ t : ℝ,
      (∫ x in upperCampanatoBall j 0 r,
        ‖euclideanWeakGradient (u-w.1) x-t • EuclideanSpace.basisFun (Fin n) ℝ j‖^2) ≤
      dx*(∫ x in upperCampanatoBall j 0 R,
        ‖euclideanWeakGradient (u-w.1) x-halfBallMeanNormal u j R • EuclideanSpace.basisFun (Fin n) ℝ j‖^2)) :
    halfBallGradientEnergy u j r ≤ 4*de*halfBallGradientEnergy u j R+(4*de+2)*dirichletEnergy Ω w w ∧
    halfBallGradientExcess u j r ≤ 4*dx*halfBallGradientExcess u j R+(4*dx+2)*dirichletEnergy Ω w w := by
  haveI : Fact (volume (upperCampanatoBall j 0 R) < ∞) := ⟨(upperCampanatoBall_finite j 0 R).lt_top⟩
  haveI : Fact (volume (upperCampanatoBall j 0 r) < ∞) := ⟨(upperCampanatoBall_finite j 0 r).lt_top⟩
  haveI : NeZero (volume (upperCampanatoBall j 0 R)) := ⟨upperCampanatoBall_measure_ne_zero j hR⟩
  haveI : NeZero (volume (upperCampanatoBall j 0 r)) := ⟨upperCampanatoBall_measure_ne_zero j hr⟩
  have hsub : upperCampanatoBall j 0 r ⊆ upperCampanatoBall j 0 R :=
    upperCampanatoBall_mono (by simpa only [dist_self,zero_add] using hrR)
  obtain ⟨he,hx⟩ := boundary_energy_excess_comparison (Measure.restrict_mono_set volume hsub) j
    ((euclideanWeakGradient_memLp u).restrict (upperCampanatoBall j 0 R))
    ((euclideanWeakGradient_memLp (u-w.1)).restrict (upperCampanatoBall j 0 R))
    ((euclideanWeakGradient_memLp w.1).restrict (upperCampanatoBall j 0 R))
    (ae_restrict_of_ae (euclideanWeakGradient_decomposition u w.1)) hde hdx hEnergy hExcess
  change halfBallGradientEnergy u j r ≤ 4*de*halfBallGradientEnergy u j R+
    (4*de+2)*halfBallGradientEnergy w.1 j R at he
  change halfBallGradientExcess u j r ≤ 4*dx*halfBallGradientExcess u j R+
    (4*dx+2)*halfBallGradientEnergy w.1 j R at hx
  have hw := halfBallGradientEnergy_le_dirichletEnergy w j R
  exact ⟨he.trans (add_le_add_left (mul_le_mul_of_nonneg_left hw (by positivity)) _),
    hx.trans (add_le_add_left (mul_le_mul_of_nonneg_left hw (by positivity)) _)⟩

/-- The real weak-jet estimates combine with a real correction bound into
the precise pair of recurrence coefficients used by the proved iteration. -/
theorem halfBall_weak_jet_energy_excess_step [NeZero n]
    {Ω : Set (CoordinateSpace n)} (u : VolumeJet n) (w : dirichletSobolev Ω) (j : Fin n)
    {R θ Kh J δ F : ℝ} (hR : 0 < R) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hKh : 0 < Kh) (hJ : 0 ≤ J) (hF : 0 ≤ F)
    (hCorrector : dirichletEnergy Ω w w ≤ J*δ^2*halfBallGradientEnergy u j R+F)
    (hEnergy : halfBallGradientEnergy (u-w.1) j (θ*R) ≤
      (Kh*θ^n)*halfBallGradientEnergy (u-w.1) j R)
    (hExcess : ∃ t : ℝ,
      (∫ x in upperCampanatoBall j 0 (θ*R),
        ‖euclideanWeakGradient (u-w.1) x-t • EuclideanSpace.basisFun (Fin n) ℝ j‖^2) ≤
      (Kh*θ^(n+2))*(∫ x in upperCampanatoBall j 0 R,
        ‖euclideanWeakGradient (u-w.1) x-halfBallMeanNormal u j R • EuclideanSpace.basisFun (Fin n) ℝ j‖^2)) :
    let K := replacementIterationConstant Kh J
    halfBallGradientEnergy u j (θ*R) ≤ (K*θ^n+K*δ^2)*halfBallGradientEnergy u j R+(4*Kh+2)*F ∧
    halfBallGradientExcess u j (θ*R) ≤ K*θ^(n+2)*halfBallGradientExcess u j R+
      K*δ^2*halfBallGradientEnergy u j R+(4*Kh+2)*F := by
  have hh := halfBall_weak_jet_energy_excess_comparison u w j (mul_pos hθ hR) hR
    (by nlinarith : θ*R ≤ R) (by positivity) (by positivity) hEnergy hExcess
  exact absorb_energy_excess_replacement n (halfBallGradientEnergy_nonneg u j R)
    (halfBallGradientExcess_nonneg u j R) hKh hJ hθ.le hθ1 hF hCorrector hh.1 hh.2

end GaussianTilt.MomentMapLinearDirichlet
