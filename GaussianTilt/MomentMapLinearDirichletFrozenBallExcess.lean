import GaussianTilt.MomentMapLinearDirichletFrozenInteriorTransport
import GaussianTilt.MomentMapLinearDirichletFrozenHalfBallExcess
import GaussianTilt.MomentMapLinearDirichletVariableWeakAffineInterior
import GaussianTilt.MomentMapLinearDirichletH1InteriorGradient

/-! # Actual frozen-SPD full-ball excess at every center -/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma normalized_translated_jet_euclidean_gradient
    (P : KernelSpace n ≃L[ℝ] KernelSpace n) (a : KernelSpace n)
    (u v : VolumeJet n) {L : ℝ}
    (hgrad : ∀ i, ∀ᵐ x ∂volume, x ∈ rawChartBall (n := n) L →
      v i.succ x=∑ k, euclideanCLMMatrix P.toContinuousLinearMap k i*u k.succ
        (rawBoundaryNormalization P x+dirichletCoordinateEquiv n a)) :
    ∀ᵐ z ∂volume, z ∈ Metric.ball (0:KernelSpace n) L →
      euclideanWeakGradient v z=boundaryDualMap P (euclideanWeakGradient u (P z+a)) := by
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  filter_upwards [hμ.quasiMeasurePreserving.ae (ae_all_iff.mpr hgrad)] with z hz hzB
  have hzraw : dirichletCoordinateEquiv n z ∈ rawChartBall (n := n) L := by
    change ‖z‖ < L
    simpa only [Metric.mem_ball,dist_zero_right] using hzB
  ext i
  rw [boundaryDualMap_apply]
  have hh := hz i hzraw
  simpa only [euclideanWeakGradient_apply,rawBoundaryNormalization_apply,
    show dirichletCoordinateEquiv n=GaussianTilt.MomentMapRegularity.coordinateEquiv n from rfl,
    ContinuousLinearEquiv.symm_apply_apply,map_add] using hh

theorem exists_frozen_ball_gradient_excess_decay [NeZero n]
    {lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) :
    ∃ θ K : ℝ, 0 < θ ∧ θ ≤ 1/2 ∧ 0 < K ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosDef →
      (∀ v : KernelSpace n, lam*‖v‖^2 ≤ euclideanQuadratic B v) →
      (∀ v : KernelSpace n, euclideanQuadratic B v ≤ Λ*‖v‖^2) →
      ∀ (Ω : Set (CoordinateSpace n)) (u : dirichletSobolev Ω),
      ∀ a : KernelSpace n, ∀ R : ℝ, 0 < R →
      (∀ ξ : smoothCompactCore n, tsupport ξ.1 ⊆ (dirichletCoordinateEquiv n).symm ⁻¹' Metric.ball a R →
        (∫ x, (fun i : Fin n => u.1 i.succ x) ⬝ᵥ (B*ᵥcoordinateGradient ξ.1 x))=0) →
      ∃ p : KernelSpace n, ∀ q : KernelSpace n, ∀ r : ℝ, 0 < r → r ≤ θ*R →
        (∫ x in Metric.ball a r, ‖euclideanWeakGradient u.1 x-p‖^2) ≤
          K*(r/R)^(n+2)*(∫ x in Metric.ball a R, ‖euclideanWeakGradient u.1 x-q‖^2) := by
  obtain ⟨C,hC,hLaplace⟩ := exists_dirichletSobolev_ball_gradient_excess_decay (n := n)
  let M := max 1 (Real.sqrt Λ)
  let N := max 1 (Real.sqrt lam)⁻¹
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  have hN : 0 < N := zero_lt_one.trans_le (le_max_left _ _)
  let θ := 1/(2*M*N)
  let K := C*M^2*N^2*(M*N)^(n+2)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hθhalf : θ ≤ 1/2 := by
    have hMN : 1 ≤ M*N := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
    change 1/(2*M*N) ≤ 1/2
    apply (div_le_iff₀ (show 0 < 2*M*N by positivity)).mpr
    nlinarith
  refine ⟨θ,K,hθ,hθhalf,hK,?_⟩
  intro B hB hlo hhi Ω u a R hR heq
  obtain ⟨P,c,hc,hplane,hinv,hP₀,hI₀,hPDE,hPP⟩ := exists_quantitative_boundary_normalization (0:Fin n) hB hlam hΛ hlo hhi
  have hP : ‖P.toContinuousLinearMap‖ ≤ M := hP₀.trans (le_max_right _ _)
  have hI : ‖P.symm.toContinuousLinearMap‖ ≤ N := hI₀.trans (le_max_right _ _)
  have hPD : MapsTo (fun x => rawBoundaryNormalization P x+dirichletCoordinateEquiv n a)
      (rawChartBall (n := n) (R/M)) ((dirichletCoordinateEquiv n).symm ⁻¹' Metric.ball a R) := by
    intro x hx
    change ‖(dirichletCoordinateEquiv n).symm (rawBoundaryNormalization P x+dirichletCoordinateEquiv n a)-a‖ < R
    have he : (dirichletCoordinateEquiv n).symm (rawBoundaryNormalization P x+dirichletCoordinateEquiv n a)-a=
        P ((dirichletCoordinateEquiv n).symm x) := by
      change (GaussianTilt.MomentMapRegularity.coordinateEquiv n).symm
        (GaussianTilt.MomentMapRegularity.coordinateEquiv n (P ((GaussianTilt.MomentMapRegularity.coordinateEquiv n).symm x))+
          GaussianTilt.MomentMapRegularity.coordinateEquiv n a)-a=_
      rw [map_add,ContinuousLinearEquiv.symm_apply_apply,ContinuousLinearEquiv.symm_apply_apply,add_sub_cancel_right]
      rfl
    rw [he]
    have hnorm := (P.toContinuousLinearMap.le_opNorm ((dirichletCoordinateEquiv n).symm x)).trans
      (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
    change ‖(dirichletCoordinateEquiv n).symm x‖ < R/M at hx
    have hh := (lt_div_iff₀ hM).mp hx
    change ‖P ((dirichletCoordinateEquiv n).symm x)‖ ≤ M*‖(dirichletCoordinateEquiv n).symm x‖ at hnorm
    nlinarith only [hnorm,hh]
  obtain ⟨v,hvalue,hgrad,harm⟩ := exists_interior_affine_normalized_harmonic_jet (rawBoundaryNormalization P)
    (dirichletCoordinateEquiv n a) (div_pos hR hM) hPD (by simpa only [rawBoundaryNormalization_matrix] using hPP) u heq
  have hRaw : rawChartBall (n := n) (R/M)=(dirichletCoordinateEquiv n).symm ⁻¹' Metric.ball (0:KernelSpace n) (R/M) := by
    ext x
    change (‖(dirichletCoordinateEquiv n).symm x‖ < R/M) ↔ dist ((dirichletCoordinateEquiv n).symm x) 0 < R/M
    rw [dist_zero_right]
  obtain ⟨p,hdec⟩ := hLaplace univ v 0 (R/M) (div_pos hR hM) (by rw [← hRaw]; exact harm)
  have hgradE := normalized_translated_jet_euclidean_gradient P a u.1 v.1
    (by simpa only [rawBoundaryNormalization_matrix] using hgrad)
  have hUa : MemLp (fun x => euclideanWeakGradient u.1 (x+a)) 2 volume :=
    (euclideanWeakGradient_memLp u.1).comp_measurePreserving (measurePreserving_add_right volume a)
  have ht := affine_ball_excess_decay P hM hN hR hC.le hP hI hUa (euclideanWeakGradient_memLp v.1) hgradE hdec
  refine ⟨boundaryDualMap P.symm p,?_⟩
  intro q r hr hrt
  have hrsmall : r ≤ R/(2*M*N) := by
    have heθ : θ*R=R/(2*M*N) := by dsimp [θ]; ring
    rwa [heθ] at hrt
  have hh := ht q r hr hrsmall
  rw [fieldExcess_translate,fieldExcess_translate] at hh
  exact hh

end GaussianTilt.MomentMapLinearDirichlet
