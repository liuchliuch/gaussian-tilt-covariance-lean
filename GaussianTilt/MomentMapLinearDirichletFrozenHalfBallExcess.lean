import GaussianTilt.MomentMapLinearDirichletFrozenExcessTransport
import GaussianTilt.MomentMapLinearDirichletVariableWeakAffineCoordinates

/-! # Genuine frozen-SPD half-ball gradient excess decay

The normalization, weak affine pullback, Laplace reflection/decay and true
Jacobian cancellation are all constructed. Constants precede the frozen
matrix, the domain, the weak solution and the radius.
-/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma boundaryDualMap_apply (P : KernelSpace n ≃L[ℝ] KernelSpace n) (x : KernelSpace n) (i : Fin n) :
    boundaryDualMap P x i=∑ k, euclideanCLMMatrix P.toContinuousLinearMap k i*x k := by
  rw [← boundaryDualMap_matrix]
  have hh := congrFun (Matrix.ofLp_toEuclideanCLM ((euclideanCLMMatrix P.toContinuousLinearMap)ᵀ) x) i
  exact hh

lemma normalized_jet_euclidean_gradient (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    (u v : VolumeJet n) {L : ℝ}
    (hgrad : ∀ i, ∀ᵐ x ∂volume, x ∈ rawChartBall (n := n) L →
      v i.succ x=∑ k, euclideanCLMMatrix P.toContinuousLinearMap k i*u k.succ (rawBoundaryNormalization P x)) :
    ∀ᵐ z ∂volume, z ∈ Metric.ball (0:KernelSpace n) L →
      euclideanWeakGradient v z=boundaryDualMap P (euclideanWeakGradient u (P z)) := by
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  filter_upwards [hμ.quasiMeasurePreserving.ae (ae_all_iff.mpr hgrad)] with z hz hzB
  have hzraw : dirichletCoordinateEquiv n z ∈ rawChartBall (n := n) L := by
    change ‖z‖ < L
    simpa only [Metric.mem_ball,dist_zero_right] using hzB
  ext i
  rw [boundaryDualMap_apply]
  have hh := hz i hzraw
  change v i.succ (dirichletCoordinateEquiv n z)=∑ k, euclideanCLMMatrix P.toContinuousLinearMap k i*u k.succ
    (rawBoundaryNormalization P (dirichletCoordinateEquiv n z)) at hh
  simpa only [euclideanWeakGradient_apply,rawBoundaryNormalization_apply,
    show dirichletCoordinateEquiv n=GaussianTilt.MomentMapRegularity.coordinateEquiv n from rfl,
    ContinuousLinearEquiv.symm_apply_apply] using hh

/-- Genuine frozen-SPD excess decay on all sufficiently small half-balls,
with one true normal approximant and every normal comparison slope. -/
theorem exists_frozen_halfBall_gradient_excess_decay [NeZero n]
    {lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) :
    ∃ θ K : ℝ, 0 < θ ∧ θ ≤ 1/2 ∧ 0 < K ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosDef →
      (∀ v : KernelSpace n, lam*‖v‖^2 ≤ euclideanQuadratic B v) →
      (∀ v : KernelSpace n, euclideanQuadratic B v ≤ Λ*‖v‖^2) →
      ∀ (j : Fin n) (Ω : Set (CoordinateSpace n)), (Ω ⊆ {x | 0 < x j}) →
      ∀ u : dirichletSobolev Ω, ∀ R : ℝ, 0 < R →
      (∀ ξ : smoothCompactCore n, tsupport ξ.1 ⊆ coordinateHalfBall j R →
        (∫ x, (fun i : Fin n => u.1 i.succ x) ⬝ᵥ (B*ᵥcoordinateGradient ξ.1 x))=0) →
      ∃ p : KernelSpace n, (∀ i, i ≠ j → p i=0) ∧
        ∀ q : KernelSpace n, (∀ i, i ≠ j → q i=0) → ∀ r : ℝ, 0 < r → r ≤ θ*R →
          (∫ x in upperCampanatoBall j 0 r, ‖euclideanWeakGradient u.1 x-p‖^2) ≤
            K*(r/R)^(n+2)*(∫ x in upperCampanatoBall j 0 R, ‖euclideanWeakGradient u.1 x-q‖^2) := by
  obtain ⟨C,hC,hLaplace⟩ := exists_dirichletSobolev_halfBall_gradient_excess_decay (n := n)
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
  intro B hB hlo hhi j Ω hΩ u R hR heq
  obtain ⟨P,c,hc,hplane,hinv,hP₀,hI₀,hPDE,hPP⟩ := exists_quantitative_boundary_normalization j hB hlam hΛ hlo hhi
  have hP : ‖P.toContinuousLinearMap‖ ≤ M := hP₀.trans (le_max_right _ _)
  have hI : ‖P.symm.toContinuousLinearMap‖ ≤ N := hI₀.trans (le_max_right _ _)
  obtain ⟨v,hvalue,hgrad,harm⟩ := exists_kernel_normalized_harmonic_jet j hΩ P hc hM hR hP hplane hPP u heq
  obtain ⟨p,hp,hdec⟩ := hLaplace {x : CoordinateSpace n | 0 < x j}
    (isOpen_lt continuous_const (continuous_apply j)).measurableSet j (fun x hx => hx) v (R/M) (div_pos hR hM) harm
  have hgradE := normalized_jet_euclidean_gradient P u.1 v.1 hgrad
  have ht := affine_halfBall_excess_decay P j hc hM hN hR hC.le hP hI hplane
    (euclideanWeakGradient_memLp u.1) (euclideanWeakGradient_memLp v.1) hgradE hp hdec
  refine ⟨c⁻¹ • p,ht.1,?_⟩
  intro q hq r hr hrt
  have hrsmall : r ≤ R/(2*M*N) := by
    have heθ : θ*R=R/(2*M*N) := by dsimp [θ]; ring
    rwa [heθ] at hrt
  exact ht.2 q hq r hr hrsmall

end GaussianTilt.MomentMapLinearDirichlet
