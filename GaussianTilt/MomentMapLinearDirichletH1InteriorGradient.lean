import GaussianTilt.MomentMapLinearDirichletH1GradientHarmonic
import GaussianTilt.MomentMapLinearDirichletEuclideanWeakGradient

/-! # Literal interior harmonicity of the actual weak-gradient field -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma dirichletSobolev_physical_weak_harmonic_on {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) {V : Set (KernelSpace n)}
    (heq : ∀ v : dirichletSobolev ((dirichletCoordinateEquiv n).symm ⁻¹' V),
      (∑ i : Fin n, inner ℝ (u.1 i.succ) (v.1 i.succ))=0)
    {ψ : KernelSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψV : tsupport ψ ⊆ V) :
    (∫ x, dirichletValue Ω u (dirichletCoordinateEquiv n x)*kernelLaplacian ψ x)=0 := by
  let g : smoothCompactCore n := ⟨ψ ∘ (dirichletCoordinateEquiv n).symm,
    hψ.comp (dirichletCoordinateEquiv n).symm.contDiff,
    hψc.comp_homeomorph (dirichletCoordinateEquiv n).symm.toHomeomorph⟩
  have hgv : tsupport g.1 ⊆ (dirichletCoordinateEquiv n).symm ⁻¹' V :=
    fun x hx => hψV (tsupport_comp_dirichletCoordinateEquiv_symm hx)
  let v := dirichletCoreToSobolev _ ⟨g,hgv⟩
  have hh := heq v
  change (∑ i : Fin n, inner ℝ (u.1 i.succ) (smoothCompactToL2 volume (smoothCompactDerivative i g)))=0 at hh
  rw [dirichletSobolev_laplacian_pairing] at hh
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  rw [← hμ.integral_comp (dirichletCoordinateEquiv n).toHomeomorph.measurableEmbedding
    (fun y => dirichletValue Ω u y*euclideanLaplacian g.1 y)] at hh
  simp only [g,euclideanLaplacian_toLp_any,ContinuousLinearEquiv.symm_apply_apply] at hh
  linarith

/-- Each true weak-gradient component is harmonic in distributions on the
actual interior harmonicity region. No reflected or classical derivative
identification is used. -/
theorem dirichletSobolev_gradient_distribution_harmonic {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) {V : Set (KernelSpace n)}
    (heq : ∀ v : dirichletSobolev ((dirichletCoordinateEquiv n).symm ⁻¹' V),
      (∑ i : Fin n, inner ℝ (u.1 i.succ) (v.1 i.succ))=0) (i : Fin n) :
    ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ V → (∫ x, euclideanWeakGradient u.1 x i*kernelLaplacian ψ x)=0 := by
  intro ψ hψ hψc hψV
  have hh := dirichletSobolev_physical_integration_by_parts u i (smooth_kernelLaplacian hψ)
    (hasCompactSupport_kernelLaplacian hψc)
  rw [kernelDerivative_laplacian_commute hψ] at hh
  have hz := dirichletSobolev_physical_weak_harmonic_on u heq
    (smooth_kernelDirectionalDerivative hψ (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hψc.fderiv_apply (𝕜 := ℝ) _) ((tsupport_kernelDerivative_subset ψ _).trans hψV)
  rw [hz,neg_zero] at hh
  exact hh

/-- Actual interior H¹ harmonic replacements have the full-ball excess
estimate, for arbitrary centers and arbitrary comparison vectors. -/
theorem exists_dirichletSobolev_ball_gradient_excess_decay [NeZero n] :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Set (CoordinateSpace n)) (u : dirichletSobolev Ω),
      ∀ a : KernelSpace n, ∀ R : ℝ, 0 < R →
      (∀ v : dirichletSobolev ((dirichletCoordinateEquiv n).symm ⁻¹' Metric.ball a R),
        (∑ i : Fin n, inner ℝ (u.1 i.succ) (v.1 i.succ))=0) →
      ∃ p : KernelSpace n, ∀ q : KernelSpace n, ∀ r : ℝ, 0 < r → r ≤ R/2 →
        (∫ x in Metric.ball a r, ‖euclideanWeakGradient u.1 x-p‖^2) ≤
          C*(r/R)^(n+2)*(∫ x in Metric.ball a R, ‖euclideanWeakGradient u.1 x-q‖^2) := by
  obtain ⟨C,hC,hDecay⟩ := exists_harmonic_vector_L2_excess_decay (n := n)
  refine ⟨C,hC,?_⟩
  intro Ω u a R hR heq
  let G := euclideanWeakGradient u.1
  let H := fun x : KernelSpace n => (WithLp.toLp 2 (fun i => harmonicRepresentative (fun z => G z i) x) : KernelSpace n)
  have hLp (i : Fin n) : MemLp (fun z => G z i) 2 volume := euclideanWeakGradient_coordinate_memLp u.1 i
  have hRep (i : Fin n) : (fun x => H x i) =ᵐ[volume] (fun x => G x i) :=
    harmonicRepresentative_ae_eq ((hLp i).locallyIntegrable (by norm_num))
  have hHLp (i : Fin n) : MemLp (fun x => H x i) 2 volume := (memLp_congr_ae (hRep i)).mpr (hLp i)
  have hDist (i : Fin n) := dirichletSobolev_gradient_distribution_harmonic u heq i
  have hs (i : Fin n) (x : KernelSpace n) (hx : x ∈ Metric.ball a R) : ContDiffAt ℝ ∞ (fun z => H z i) x :=
    harmonicRepresentative_contDiffAt_of_L2_distribution_harmonic Metric.isOpen_ball (hLp i) (hDist i) x hx
  have hhar (i : Fin n) (x : KernelSpace n) (hx : x ∈ Metric.ball a R) : kernelLaplacian (fun z => H z i) x=0 :=
    harmonicRepresentative_laplacian_of_L2_distribution_harmonic Metric.isOpen_ball (hLp i) (hDist i) x hx
  have hAE : H =ᵐ[volume] G := by
    filter_upwards [ae_all_iff.mpr hRep] with x hx
    ext i
    exact hx i
  have hE (q : KernelSpace n) (r : ℝ) :
      (∫ x in Metric.ball a r, ‖H x-q‖^2)=∫ x in Metric.ball a r, ‖G x-q‖^2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hAE] with x hx
    rw [hx]
  refine ⟨H a,?_⟩
  intro q r hr hrR
  have hh := hDecay H hHLp a R hR hs hhar q r hr hrR
  rw [hE,hE] at hh
  exact hh

end GaussianTilt.MomentMapLinearDirichlet
