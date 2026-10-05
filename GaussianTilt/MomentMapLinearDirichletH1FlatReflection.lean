import GaussianTilt.MomentMapLinearDirichletH1FlatEquation
import GaussianTilt.MomentMapLinearDirichletFlatWeakReflection

/-! # Genuine weak odd reflection of an H₀¹ harmonic replacement

The zero-flat-trace input is the actual Sobolev closure class on an outer
upper domain. Harmonicity is required only on the smaller half-ball.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma flatOddExtension_distribution_harmonic_of_plane_zero_tests
    (j : Fin n) {u : KernelSpace n → ℝ} (hu : MemLp u 2 volume) {R : ℝ}
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R → (∀ x, x j=0 → ψ x=0) →
      (∫ x, u x*kernelLaplacian ψ x)=0) :
    ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
      (∫ x, flatOddExtension j u x*kernelLaplacian ψ x)=0 := by
  intro ψ hψ hψc hψR
  have hui := hu.locallyIntegrable (by norm_num)
  have huTi := (hu.comp_measurePreserving (flatReflection j).measurePreserving).locallyIntegrable (by norm_num)
  have hψT : ContDiff ℝ ∞ (ψ ∘ flatReflection j) := hψ.comp (flatReflection j).toContinuousLinearEquiv.contDiff
  have hψTc : HasCompactSupport (ψ ∘ flatReflection j) := hψc.comp_homeomorph (flatReflection j).toHomeomorph
  have hψ2 := contDiff_infty.mp hψ 2
  have hψT2 := contDiff_infty.mp hψT 2
  have hi1 := integrable_locally_mul_laplacian hui hψ2 hψc
  have hi2 := integrable_locally_mul_laplacian huTi hψ2 hψc
  have hi3 := integrable_locally_mul_laplacian hui hψT2 hψTc
  dsimp only [Function.comp_def] at hi2
  have hchange : (∫ x, u (flatReflection j x)*kernelLaplacian ψ x)=
      ∫ x, u x*kernelLaplacian (ψ ∘ flatReflection j) x := by
    have hh := (flatReflection j).measurePreserving.integral_comp
      (flatReflection j).toHomeomorph.measurableEmbedding
      (fun x => u (flatReflection j x)*kernelLaplacian ψ x)
    have hTT (x : KernelSpace n) : flatReflection j (flatReflection j x)=x := flatReflection_involutive j x
    simpa only [hTT,kernelLaplacian_flatReflection hψ2] using hh.symm
  have ht := heq (oddReflectionTest j ψ) (contDiff_oddReflectionTest j hψ)
    (hasCompactSupport_oddReflectionTest j hψc) (tsupport_oddReflectionTest_subset_ball j hψR)
    (fun x hx => oddReflectionTest_zero_on_plane j ψ hx)
  have hlap (x : KernelSpace n) : kernelLaplacian (oddReflectionTest j ψ) x=
      kernelLaplacian ψ x-kernelLaplacian (ψ ∘ flatReflection j) x := kernelLaplacian_sub_C2 hψ2 hψT2 x
  simp_rw [hlap,mul_sub] at ht
  rw [integral_sub hi1 hi3] at ht
  simp only [flatOddExtension,sub_mul]
  rw [integral_sub hi1 hi2,hchange]
  exact ht

/-- Odd reflection of the literal value coordinate of an actual H₀¹ jet
is distribution-harmonic on the full ball. There is no pointwise boundary
value, height bound, or classical regularity assumption. -/
theorem dirichletSobolev_odd_distribution_harmonic
    {Ω : Set (CoordinateSpace n)} (hΩ : MeasurableSet Ω) (j : Fin n)
    (hupper : ∀ x ∈ Ω, 0 < x j) (u : dirichletSobolev Ω) {R : ℝ}
    (heq : ∀ v : dirichletSobolev (coordinateHalfBall j R),
      (∑ i : Fin n, inner ℝ (u.1 i.succ) (v.1 i.succ))=0) :
    let h := fun x : KernelSpace n => dirichletValue Ω u (dirichletCoordinateEquiv n x)
    MemLp (flatOddExtension j h) 2 volume ∧
      ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball 0 R →
        (∫ x, flatOddExtension j h x*kernelLaplacian ψ x)=0 := by
  dsimp only
  have hu : MemLp (fun x => dirichletValue Ω u (dirichletCoordinateEquiv n x)) 2 volume :=
    (Lp.memLp (dirichletValue Ω u)).comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin n))
  refine ⟨flatOddExtension_memLp j hu,?_⟩
  apply flatOddExtension_distribution_harmonic_of_plane_zero_tests j hu
  intro ψ hψ hψc hψR hψ0
  exact dirichletSobolev_flat_zero_test hΩ j hupper u heq hψ hψc hψR hψ0

end GaussianTilt.MomentMapLinearDirichlet
