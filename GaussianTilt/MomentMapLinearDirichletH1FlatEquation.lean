import GaussianTilt.MomentMapLinearDirichletH1FlatAdmissibility
import GaussianTilt.MomentMapLinearDirichletH1ZeroExtension
import GaussianTilt.MomentMapLinearDirichletCoordinates
import GaussianTilt.MomentMapLinearDirichletHalfBallGeometry

/-! # Literal Euclidean weak identities from the full H₀¹ jet -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma coordinateDerivative_toLp_any (ψ : KernelSpace n → ℝ) (i : Fin n) (x : KernelSpace n) :
    coordinateDerivative i (ψ ∘ (dirichletCoordinateEquiv n).symm) (dirichletCoordinateEquiv n x)=
      kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x := by
  have hh := kernelDirectionalDerivative_ofLp_any (ψ ∘ (dirichletCoordinateEquiv n).symm) i x
  have he : ((ψ ∘ (dirichletCoordinateEquiv n).symm) ∘ dirichletCoordinateEquiv n)=ψ := by funext y; simp
  rw [he] at hh
  exact hh.symm

lemma dirichletSobolev_physical_gradient_pairing {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) {ψ : KernelSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    (∑ i, ∫ x, u.1 i.succ (dirichletCoordinateEquiv n x)*
      kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x)=
      -(∫ x, dirichletValue Ω u (dirichletCoordinateEquiv n x)*kernelLaplacian ψ x) := by
  let g : smoothCompactCore n := ⟨ψ ∘ (dirichletCoordinateEquiv n).symm,
    hψ.comp (dirichletCoordinateEquiv n).symm.contDiff,
    hψc.comp_homeomorph (dirichletCoordinateEquiv n).symm.toHomeomorph⟩
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have hi (i : Fin n) : inner ℝ (u.1 i.succ) (smoothCompactToL2 volume (smoothCompactDerivative i g))=
      ∫ x, u.1 i.succ (dirichletCoordinateEquiv n x)*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x := by
    rw [inner_Lp_smoothCompactToL2]
    change (∫ y, u.1 i.succ y*coordinateDerivative i (ψ ∘ (dirichletCoordinateEquiv n).symm) y)=_
    rw [← hμ.integral_comp (dirichletCoordinateEquiv n).toHomeomorph.measurableEmbedding]
    simp only [coordinateDerivative_toLp_any]
  have hh := dirichletSobolev_laplacian_pairing u g
  simp_rw [hi] at hh
  rw [← hμ.integral_comp (dirichletCoordinateEquiv n).toHomeomorph.measurableEmbedding
    (fun y => dirichletValue Ω u y*euclideanLaplacian g.1 y)] at hh
  simpa only [g,euclideanLaplacian_toLp_any,ContinuousLinearEquiv.symm_apply_apply] using hh

lemma dirichletSobolev_physical_weak_harmonic {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (j : Fin n) {R : ℝ}
    (heq : ∀ v : dirichletSobolev (coordinateHalfBall j R),
      (∑ i : Fin n, inner ℝ (u.1 i.succ) (v.1 i.succ))=0)
    {ψ : KernelSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Metric.ball 0 R ∩ {x | 0 < x j}) :
    (∑ i, ∫ x, u.1 i.succ (dirichletCoordinateEquiv n x)*
      kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x)=0 := by
  let g : smoothCompactCore n := ⟨ψ ∘ (dirichletCoordinateEquiv n).symm,
    hψ.comp (dirichletCoordinateEquiv n).symm.contDiff,
    hψc.comp_homeomorph (dirichletCoordinateEquiv n).symm.toHomeomorph⟩
  have hgΩ : tsupport g.1 ⊆ coordinateHalfBall j R := by
    intro x hx
    have hh := hψΩ (tsupport_comp_dirichletCoordinateEquiv_symm hx)
    exact ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hh.1,hh.2⟩
  let v : dirichletSobolev (coordinateHalfBall j R) := dirichletCoreToSobolev _ ⟨g,hgΩ⟩
  have hh := heq v
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have hi (i : Fin n) : inner ℝ (u.1 i.succ) (v.1 i.succ)=
      ∫ x, u.1 i.succ (dirichletCoordinateEquiv n x)*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x := by
    change inner ℝ (u.1 i.succ) (smoothCompactToL2 volume (smoothCompactDerivative i g))=_
    rw [inner_Lp_smoothCompactToL2]
    change (∫ y, u.1 i.succ y*coordinateDerivative i (ψ ∘ (dirichletCoordinateEquiv n).symm) y)=_
    rw [← hμ.integral_comp (dirichletCoordinateEquiv n).toHomeomorph.measurableEmbedding]
    simp only [coordinateDerivative_toLp_any]
  simpa only [hi] using hh

/-- A genuine H₀¹ jet on an outer upper domain admits every smooth compact
plane-zero test on the smaller harmonic half-ball. No growth or pointwise
boundary regularity of the weak solution is assumed. -/
theorem dirichletSobolev_flat_zero_test {Ω : Set (CoordinateSpace n)}
    (hΩ : MeasurableSet Ω) (j : Fin n) (hupper : ∀ x ∈ Ω, 0 < x j)
    (u : dirichletSobolev Ω) {R : ℝ}
    (heq : ∀ v : dirichletSobolev (coordinateHalfBall j R),
      (∑ i : Fin n, inner ℝ (u.1 i.succ) (v.1 i.succ))=0)
    {ψ : KernelSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψR : tsupport ψ ⊆ Metric.ball 0 R) (hψ0 : ∀ x, x j=0 → ψ x=0) :
    (∫ x, dirichletValue Ω u (dirichletCoordinateEquiv n x)*kernelLaplacian ψ x)=0 := by
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have hG (i : Fin n) : LocallyIntegrable (fun x => u.1 i.succ (dirichletCoordinateEquiv n x)) volume :=
    ((Lp.memLp (u.1 i.succ)).comp_measurePreserving hμ).locallyIntegrable (by norm_num)
  have hG0 (i : Fin n) : ∀ᵐ x ∂volume, x j ≤ 0 → u.1 i.succ (dirichletCoordinateEquiv n x)=0 := by
    filter_upwards [hμ.quasiMeasurePreserving.ae (dirichletGradient_ae_zero_outside hΩ u i)] with x hx hxj
    apply hx
    intro hxΩ
    have hh := hupper _ hxΩ
    change 0 < x j at hh
    linarith
  have hh := integral_gradient_flat_zero_test j hG hG0
    (fun φ hφ hφc hφΩ => dirichletSobolev_physical_weak_harmonic u j heq hφ hφc hφΩ)
    hψ hψc hψR hψ0
  rw [dirichletSobolev_physical_gradient_pairing u hψ hψc] at hh
  linarith

end GaussianTilt.MomentMapLinearDirichlet
