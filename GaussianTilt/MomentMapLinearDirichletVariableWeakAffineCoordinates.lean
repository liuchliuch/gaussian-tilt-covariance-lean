import GaussianTilt.MomentMapLinearDirichletVariableWeakAffineHarmonic

/-! # The genuine boundary normalization in raw weak-gradient coordinates -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 1000

def rawBoundaryNormalization (P:KernelSpace n ≃L[ℝ] KernelSpace n) :
    CoordinateSpace n ≃L[ℝ] CoordinateSpace n :=
  ((coordinateEquiv n).symm.trans P).trans (coordinateEquiv n)

lemma rawBoundaryNormalization_apply (P:KernelSpace n ≃L[ℝ] KernelSpace n) (x:CoordinateSpace n) :
    rawBoundaryNormalization P x=coordinateEquiv n (P ((coordinateEquiv n).symm x)) := rfl

lemma rawBoundaryNormalization_matrix (P:KernelSpace n ≃L[ℝ] KernelSpace n) :
    LinearMap.toMatrix' (rawBoundaryNormalization P).toLinearMap=euclideanCLMMatrix P.toContinuousLinearMap := by
  ext i k
  rw [euclideanCLMMatrix_entry]
  change (coordinateEquiv n (P ((coordinateEquiv n).symm (Pi.single k 1)))) i=_
  rw [GaussianTilt.MomentMapSchauder.coordinateEquiv_symm_single]
  rfl

lemma rawBoundaryNormalization_plane (P:KernelSpace n ≃L[ℝ] KernelSpace n) (j:Fin n) {c:ℝ}
    (hplane:∀x,(P x) j=c*x j) (x:CoordinateSpace n) :
    rawBoundaryNormalization P x j=c*x j := hplane ((coordinateEquiv n).symm x)

lemma rawBoundaryNormalization_maps_halfball (P:KernelSpace n ≃L[ℝ] KernelSpace n) (j:Fin n)
    {c M r:ℝ} (hc:0<c) (hM:0<M) (hP:‖P.toContinuousLinearMap‖≤M)
    (hplane:∀x,(P x) j=c*x j) :
    MapsTo (rawBoundaryNormalization P) (coordinateHalfBall j (r/M)) (coordinateHalfBall j r) := by
  intro x hx
  have hi := (boundary_normalization_maps_halfball P j hc hM hP hplane).1 hx
  refine ⟨?_,hi.2⟩
  change ‖(coordinateEquiv n).symm (coordinateEquiv n (P ((coordinateEquiv n).symm x)))‖<r
  rw [(coordinateEquiv n).symm_apply_apply]
  exact hi.1

/-- The actual square-root normalization supplied by ellipticity really
produces a weak Laplace-harmonic zero-flat-trace jet on the contained ball. -/
theorem exists_kernel_normalized_harmonic_jet {Ω:Set (CoordinateSpace n)}
    (j:Fin n) (hΩ:Ω⊆{x:CoordinateSpace n|0<x j})
    (P:KernelSpace n ≃L[ℝ] KernelSpace n) {c M r:ℝ}
    (hc:0<c) (hM:0<M) (hr:0<r) (hP:‖P.toContinuousLinearMap‖≤M)
    (hplane:∀x,(P x) j=c*x j) {B:Matrix (Fin n) (Fin n) ℝ}
    (hB:euclideanCLMMatrix P.toContinuousLinearMap*(euclideanCLMMatrix P.toContinuousLinearMap)ᵀ=B)
    (u:dirichletSobolev Ω)
    (heq:∀ξ:smoothCompactCore n,tsupport ξ.1⊆coordinateHalfBall j r →
      (∫ x,(fun i:Fin n=>u.1 i.succ x) ⬝ᵥ (B *ᵥ coordinateGradient ξ.1 x))=0) :
    ∃ v:dirichletSobolev {x:CoordinateSpace n|0<x j},
      (∀ᵐ x∂volume,x∈rawChartBall (n:=n) (r/M) → v.1 0 x=u.1 0 (rawBoundaryNormalization P x)) ∧
      (∀ i,∀ᵐ x∂volume,x∈rawChartBall (n:=n) (r/M) →
        v.1 i.succ x=∑ k,euclideanCLMMatrix P.toContinuousLinearMap k i*u.1 k.succ (rawBoundaryNormalization P x)) ∧
      ∀ τ:dirichletSobolev (coordinateHalfBall j (r/M)),
        (∑ i:Fin n,inner ℝ (v.1 i.succ) (τ.1 i.succ))=0 := by
  simpa only [rawBoundaryNormalization_matrix] using exists_affine_normalized_harmonic_jet j hΩ
    (rawBoundaryNormalization P) hc (div_pos hr hM) (rawBoundaryNormalization_plane P j hplane)
    (rawBoundaryNormalization_maps_halfball P j hc hM hP hplane)
    (by simpa only [rawBoundaryNormalization_matrix] using hB) u heq

end GaussianTilt.MomentMapLinearDirichlet
