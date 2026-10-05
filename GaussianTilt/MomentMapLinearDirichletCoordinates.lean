import GaussianTilt.MomentMapLinearDirichletMollification
import GaussianTilt.MomentMapLinearDirichletHarmonicLocal

/-!
# Exact Euclidean-coordinate transfer for the weak Dirichlet equation

The canonical linear equivalence preserves Lebesgue measure and carries
the orthonormal basis to the actual coordinate vectors. Both Laplacians
and the literal distributional identities therefore transfer exactly,
without a norm or Jacobian convention being assumed.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def dirichletCoordinateEquiv (n : ℕ) : KernelSpace n ≃L[ℝ] CoordinateSpace n :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)

lemma dirichletCoordinateEquiv_basis (i : Fin n) :
    dirichletCoordinateEquiv n (EuclideanSpace.basisFun (Fin n) ℝ i) = Pi.single i 1 := by
  change WithLp.ofLp (EuclideanSpace.basisFun (Fin n) ℝ i) = _
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.ofLp_single]

lemma kernelDirectionalDerivative_ofLp_any (f : CoordinateSpace n → ℝ)
    (i : Fin n) (x : KernelSpace n) :
    kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i)
      (f ∘ dirichletCoordinateEquiv n) x = coordinateDerivative i f (dirichletCoordinateEquiv n x) := by
  unfold kernelDirectionalDerivative coordinateDerivative
  rw [(dirichletCoordinateEquiv n).comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    dirichletCoordinateEquiv_basis]

lemma kernelLaplacian_ofLp_any (f : CoordinateSpace n → ℝ) (x : KernelSpace n) :
    kernelLaplacian (f ∘ dirichletCoordinateEquiv n) x =
      euclideanLaplacian f (dirichletCoordinateEquiv n x) := by
  have hd (i : Fin n) : kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i)
      (f ∘ dirichletCoordinateEquiv n) = coordinateDerivative i f ∘ dirichletCoordinateEquiv n :=
    funext (kernelDirectionalDerivative_ofLp_any f i)
  apply Finset.sum_congr rfl
  intro i _
  change kernelDirectionalDerivative _ (kernelDirectionalDerivative _ (f ∘ dirichletCoordinateEquiv n)) x = _
  rw [hd, kernelDirectionalDerivative_ofLp_any]

lemma euclideanLaplacian_toLp_any (f : KernelSpace n → ℝ) (x : CoordinateSpace n) :
    euclideanLaplacian (f ∘ (dirichletCoordinateEquiv n).symm) x =
      kernelLaplacian f ((dirichletCoordinateEquiv n).symm x) := by
  have h := kernelLaplacian_ofLp_any (f ∘ (dirichletCoordinateEquiv n).symm)
    ((dirichletCoordinateEquiv n).symm x)
  have he : ((f ∘ (dirichletCoordinateEquiv n).symm) ∘ dirichletCoordinateEquiv n) = f := by
    funext y
    simp
  rw [he, (dirichletCoordinateEquiv n).apply_symm_apply] at h
  exact h.symm

lemma kernelDirectionalDerivative_ofLp {f : CoordinateSpace n → ℝ}
    (hf : Differentiable ℝ f) (i : Fin n) (x : KernelSpace n) :
    kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i)
      (f ∘ dirichletCoordinateEquiv n) x = coordinateDerivative i f (dirichletCoordinateEquiv n x) := by
  unfold kernelDirectionalDerivative coordinateDerivative
  rw [fderiv_comp x (hf _) (dirichletCoordinateEquiv n).differentiableAt,
    (dirichletCoordinateEquiv n).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    dirichletCoordinateEquiv_basis]

lemma kernelLaplacian_ofLp {f : CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (x : KernelSpace n) :
    kernelLaplacian (f ∘ dirichletCoordinateEquiv n) x =
      euclideanLaplacian f (dirichletCoordinateEquiv n x) := by
  have hd (i : Fin n) : kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i)
      (f ∘ dirichletCoordinateEquiv n) = coordinateDerivative i f ∘ dirichletCoordinateEquiv n :=
    funext (kernelDirectionalDerivative_ofLp (hf.differentiable (by norm_num)) i)
  apply Finset.sum_congr rfl
  intro i _
  change kernelDirectionalDerivative _ (kernelDirectionalDerivative _ (f ∘ dirichletCoordinateEquiv n)) x = _
  rw [hd, kernelDirectionalDerivative_ofLp ((contDiff_coordinateDerivative hf (m := 1) (by norm_num) i).differentiable le_rfl)]

lemma euclideanLaplacian_toLp {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (x : CoordinateSpace n) :
    euclideanLaplacian (f ∘ (dirichletCoordinateEquiv n).symm) x =
      kernelLaplacian f ((dirichletCoordinateEquiv n).symm x) := by
  have h := kernelLaplacian_ofLp (hf.comp (dirichletCoordinateEquiv n).symm.contDiff)
    ((dirichletCoordinateEquiv n).symm x)
  have he : ((f ∘ (dirichletCoordinateEquiv n).symm) ∘ dirichletCoordinateEquiv n) = f := by
    funext y
    simp
  rw [he, (dirichletCoordinateEquiv n).apply_symm_apply] at h
  exact h.symm

lemma tsupport_comp_dirichletCoordinateEquiv_symm {ψ : KernelSpace n → ℝ} :
    tsupport (ψ ∘ (dirichletCoordinateEquiv n).symm) ⊆
      (dirichletCoordinateEquiv n).symm ⁻¹' tsupport ψ := by
  apply closure_minimal _ ((isClosed_tsupport ψ).preimage (dirichletCoordinateEquiv n).symm.continuous)
  intro y hy
  exact subset_tsupport ψ hy

/-- Literal weak Poisson identities transfer with the true unit Jacobian. -/
theorem distribution_poisson_ofLp {Ω : Set (CoordinateSpace n)}
    {u f : CoordinateSpace n → ℝ}
    (heq : ∀ ψ : CoordinateSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y * euclideanLaplacian ψ y) = ∫ y, f y * ψ y) :
    ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (dirichletCoordinateEquiv n) ⁻¹' Ω →
      (∫ y, u (dirichletCoordinateEquiv n y) * kernelLaplacian ψ y) =
        ∫ y, f (dirichletCoordinateEquiv n y) * ψ y := by
  intro ψ hψ hψc hψΩ
  let Φ := ψ ∘ (dirichletCoordinateEquiv n).symm
  have hΦ : ContDiff ℝ ∞ Φ := hψ.comp (dirichletCoordinateEquiv n).symm.contDiff
  have hΦc : HasCompactSupport Φ := hψc.comp_homeomorph (dirichletCoordinateEquiv n).symm.toHomeomorph
  have hΦΩ : tsupport Φ ⊆ Ω := by
    intro y hy
    have hh := hψΩ (tsupport_comp_dirichletCoordinateEquiv_symm hy)
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hh
  have h := heq Φ hΦ hΦc hΦΩ
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  rw [← hμ.integral_comp (dirichletCoordinateEquiv n).toHomeomorph.measurableEmbedding
      (fun y => u y * euclideanLaplacian Φ y),
    ← hμ.integral_comp (dirichletCoordinateEquiv n).toHomeomorph.measurableEmbedding
      (fun y => f y * Φ y)] at h
  simpa only [Φ, euclideanLaplacian_toLp (contDiff_infty.mp hψ 2), Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply] using h

end GaussianTilt.MomentMapLinearDirichlet
