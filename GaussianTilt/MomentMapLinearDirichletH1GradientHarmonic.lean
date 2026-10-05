import GaussianTilt.MomentMapLinearDirichletH1ReflectedGradient

/-! # Actual reflected weak gradients are harmonic and admit smooth representatives -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma kernelDerivative_laplacian_commute {ψ : KernelSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (v : KernelSpace n) :
    kernelDirectionalDerivative v (kernelLaplacian ψ)=kernelLaplacian (kernelDirectionalDerivative v ψ) := by
  funext x
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  change (fderiv ℝ (fun z => ∑ i : Fin n, kernelDirectionalDerivative (b i)
    (kernelDirectionalDerivative (b i) ψ) z) x) v=
      ∑ i : Fin n, kernelDirectionalDerivative (b i) (kernelDirectionalDerivative (b i) (kernelDirectionalDerivative v ψ)) x
  rw [fderiv_fun_sum (fun i _ => ((smooth_kernelDirectionalDerivative (smooth_kernelDirectionalDerivative hψ (b i)) (b i)).differentiable (by simp) x))]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change kernelDirectionalDerivative v (kernelDirectionalDerivative (b i) (kernelDirectionalDerivative (b i) ψ)) x=_
  rw [kernelDirectionalDerivative_commute (contDiff_infty.mp (smooth_kernelDirectionalDerivative hψ (b i)) 2) v (b i),
    kernelDirectionalDerivative_commute (contDiff_infty.mp hψ 2) v (b i)]

lemma tsupport_kernelDerivative_subset (ψ : KernelSpace n → ℝ) (v : KernelSpace n) :
    tsupport (kernelDirectionalDerivative v ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro x hx
  by_contra hh
  exact hx (kernelDerivative_zero_off_tsupport ψ v hh)

/-- The harmonic equation is differentiated in distributions using the
proved full Sobolev weak-gradient identity, not classical regularity. -/
theorem dirichletSobolev_reflected_gradient_distribution_harmonic
    {Ω : Set (CoordinateSpace n)} (hΩ : MeasurableSet Ω) (j : Fin n)
    (hupper : ∀ x ∈ Ω, 0 < x j) (u : dirichletSobolev Ω) {R : ℝ}
    (heq : ∀ v : dirichletSobolev (coordinateHalfBall j R),
      (∑ i : Fin n, inner ℝ (u.1 i.succ) (v.1 i.succ))=0) (i : Fin n) :
    let G := flatReflectedGradient j i (fun k y => u.1 k.succ (dirichletCoordinateEquiv n y))
    MemLp G 2 volume ∧
      ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball 0 R → (∫ x, G x*kernelLaplacian ψ x)=0 := by
  dsimp only
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  refine ⟨flatReflectedGradient_memLp j i ((Lp.memLp (u.1 i.succ)).comp_measurePreserving hμ),?_⟩
  intro ψ hψ hψc hψR
  have hder := dirichletSobolev_odd_weak_gradient u j i (smooth_kernelLaplacian hψ) (hasCompactSupport_kernelLaplacian hψc)
  rw [kernelDerivative_laplacian_commute hψ] at hder
  have hh := (dirichletSobolev_odd_distribution_harmonic hΩ j hupper u heq).2
    (kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ)
    (smooth_kernelDirectionalDerivative hψ _) (hψc.fderiv_apply (𝕜 := ℝ) _)
    ((tsupport_kernelDerivative_subset ψ _).trans hψR)
  rw [hh,neg_zero] at hder
  exact hder

theorem dirichletSobolev_reflected_gradient_regular [NeZero n]
    {Ω : Set (CoordinateSpace n)} (hΩ : MeasurableSet Ω) (j : Fin n)
    (hupper : ∀ x ∈ Ω, 0 < x j) (u : dirichletSobolev Ω) {R : ℝ}
    (heq : ∀ v : dirichletSobolev (coordinateHalfBall j R),
      (∑ i : Fin n, inner ℝ (u.1 i.succ) (v.1 i.succ))=0) (i : Fin n) :
    let G := flatReflectedGradient j i (fun k y => u.1 k.succ (dirichletCoordinateEquiv n y))
    (harmonicRepresentative G =ᵐ[volume] G) ∧
      (∀ x ∈ Metric.ball (0:KernelSpace n) R, ContDiffAt ℝ ∞ (harmonicRepresentative G) x) ∧
      (∀ x ∈ Metric.ball (0:KernelSpace n) R, kernelLaplacian (harmonicRepresentative G) x=0) := by
  dsimp only
  obtain ⟨hG,hH⟩ := dirichletSobolev_reflected_gradient_distribution_harmonic hΩ j hupper u heq i
  exact ⟨harmonicRepresentative_ae_eq (hG.locallyIntegrable (by norm_num)),
    harmonicRepresentative_contDiffAt_of_L2_distribution_harmonic Metric.isOpen_ball hG hH,
    harmonicRepresentative_laplacian_of_L2_distribution_harmonic Metric.isOpen_ball hG hH⟩

lemma dirichletSobolev_reflected_gradient_ae_upper
    {Ω : Set (CoordinateSpace n)} (hΩ : MeasurableSet Ω) (j : Fin n)
    (hupper : ∀ x ∈ Ω, 0 < x j) (u : dirichletSobolev Ω) (i : Fin n) :
    ∀ᵐ x ∂volume, 0 ≤ x j →
      flatReflectedGradient j i (fun k y => u.1 k.succ (dirichletCoordinateEquiv n y)) x=
        u.1 i.succ (dirichletCoordinateEquiv n x) := by
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have hzero := ((hμ.comp (flatReflection j).measurePreserving).quasiMeasurePreserving).ae
    (dirichletGradient_ae_zero_outside hΩ u i)
  filter_upwards [hzero] with x hx hxj
  have hnot : dirichletCoordinateEquiv n (flatReflection j x) ∉ Ω := by
    intro hxΩ
    have hh := hupper _ hxΩ
    change 0 < flatReflection j x j at hh
    rw [flatReflection_apply,if_pos rfl] at hh
    linarith
  have hz : u.1 i.succ (dirichletCoordinateEquiv n (flatReflection j x))=0 := hx hnot
  simp only [flatReflectedGradient,hz,mul_zero,sub_zero]

end GaussianTilt.MomentMapLinearDirichlet
