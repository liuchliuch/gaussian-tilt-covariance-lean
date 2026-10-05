import GaussianTilt.MomentMapLinearDirichletHarmonicHalfEnergy
import GaussianTilt.MomentMapLinearDirichletEuclideanWeakGradient

/-! # Genuine H¹ half-ball gradient excess decay

The normal approximating vector is constructed from the smooth reflected
weak-gradient representative. All weak-gradient identities, reflection,
Weyl regularity, energy identities and the n+2 decay are proved inputs.
-/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma dirichletSobolev_regular_reflected_gradient_parity [NeZero n]
    {Ω : Set (CoordinateSpace n)} (hΩ : MeasurableSet Ω) (j : Fin n)
    (hupper : ∀ x ∈ Ω, 0 < x j) (u : dirichletSobolev Ω) {R : ℝ}
    (heq : ∀ v : dirichletSobolev (coordinateHalfBall j R),
      (∑ i : Fin n, inner ℝ (u.1 i.succ) (v.1 i.succ))=0) (i : Fin n) :
    let G := flatReflectedGradient j i (fun k y => u.1 k.succ (dirichletCoordinateEquiv n y))
    ∀ x ∈ Metric.ball (0:KernelSpace n) R,
      harmonicRepresentative G (flatReflection j x)=-flatReflectionSign j i*harmonicRepresentative G x := by
  dsimp only
  let G := flatReflectedGradient j i (fun k y => u.1 k.succ (dirichletCoordinateEquiv n y))
  obtain ⟨hae,hs,hh⟩ := dirichletSobolev_reflected_gradient_regular hΩ j hupper u heq i
  have hAE : (fun x => harmonicRepresentative G (flatReflection j x)) =ᵐ[volume]
      (fun x => -flatReflectionSign j i*harmonicRepresentative G x) := by
    filter_upwards [hae,(flatReflection j).measurePreserving.quasiMeasurePreserving.ae hae] with x hx hTx
    change harmonicRepresentative G x=G x at hx
    change harmonicRepresentative G (flatReflection j x)=G (flatReflection j x) at hTx
    rw [hTx,hx]
    exact flatReflectedGradient_parity j i _ x
  have hhc : ContinuousOn (harmonicRepresentative G) (Metric.ball (0:KernelSpace n) R) :=
    fun x hx => (hs x hx).continuousAt.continuousWithinAt
  have hleft : ContinuousOn (fun x => harmonicRepresentative G (flatReflection j x)) (Metric.ball (0:KernelSpace n) R) := by
    intro x hx
    have hTx : flatReflection j x ∈ Metric.ball (0:KernelSpace n) R := by
      simpa only [Metric.mem_ball,dist_zero_right,LinearIsometryEquiv.norm_map] using hx
    exact ((hs _ hTx).continuousAt.comp (flatReflection j).continuous.continuousAt).continuousWithinAt
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hAE) Metric.isOpen_ball hleft (continuousOn_const.mul hhc)

/-- The complete boundary excess estimate for the actual weak-gradient
field. The outer zero-flat-trace class is genuine H₀¹ membership; no height,
pointwise boundary derivative, smooth approximation, or decay premise is
assumed. The same normal p works for every normal comparison q and radius. -/
theorem exists_dirichletSobolev_halfBall_gradient_excess_decay [NeZero n] :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Set (CoordinateSpace n)), MeasurableSet Ω →
      ∀ j : Fin n, (∀ x ∈ Ω, 0 < x j) → ∀ u : dirichletSobolev Ω,
      ∀ R : ℝ, 0 < R →
      (∀ v : dirichletSobolev (coordinateHalfBall j R),
        (∑ i : Fin n, inner ℝ (u.1 i.succ) (v.1 i.succ))=0) →
      ∃ p : KernelSpace n, (∀ i, i ≠ j → p i=0) ∧
        ∀ q : KernelSpace n, (∀ i, i ≠ j → q i=0) → ∀ r : ℝ, 0 < r → r ≤ R/2 →
          (∫ x in upperCampanatoBall j 0 r, ‖euclideanWeakGradient u.1 x-p‖^2) ≤
            C*(r/R)^(n+2)*(∫ x in upperCampanatoBall j 0 R, ‖euclideanWeakGradient u.1 x-q‖^2) := by
  obtain ⟨C,hC,hDecay⟩ := exists_reflected_harmonic_L2_excess_decay (n := n)
  refine ⟨C,hC,?_⟩
  intro Ω hΩ j hupper u R hR heq
  let G := fun i => flatReflectedGradient j i (fun k y => u.1 k.succ (dirichletCoordinateEquiv n y))
  let H := fun x : KernelSpace n => (WithLp.toLp 2 (fun i => harmonicRepresentative (G i) x) : KernelSpace n)
  have hReg (i : Fin n) := dirichletSobolev_reflected_gradient_regular hΩ j hupper u heq i
  have hLp (i : Fin n) : MemLp (fun x => H x i) 2 volume :=
    (memLp_congr_ae (hReg i).1).mpr (dirichletSobolev_reflected_gradient_distribution_harmonic hΩ j hupper u heq i).1
  have hS (i : Fin n) (x : KernelSpace n) (hx : x ∈ Metric.ball (0:KernelSpace n) R) :
      ContDiffAt ℝ ∞ (fun y => H y i) x := (hReg i).2.1 x hx
  have hP (i : Fin n) (x : KernelSpace n) (hx : x ∈ Metric.ball (0:KernelSpace n) R) :
      kernelLaplacian (fun y => H y i) x=0 := (hReg i).2.2 x hx
  have hParity (i : Fin n) (x : KernelSpace n) (hx : x ∈ Metric.ball (0:KernelSpace n) R) :
      H (flatReflection j x) i=-flatReflectionSign j i*H x i :=
    dirichletSobolev_regular_reflected_gradient_parity hΩ j hupper u heq i x hx
  have hD := hDecay j H hLp R hR hS hP hParity
  refine ⟨H 0,hD.1,?_⟩
  have hAE : ∀ᵐ x ∂volume, 0 ≤ x j → H x=euclideanWeakGradient u.1 x := by
    have hAEs := ae_all_iff.mpr (fun i => (hReg i).1)
    have hUp := ae_all_iff.mpr (fun i => dirichletSobolev_reflected_gradient_ae_upper hΩ j hupper u i)
    filter_upwards [hAEs,hUp] with x hx hxu hxj
    ext i
    exact (hx i).trans (hxu i hxj)
  have hEnergy (q : KernelSpace n) (r : ℝ) :
      (∫ x in upperCampanatoBall j 0 r, ‖H x-q‖^2)=
        ∫ x in upperCampanatoBall j 0 r, ‖euclideanWeakGradient u.1 x-q‖^2 := by
    apply setIntegral_congr_ae (isOpen_upperCampanatoBall j 0 r).measurableSet
    filter_upwards [hAE] with x hx hxs
    rw [hx hxs.2.le]
  intro q hq r hr hrR
  have hh := hD.2 q hq r hr hrR
  rw [hEnergy,hEnergy] at hh
  exact hh

end GaussianTilt.MomentMapLinearDirichlet
