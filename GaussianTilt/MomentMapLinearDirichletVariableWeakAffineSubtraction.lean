import GaussianTilt.MomentMapLinearDirichletVariableWeakFullBallReplacement
import GaussianTilt.MomentMapLinearDirichletEuclideanWeakGradient
import GaussianTilt.MomentMapClassicalDirichletSolutionCompactness

/-! # Genuine compact affine subtraction in the zero-boundary Sobolev graph -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapElliptic
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 1000

def centeredAffineFunction (a p:KernelSpace n) (x:CoordinateSpace n) : ℝ :=
  coordinateCovector (dirichletCoordinateEquiv n p) (x-dirichletCoordinateEquiv n a)

lemma centeredAffineFunction_smooth (a p:KernelSpace n) : ContDiff ℝ ∞ (centeredAffineFunction a p) :=
  (coordinateCovector (dirichletCoordinateEquiv n p)).contDiff.comp (contDiff_id.sub contDiff_const)

lemma centeredAffineFunction_derivative (a p:KernelSpace n) (i:Fin n) (x:CoordinateSpace n) :
    coordinateDerivative i (centeredAffineFunction a p) x=p i := by
  have hd : HasFDerivAt (centeredAffineFunction a p) (coordinateCovector (dirichletCoordinateEquiv n p)) x := by
    simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using
      (coordinateCovector (dirichletCoordinateEquiv n p)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const (dirichletCoordinateEquiv n a))
  unfold coordinateDerivative
  rw [hd.fderiv,coordinateCovector_apply]
  change (dirichletCoordinateEquiv n p) ⬝ᵥ (Pi.single i (1:ℝ))=p i
  rw [dotProduct_single,mul_one]
  rfl

lemma centeredAffineFunction_eq_inner (a p:KernelSpace n) (x:CoordinateSpace n) :
    centeredAffineFunction a p x=inner ℝ p ((dirichletCoordinateEquiv n).symm x-a) := by
  simp only [centeredAffineFunction,coordinateCovector_apply,PiLp.inner_apply,RCLike.inner_apply,
    conj_trivial,Pi.sub_apply]
  apply Finset.sum_congr rfl
  intro i _
  change p i*(x i-a i)=(x i-a i)*p i
  ring

/-- The real compact test equals the prescribed affine function on the
inner ball and has every derivative equal to the actual slope there. -/
theorem exists_compact_affine_subtraction {Ω:Set (CoordinateSpace n)}
    (a p:KernelSpace n) {r:ℝ} (hr:0<r) (hball:coordinateFullBall a (2*r)⊆Ω) :
    ∃ ℓ:smoothCompactCore n,tsupport ℓ.1⊆Ω ∧
      (∀x∈coordinateFullBall a r,ℓ.1 x=centeredAffineFunction a p x) ∧
      ∀i,∀x∈coordinateFullBall a r,coordinateDerivative i ℓ.1 x=p i := by
  let K := (dirichletCoordinateEquiv n).symm ⁻¹' Metric.closedBall a r
  have hK:IsCompact K := (dirichletCoordinateEquiv n).symm.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall a r)
  have hKU:K⊆coordinateFullBall a (2*r) := by
    intro x hx
    change dist ((dirichletCoordinateEquiv n).symm x) a≤r at hx
    change dist ((dirichletCoordinateEquiv n).symm x) a<2*r
    linarith
  obtain ⟨χ,hχsupp,hχone⟩ := exists_smooth_interior_cutoff (isOpen_coordinateFullBall a (2*r))
    (isBounded_coordinateFullBall a (2*r)) hK hKU
  let ℓ := smoothCompactMultiply (centeredAffineFunction_smooth a p) χ
  have hℓsupp:tsupport ℓ.1⊆Ω := tsupport_mul_subset_right.trans (hχsupp.trans hball)
  have hℓ (x:CoordinateSpace n) (hx:x∈coordinateFullBall a r) : ℓ.1 x=centeredAffineFunction a p x := by
    have hxK:x∈K := Metric.ball_subset_closedBall hx
    change centeredAffineFunction a p x*χ.1 x=_
    rw [hχone hxK]
    simp
  refine ⟨ℓ,hℓsupp,hℓ,?_⟩
  intro i x hx
  have he : ℓ.1=ᶠ[𝓝 x] centeredAffineFunction a p := by
    filter_upwards [(isOpen_coordinateFullBall a r).mem_nhds hx] with y hy
    exact hℓ y hy
  unfold coordinateDerivative
  rw [(he.fderiv (𝕜:=ℝ)).self_of_nhds]
  exact centeredAffineFunction_derivative a p i x

/-- Subtracting the constructed core element preserves the actual H₀¹
membership and gives literal AE affine subtraction of values and gradients. -/
theorem exists_dirichlet_affine_subtraction {Ω:Set (CoordinateSpace n)}
    (a p:KernelSpace n) {r:ℝ} (hr:0<r) (hball:coordinateFullBall a (2*r)⊆Ω)
    (u:dirichletSobolev Ω) :
    ∃ v:dirichletSobolev Ω,
      (∀ᵐx∂volume,x∈coordinateFullBall a r → v.1 0 x=u.1 0 x-centeredAffineFunction a p x) ∧
      (∀i,∀ᵐx∂volume,x∈coordinateFullBall a r → v.1 i.succ x=u.1 i.succ x-p i) ∧
      (∀ᵐx∂(volume:Measure (KernelSpace n)),x∈Metric.ball a r → euclideanWeakGradient v.1 x=euclideanWeakGradient u.1 x-p) := by
  obtain ⟨ℓ,hℓsupp,hℓ,hDℓ⟩ := exists_compact_affine_subtraction a p hr hball
  let z := dirichletCoreToSobolev Ω ⟨ℓ,hℓsupp⟩
  let v := u-z
  have hv0 : ∀ᵐx∂volume,x∈coordinateFullBall a r → v.1 0 x=u.1 0 x-centeredAffineFunction a p x := by
    filter_upwards [Lp.coeFn_sub (u.1 0) (smoothCompactToL2 volume ℓ),smoothCompactToL2_ae volume ℓ] with x hx hℓx hxB
    change (u.1 0-smoothCompactToL2 volume ℓ) x=_
    rw [hx]
    simp only [Pi.sub_apply,hℓx,hℓ x hxB]
  have hvD (i:Fin n) : ∀ᵐx∂volume,x∈coordinateFullBall a r → v.1 i.succ x=u.1 i.succ x-p i := by
    filter_upwards [Lp.coeFn_sub (u.1 i.succ) (smoothCompactToL2 volume (smoothCompactDerivative i ℓ)),
      smoothCompactToL2_ae volume (smoothCompactDerivative i ℓ)] with x hx hℓx hxB
    change (u.1 i.succ-smoothCompactToL2 volume (smoothCompactDerivative i ℓ)) x=_
    rw [hx]
    simp only [Pi.sub_apply,hℓx]
    change u.1 i.succ x-coordinateDerivative i ℓ.1 x=_
    rw [hDℓ i x hxB]
  refine ⟨v,hv0,hvD,?_⟩
  have hμ:MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  filter_upwards [hμ.quasiMeasurePreserving.ae (ae_all_iff.mpr hvD)] with x hx hxB
  ext i
  exact hx i (by simpa only [coordinateFullBall,mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using hxB)

end GaussianTilt.MomentMapLinearDirichlet
