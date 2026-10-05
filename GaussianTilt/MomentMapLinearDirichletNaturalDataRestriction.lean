import GaussianTilt.MomentMapLinearDirichletNaturalData
import GaussianTilt.MomentMapLinearDirichletEuclideanWeakGradient

/-! # Restriction of literal coefficient, load and representative data -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma WeakBallCoefficientBounds.mono_radius
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {KA R r lam Λ D β : ℝ}
    (hA : WeakBallCoefficientBounds A KA R lam Λ D β) (hr : r≤R) :
    WeakBallCoefficientBounds A KA r lam Λ D β where
  nonneg := hA.nonneg
  measurable := hA.measurable
  bound := hA.bound
  positive := fun x hx=>hA.positive x (hx.trans hr)
  lower := fun x hx=>hA.lower x (hx.trans hr)
  upper := fun x hx=>hA.upper x (hx.trans hr)
  holder := fun x hx y hy=>hA.holder x (hx.trans hr) y (hy.trans hr)

lemma WeakHalfBallLoadBounds.mono_radius {j : Fin n} {R r β F H : ℝ}
    {f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))}
    {G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))}
    {g : KernelSpace n → Fin n → ℝ} (hg : WeakHalfBallLoadBounds j R β F H f G g)
    (hr : r≤R) : WeakHalfBallLoadBounds j r β F H f G g := by
  have hsub : coordinateHalfBall j r⊆coordinateHalfBall j R := fun x hx=>⟨hx.1.trans_le hr,hx.2⟩
  refine ⟨hg.scalar_nonneg,hg.vector_nonneg,?_,?_,?_⟩
  · filter_upwards [hg.scalar_bound] with x hx hxr
    exact hx (hsub hxr)
  · intro i
    filter_upwards [hg.vector_ae i] with x hx hxr
    exact hx (hsub hxr)
  · intro x hx hxj y hy hyj
    exact hg.vector_holder x (hx.trans hr) hxj y (hy.trans hr) hyj

lemma weak_halfBall_equation_mono_radius
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {KA R r lam Λ D β : ℝ}
    (hA : WeakBallCoefficientBounds A KA R lam Λ D β) {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (j : Fin n) (hr : r≤R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (heq : ∀v:dirichletSobolev (coordinateHalfBall j R),
      variableJetEnergy A hA.measurable hA.nonneg hA.bound u.1 v.1=variableScalarVectorLoad (coordinateHalfBall j R) f G v) :
    ∀v:dirichletSobolev (coordinateHalfBall j r),
      variableJetEnergy A hA.measurable hA.nonneg hA.bound u.1 v.1=variableScalarVectorLoad (coordinateHalfBall j r) f G v := by
  have hsub : coordinateHalfBall j r⊆coordinateHalfBall j R := fun x hx=>⟨hx.1.trans_le hr,hx.2⟩
  intro v
  have hh:=heq (dirichletInclusion hsub v)
  rw [variableScalarVectorLoad_apply,dirichletInclusion_value] at hh
  rw [variableScalarVectorLoad_apply]
  exact hh

/-- Compactness of the actual continuous representative supplies a genuine
AE bound on the weak gradient, suitable for the sharp second pass. -/
theorem exists_weakGradient_bound_of_continuous_representative
    (j : Fin n) (u : VolumeJet n) {R : ℝ} {L : KernelSpace n → KernelSpace n}
    (hL : ContinuousOn L (Metric.closedBall 0 R∩{x|0≤x j}))
    (hLAE : ∀ᵐx∂volume,‖x‖≤R → 0<x j → L x=euclideanWeakGradient u x) :
    ∃B:ℝ,0≤B ∧ ∀ᵐx∂volume,‖x‖<R → 0<x j → ‖euclideanWeakGradient u x‖≤B := by
  have hc : IsCompact (Metric.closedBall (0:KernelSpace n) R∩{x|0≤x j}) :=
    (isCompact_closedBall (0:KernelSpace n) R).inter_right
      (isClosed_le continuous_const (PiLp.proj 2 (𝕜:=ℝ) (fun _:Fin n=>ℝ) j).continuous)
  obtain ⟨B,hB⟩:=hc.exists_bound_of_continuousOn hL
  refine ⟨max B 0,le_max_right _ _,?_⟩
  filter_upwards [hLAE] with x hx hxn hxj
  rw [←hx hxn.le hxj]
  exact (hB x ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxn.le,hxj.le⟩).trans (le_max_left _ _)

end GaussianTilt.MomentMapLinearDirichlet
