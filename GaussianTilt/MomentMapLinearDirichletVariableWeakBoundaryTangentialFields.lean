import GaussianTilt.MomentMapLinearDirichletNaturalSharpCoordinate
import GaussianTilt.MomentMapLinearDirichletVariableWeakNaturalTools
import GaussianTilt.MomentMapLinearDirichletVariableWeakNaturalLoadData
import GaussianTilt.MomentMapLinearDirichletVariableWeakBootstrapLoads
import GaussianTilt.MomentMapLinearDirichletTangentialDifferenceH1

/-! # Actual Hölder tangential second fields from the genuine weak boundary solution -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 1000

/-- The tangential H¹ jets and their α-Hölder weak-gradient representatives
are constructed from the source equation and the already constructed first
field. No second derivative of the unknown is assumed. -/
theorem exists_boundary_tangential_second_fields [NeZero n]
    (j:Fin n) {A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {K lam Λ D lam₀:ℝ}
    (hlam:0<lam) (hΛ:0≤Λ) (hD:0≤D)
    (hA:WeakBallCoefficientBounds A K (1/4) lam Λ D 1)
    (hAs:∀ i k,ContDiffOn ℝ ∞ (fun x=>A x i k) (rawChartBall (n:=n) (1/4)))
    (hlam₀:0<lam₀) (hEll:∀ᵐx∂volume,∀z:Fin n→ℝ,lam₀*(∑i,(z i)^2)≤z ⬝ᵥ (A x *ᵥ z))
    {L:ℝ≥0} (hLip:LipschitzOnWith L A (rawChartClosedBall (n:=n) (1/4)))
    (u:dirichletSobolev (coordinateHalfBall j 1)) (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (heq:∀v:dirichletSobolev (coordinateHalfBall j (1/4)),
      variableJetEnergy A hA.measurable hA.nonneg hA.bound u.1 v.1=inner ℝ f (dirichletValue (coordinateHalfBall j (1/4)) v))
    {f₀:CoordinateSpace n → ℝ} {α:ℝ} (hα:0<α) (hα1:α<1)
    (hfH:BoundedHolderOn α f₀ (coordinateClosedHalfBall j (1/4)))
    (hfAE:∀ᵐx∂volume,x∈coordinateHalfBall j (1/4) → f x=f₀ x)
    {rQ γ:ℝ} (hrQ:0<rQ) (hrQmax:rQ≤1/16) (hαγ:α≤γ)
    (Q:CoordinateSpace n → CoordinateSpace n)
    (hQH:BoundedHolderOn γ Q (coordinateClosedHalfBall j rQ))
    (hQAE:∀i,∀ᵐx∂volume,x∈coordinateHalfBall j rQ → Q x i=u.1 i.succ x) :
    ∃r:ℝ,0<r ∧ r<rQ ∧ r≤1/16 ∧
    ∃W:{k:Fin n//k≠j} → dirichletSobolev (coordinateHalfBall j (1/8)),
    ∃J:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ,
      BoundedHolderOn α J (coordinateClosedHalfBall j r) ∧
      (∀k i,ContinuousOn (fun x=>J x k i) (coordinateClosedHalfBall j r)) ∧
      (∀k,∀ᵐx∂volume,x∈coordinateHalfBall j r → (W k).1 0 x=u.1 k.1.succ x) ∧
      (∀k i,∀ᵐx∂volume,x∈coordinateHalfBall j r → J x k.1 i=(W k).1 i.succ x) ∧
      ∀x i,J x j i=0 := by
  let R:ℝ := rQ/2
  have hR:0<R := by dsimp [R]; positivity
  have hRQ:R≤rQ := by dsimp [R]; linarith
  have hRmax:R≤1/32 := by dsimp [R]; linarith
  have hRquarter:R≤1/4 := by linarith
  have hReighth:R≤1/8 := by linarith
  have hR16:R≤1/16 := by linarith
  have hSsub:coordinateClosedHalfBall j R⊆rawChartBall (n:=n) (1/4) := by
    intro x hx
    change ‖(coordinateEquiv n).symm x‖<1/4
    have hh:=hx.1
    change ‖(coordinateEquiv n).symm x‖≤R at hh
    linarith
  have hUS:coordinateHalfBall j R⊆coordinateClosedHalfBall j R := coordinateHalfBall_subset_closed j R
  have hUquarter:coordinateHalfBall j R⊆coordinateHalfBall j (1/4) := coordinateHalfBall_radius_mono j hRquarter
  have hCompactEq (ψ:smoothCompactCore n) (hψ:tsupport ψ.1⊆coordinateHalfBall j R) :
      (∫x,∑i:Fin n,∑k:Fin n,A x i k*u.1 k.succ x*coordinateDerivative i ψ.1 x)=∫x,f x*ψ.1 x :=
    scalar_weak_equation_compact_test A hA.measurable hA.nonneg hA.bound u.1 f heq ψ (hψ.trans hUquarter)
  have hfu:∀ᵐx∂volume,x∈coordinateHalfBall j R → f x=f₀ x := by
    filter_upwards [hfAE] with x hx hxU
    exact hx (hUquarter hxU)
  have hqu (k:Fin n) : ∀ᵐx∂volume,x∈coordinateHalfBall j R → u.1 k.succ x=Q x k := by
    filter_upwards [hQAE k] with x hx hxU
    exact (hx (coordinateHalfBall_radius_mono j hRQ hxU)).symm
  have hqH (k:Fin n) : BoundedHolderOn γ (fun x=>Q x k) (coordinateClosedHalfBall j R) :=
    (hQH.mono (coordinateClosedHalfBall_mono j hRQ)).map (ContinuousLinearMap.proj k)
  have hfH' := hfH.mono (coordinateClosedHalfBall_mono j hRquarter)
  have hexW (k:{k:Fin n//k≠j}) : ∃v:dirichletSobolev (coordinateHalfBall j (1/8)),
      ∀ᵐx∂volume,x∈rawChartClosedBall (n:=n) (1/16) → v.1 0 x=u.1 k.1.succ x :=
    exists_tangential_h1_on_halfBall j k.1 k.2 (by norm_num : (1/16:ℝ)<1/8) (by norm_num : (1/8:ℝ)<1/4)
      A hA.measurable hA.nonneg hA.bound hlam₀ hEll hLip u f heq
  choose W hW using hexW
  have hWval (k:{k:Fin n//k≠j}) : ∀ᵐx∂volume,x∈coordinateHalfBall j R → (W k).1 0 x=u.1 k.1.succ x := by
    filter_upwards [hW k] with x hx hxU
    exact hx (show x∈rawChartClosedBall (n:=n) (1/16) from hxU.1.le.trans hR16)
  have hAR:WeakBallCoefficientBounds A K R lam Λ D α := hA.shrink_quarter_exponent hD hRquarter hα.le hα1.le
  have hfields (k:{k:Fin n//k≠j}) : ∃s:ℝ,0<s ∧ s≤R/4 ∧ ∃Qk:CoordinateSpace n → CoordinateSpace n,
      BoundedHolderOn α Qk (coordinateClosedHalfBall j s) ∧ ContinuousOn Qk (coordinateClosedHalfBall j s) ∧
      ∀i,∀ᵐx∂volume,x∈coordinateHalfBall j s → Qk x i=(W k).1 i.succ x := by
    obtain ⟨G,g,hg,hgAE,hgval,hweak⟩ := exists_holder_tangential_vector_equation
      (isOpen_coordinateHalfBall j R) (isOpen_rawChartBall (n:=n) (1/4))
      (isCompact_coordinateClosedHalfBall j R) (convex_coordinateClosedHalfBall j R) hUS hSsub
      u (W k) k.1 (hWval k) A hAs hA.measurable hA.nonneg hA.bound f hCompactEq hfu hqu
      hα.le hα1.le le_rfl hαγ hfH' hqH
    obtain ⟨H,hH,hLoad⟩ := exists_natural_vector_load_bounds_of_raw_holder j R hα.le G g hg hgAE
    exact exists_natural_coordinate_gradient_sharp_holder j hR hlam hΛ hD hα hα1 hAR
      (fun _ hx=>hx.2) (W k) (coordinateHalfBall_radius_mono j hReighth) hLoad hweak
  choose rₖ hrₖ hrₖR Qₖ hQₖH hQₖc hQₖAE using hfields
  obtain ⟨r,hr,hrR,hJH,hJc,hJAE,hJzero⟩ := exists_common_tangential_field_patch j hR rₖ hrₖ
    (fun k=>(W k).1) Qₖ hQₖc hQₖH hQₖAE
  refine ⟨r,hr,hrR.trans_le hRQ,hrR.le.trans hR16,W,assembledTangentRows j Qₖ,hJH,hJc,?_,?_,hJzero⟩
  · intro k
    filter_upwards [hWval k] with x hx hxU
    exact hx (coordinateHalfBall_radius_mono j hrR.le hxU)
  · intro k i
    exact hJAE k.1 k.2 i

end GaussianTilt.MomentMapLinearDirichlet
