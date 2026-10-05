import GaussianTilt.MomentMapLinearDirichletTangentialDifferenceL2
import GaussianTilt.MomentMapLinearDirichletHalfBallGeometry
import GaussianTilt.MomentMapLinearDirichletVariableWeakFlattening

/-! # Genuine tangential difference jets and flat-boundary localization

Tangential translation preserves the actual H₀¹ half-space closure. A
compact radial cutoff then puts its difference quotient into a smaller
half-ball without incorrectly requiring the cutoff to vanish near the
flat boundary. All product rules are proved on the genuine compact core.
-/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- The difference quotient of the actual value/weak-gradient jet. -/
def volumeDifferenceJet (i : Fin n) (h : ℝ) : VolumeJet n →L[ℝ] VolumeJet n :=
  h⁻¹ • (volumeTranslateJet (h • (Pi.single i 1 : CoordinateSpace n)) - ContinuousLinearMap.id ℝ _)

@[simp] lemma volumeDifferenceJet_apply (i : Fin n) (h : ℝ) (u : VolumeJet n) (k : Fin (n+1)) :
    volumeDifferenceJet i h u k =
      h⁻¹ • (volumeTranslate (h • (Pi.single i 1 : CoordinateSpace n)) (u k)-u k) := rfl

@[simp] lemma volumeDifferenceJet_value {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (i : Fin n) (h : ℝ) :
    volumeDifferenceJet i h u.1 0 = dirichletDifferenceQuotient u i h := rfl

/-- A true tangential H₀¹ difference quotient has zero flat trace. -/
theorem volumeDifferenceJet_mem_halfspace (q i : Fin n) (hi : i≠q) (h : ℝ)
    (u : dirichletSobolev {x : CoordinateSpace n | 0 < x q}) :
    volumeDifferenceJet i h u.1 ∈ dirichletSobolev {x : CoordinateSpace n | 0 < x q} := by
  apply (dirichletSobolev _).smul_mem
  apply (dirichletSobolev _).sub_mem _ u.2
  exact volumeTranslateJet_mem_halfspace q (by simp [Ne.symm hi]) u

/-- A concrete continuous L² multiplier by a genuine smooth compact cutoff. -/
def smoothCoreL2Multiply (a : smoothCompactCore n) :
    Lp ℝ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ] Lp ℝ 2 (volume : Measure (CoordinateSpace n)) := by
  let hb := a.2.2.exists_bound_of_continuous a.2.1.continuous
  exact boundedL2Multiplier a.2.1.continuous.aestronglyMeasurable
    ((norm_nonneg (a.1 0)).trans (Classical.choose_spec hb 0))
    (ae_of_all volume (Classical.choose_spec hb))

lemma smoothCoreL2Multiply_ae (a : smoothCompactCore n)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    smoothCoreL2Multiply a f =ᵐ[volume] fun x=>a.1 x*f x := by
  unfold smoothCoreL2Multiply
  exact boundedL2Multiplier_ae _ _ _ _

/-- The literal product-rule jet map. -/
def smoothCoreJetMultiply (a : smoothCompactCore n) : VolumeJet n →L[ℝ] VolumeJet n :=
  sobolevJetMultiply (smoothCoreL2Multiply a) (fun i=>smoothCoreL2Multiply (smoothCompactDerivative i a))

@[simp] lemma smoothCoreJetMultiply_zero (a : smoothCompactCore n) (u : VolumeJet n) :
    smoothCoreJetMultiply a u 0 = smoothCoreL2Multiply a (u 0) := rfl

@[simp] lemma smoothCoreJetMultiply_succ (a : smoothCompactCore n) (u : VolumeJet n) (i : Fin n) :
    smoothCoreJetMultiply a u i.succ = smoothCoreL2Multiply a (u i.succ)+
      smoothCoreL2Multiply (smoothCompactDerivative i a) (u 0) := rfl

lemma smoothCoreJetMultiply_core (a f : smoothCompactCore n) :
    smoothCoreJetMultiply a (smoothCompactJet volume f) =
      smoothCompactJet volume (smoothCompactMultiply a.2.1 f) :=
  sobolevJetMultiply_core a.2.1 (Measure.AbsolutelyContinuous.refl volume) _ _
    (smoothCoreL2Multiply_ae a) (fun i=>smoothCoreL2Multiply_ae (smoothCompactDerivative i a)) f

/-- Only the intersection of cutoff support with the original domain has
to lie in the target domain. This preserves an actual pre-existing zero
trace, even when the cutoff is nonzero on the flat boundary. -/
theorem smoothCoreJetMultiply_mem {Ω U : Set (CoordinateSpace n)}
    (a : smoothCompactCore n) (ha : tsupport a.1 ∩ Ω ⊆ U) (u : dirichletSobolev Ω) :
    smoothCoreJetMultiply a u.1 ∈ dirichletSobolev U := by
  have hclosed : IsClosed ((smoothCoreJetMultiply a) ⁻¹'
      (dirichletSobolev U : Set (VolumeJet n))) :=
    (LinearMap.range (dirichletJet U)).isClosed_topologicalClosure.preimage (smoothCoreJetMultiply a).continuous
  have hcore : (LinearMap.range (dirichletJet Ω) : Set (VolumeJet n)) ⊆
      (smoothCoreJetMultiply a) ⁻¹' (dirichletSobolev U : Set (VolumeJet n)) := by
    rintro _ ⟨f,rfl⟩
    change smoothCoreJetMultiply a (smoothCompactJet volume f.1) ∈ dirichletSobolev U
    rw [smoothCoreJetMultiply_core]
    apply (LinearMap.range (dirichletJet U)).le_topologicalClosure
    refine ⟨⟨smoothCompactMultiply a.2.1 f.1,?_⟩,rfl⟩
    intro x hx
    exact ha ⟨tsupport_mul_subset_left hx,f.2 (tsupport_mul_subset_right hx)⟩
  exact closure_minimal hcore hclosed u.2

/-- The actual cutoff product in the target H₀¹ space. -/
def dirichletSmoothMultiply {Ω U : Set (CoordinateSpace n)}
    (a : smoothCompactCore n) (ha : tsupport a.1 ∩ Ω ⊆ U) :
    dirichletSobolev Ω →L[ℝ] dirichletSobolev U :=
  ((smoothCoreJetMultiply a).comp (dirichletSobolev Ω).subtypeL).codRestrict _
    (smoothCoreJetMultiply_mem a ha)

@[simp] lemma dirichletSmoothMultiply_value {Ω U : Set (CoordinateSpace n)}
    (a : smoothCompactCore n) (ha : tsupport a.1 ∩ Ω ⊆ U) (u : dirichletSobolev Ω) :
    dirichletValue U (dirichletSmoothMultiply a ha u) = smoothCoreL2Multiply a (dirichletValue Ω u) := rfl

/-- A radial cutoff of a tangential quotient belongs to the actual smaller
half-ball H₀¹ space, including its zero flat-boundary trace. -/
theorem smoothCoreJetMultiply_difference_mem_halfBall (q i : Fin n) (hi : i≠q)
    {r : ℝ} (a : smoothCompactCore n) (ha : tsupport a.1 ⊆ rawChartBall r)
    (u : dirichletSobolev {x : CoordinateSpace n | 0 < x q}) (h : ℝ) :
    smoothCoreJetMultiply a (volumeDifferenceJet i h u.1) ∈ dirichletSobolev (coordinateHalfBall q r) := by
  exact smoothCoreJetMultiply_mem (Ω := {x : CoordinateSpace n | 0 < x q})
    (U := coordinateHalfBall q r) a (fun x hx=>⟨ha hx.1,hx.2⟩)
    ⟨volumeDifferenceJet i h u.1,volumeDifferenceJet_mem_halfspace q i hi h u⟩

/-- Localized difference quotient values genuinely converge strongly in
L² to the cutoff times the original weak derivative. -/
theorem smoothCoreL2Multiply_difference_tendsto {Ω : Set (CoordinateSpace n)}
    (a : smoothCompactCore n) (u : dirichletSobolev Ω) (i : Fin n) :
    Tendsto (fun h=>smoothCoreJetMultiply a (volumeDifferenceJet i h u.1) 0)
      (𝓝[≠] (0:ℝ)) (𝓝 (smoothCoreL2Multiply a (u.1 i.succ))) :=
  ((smoothCoreL2Multiply a).continuous.tendsto _).comp (dirichletDifferenceQuotient_tendsto u i)

end GaussianTilt.MomentMapLinearDirichlet
