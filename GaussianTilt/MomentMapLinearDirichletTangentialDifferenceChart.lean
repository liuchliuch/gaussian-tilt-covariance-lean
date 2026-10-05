import GaussianTilt.MomentMapLinearDirichletTangentialDifferenceH1
import GaussianTilt.MomentMapLinearDirichletVariableWeakUniformChart

/-! # Actual higher weak tangential jets in the constructed boundary chart

This directly composes the physical weak Poisson inverse, genuine H¹
chart pullback, derived coefficient bounds and tangential H¹ regularity.
-/
noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Every actual weak physical Poisson solution has genuine higher H¹
tangential derivative jets after flattening. No regularity of the unknown
beyond its original H₀¹ membership is used. -/
theorem exists_flattened_weak_poisson_tangential_h1
    {w : E n→ℝ} (hw : ContDiff ℝ ∞ w) (a : E n) (q : Fin n)
    (hq : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ q)≠0)
    {s : ℝ} (hs : 0<s)
    (hInv : ∀ z∈Metric.closedBall (0:E n) (2*s),
      z∈(regularLevelFlatteningChart hw a q hq).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a q hq).symm z)
    (u : dirichletSobolev (chartPhysicalDomain w a))
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (hu : ∀ v : dirichletSobolev (chartPhysicalDomain w a),
      dirichletEnergy (chartPhysicalDomain w a) u v=inner ℝ f (dirichletValue (chartPhysicalDomain w a) v)) :
    ∃ ψ : CoordinateSpace n → CoordinateSpace n,
    ∃ v : dirichletSobolev (coordinateHalfBall q 1),
    ∃ A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ,
    ∃ g : Lp ℝ 2 (volume : Measure (CoordinateSpace n)),
      ContDiff ℝ ∞ ψ ∧
      (∀ y∈rawChartClosedBall (n:=n) 1, ψ=ᶠ[𝓝 y] scaledRawInverseChart hw a q hq s) ∧
      (∀ᵐ y∂volume, y∈rawChartBall (n:=n) (1/2) →
        dirichletValue (coordinateHalfBall q 1) v y=dirichletValue (chartPhysicalDomain w a) u (ψ y)) ∧
      (∀ i, ∀ᵐ y∂volume, y∈rawChartBall (n:=n) (1/2) →
        v.1 i.succ y=∑ k,chartDerivativeEntry ψ i k y*u.1 k.succ (ψ y)) ∧
      (∀ x∈rawChartClosedBall (n:=n) (1/4), A x=divergenceChartCoefficient (scaledRawForwardChart w a q s) ψ x) ∧
      (∀ τ : dirichletSobolev (coordinateHalfBall q (1/4)),
        (∫ x, ∑ i : Fin n, ∑ k : Fin n, A x i k*v.1 k.succ x*τ.1 i.succ x)=
          inner ℝ g (dirichletValue (coordinateHalfBall q (1/4)) τ)) ∧
      (∀ i : Fin n, i≠q → ∃ W : dirichletSobolev (coordinateHalfBall q (1/8)),
        ∀ᵐ x∂volume, x∈rawChartClosedBall (n:=n) (1/16) →
          dirichletValue (coordinateHalfBall q (1/8)) W x=v.1 i.succ x) := by
  obtain ⟨ψ,v,A,g,lam,K,L,hψ,hlam,hK,he,hval,hgrad,hAm,hAb,hell,hLip,hAeq,hg,hweak⟩ :=
    exists_uniform_flattened_weak_poisson hw a q hq hs hInv u f hu
  refine ⟨ψ,v,A,g,hψ,he,hval,hgrad,hAeq,hweak,?_⟩
  intro i hi
  apply exists_tangential_h1_on_halfBall q i hi (by norm_num : (1:ℝ)/16<1/8)
    (by norm_num : (1:ℝ)/8<1/4) A (fun p k=>(hAm p k).aestronglyMeasurable) hK
    (fun p k=>ae_of_all _ (fun x=>hAb x p k)) hlam (ae_of_all _ hell) hLip v g
  intro τ
  rw [variableJetEnergy_integral]
  exact hweak τ

end GaussianTilt.MomentMapLinearDirichlet
