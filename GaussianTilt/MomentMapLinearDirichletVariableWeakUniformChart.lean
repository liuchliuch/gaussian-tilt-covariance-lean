import GaussianTilt.MomentMapLinearDirichletVariableWeakTestClosure

/-! # Fully constructed uniformly elliptic weak boundary chart data -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 1000

/-- Construct every coefficient, forcing class and zero-flat-trace weak jet
needed by frozen harmonic replacement, directly from the genuine physical
weak solution and the actual boundary chart. -/
theorem exists_uniform_flattened_weak_poisson {w : E n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : E n) (j : Fin n) (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0)
    {s : ℝ} (hs : 0 < s)
    (hInv : ∀ z∈Metric.closedBall (0:E n) (2*s),
      z∈(regularLevelFlatteningChart hw a j hj).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z)
    (u : dirichletSobolev (chartPhysicalDomain w a))
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (hu : ∀ v : dirichletSobolev (chartPhysicalDomain w a),
      dirichletEnergy (chartPhysicalDomain w a) u v=inner ℝ f (dirichletValue (chartPhysicalDomain w a) v)) :
    ∃ ψ : CoordinateSpace n → CoordinateSpace n,
    ∃ v : dirichletSobolev (coordinateHalfBall j 1),
    ∃ A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ,
    ∃ g : Lp ℝ 2 (volume : Measure (CoordinateSpace n)),
    ∃ lam K : ℝ, ∃ L : ℝ≥0,
      ContDiff ℝ ∞ ψ ∧ 0 < lam ∧ 0 ≤ K ∧
      (∀ y∈rawChartClosedBall (n:=n) 1, ψ=ᶠ[𝓝 y] scaledRawInverseChart hw a j hj s) ∧
      (∀ᵐ y∂volume, y∈rawChartBall (n:=n) (1/2) →
        dirichletValue (coordinateHalfBall j 1) v y=dirichletValue (chartPhysicalDomain w a) u (ψ y)) ∧
      (∀ i, ∀ᵐ y∂volume, y∈rawChartBall (n:=n) (1/2) →
        v.1 i.succ y=∑ k, chartDerivativeEntry ψ i k y*u.1 k.succ (ψ y)) ∧
      (∀ i k, Measurable (fun x=>A x i k)) ∧
      (∀ x i k, |A x i k| ≤ K) ∧
      (∀ x, ∀ z : Fin n → ℝ, lam*(∑ i,(z i)^2) ≤ z ⬝ᵥ (A x *ᵥ z)) ∧
      LipschitzOnWith L A (rawChartClosedBall (1/4)) ∧
      (∀ x∈rawChartClosedBall (n:=n) (1/4), A x=divergenceChartCoefficient (scaledRawForwardChart w a j s) ψ x) ∧
      (∀ᵐ x∂volume, x∈rawChartClosedBall (n:=n) 1 → g x=|(fderiv ℝ ψ x).det| *f (ψ x)) ∧
      ∀ τ : dirichletSobolev (coordinateHalfBall j (1/4)),
        (∫ x, ∑ i:Fin n, ∑ k:Fin n, A x i k*v.1 k.succ x*τ.1 i.succ x)=
          inner ℝ g (dirichletValue (coordinateHalfBall j (1/4)) τ) := by
  obtain ⟨ψ,C,v,hψ,hC,he,hmap,hval,hgrad,hweak⟩ := exists_flattened_weak_poisson hw a j hj hs hInv u f hu
  obtain ⟨lam,K,L,hlam,hK,hL,hb,hell⟩ := actual_flattening_coefficient_bounds hw a j hj hs hInv hψ he
  let A₀ := divergenceChartCoefficient (scaledRawForwardChart w a j s) ψ
  let A := ellipticPatchExtension (rawChartClosedBall (n:=n) (1/4)) A₀ lam
  have hAm (i k:Fin n) : Measurable (fun x=>A x i k) :=
    ellipticPatchExtension_measurable (isCompact_rawChartClosedBall (n:=n) (1/4)).measurableSet
      (measurable_divergenceChartCoefficient (contDiff_scaledRawForwardChart hw a j s) hψ) lam i k
  have hAb (x:CoordinateSpace n) (i k:Fin n) : |A x i k| ≤ max K lam :=
    ellipticPatchExtension_bound hlam.le hb x i k
  have hAell (x:CoordinateSpace n) (z:Fin n→ℝ) : lam*(∑ i,(z i)^2) ≤ z ⬝ᵥ (A x *ᵥ z) :=
    ellipticPatchExtension_elliptic hell x z
  have hAeq (x:CoordinateSpace n) (hx:x∈rawChartClosedBall (n:=n) (1/4)) : A x=A₀ x :=
    ellipticPatchExtension_eq A₀ lam hx
  have hAL : LipschitzOnWith L A (rawChartClosedBall (n:=n) (1/4)) := by
    intro x hx y hy
    rw [hAeq x hx,hAeq y hy]
    exact hL hx hy
  obtain ⟨g,hg⟩ := exists_masked_jacobian_load (isCompact_rawChartClosedBall (n:=n) 1) hψ hC.le hmap f
  have hgin : ∀ᵐ x∂volume, x∈rawChartClosedBall (n:=n) 1 → g x=|(fderiv ℝ ψ x).det| *f (ψ x) := by
    filter_upwards [hg] with x hx hxS
    simpa only [indicator_of_mem hxS] using hx
  have hDsub (x:CoordinateSpace n) (hx:x∈coordinateHalfBall j (1/4)) : x∈rawChartClosedBall (n:=n) (1/4) := hx.1.le
  have hD1 (x:CoordinateSpace n) (hx:x∈coordinateHalfBall j (1/4)) : x∈rawChartClosedBall (n:=n) 1 := by
    change ‖(coordinateEquiv n).symm x‖ ≤ 1
    have hh := hx.1
    change ‖(coordinateEquiv n).symm x‖ < 1/4 at hh
    linarith
  have hDhalf : coordinateHalfBall j (1/4)⊆coordinateHalfBall j (1/2) := by
    intro x hx
    refine ⟨?_,hx.2⟩
    have hh := hx.1
    change ‖(coordinateEquiv n).symm x‖ < 1/4 at hh
    change ‖(coordinateEquiv n).symm x‖ < 1/2
    linarith
  have hweak' (τ:smoothCompactCore n) (hτ:tsupport τ.1⊆coordinateHalfBall j (1/4)) :
      (∫ x,∑ i:Fin n,∑ k:Fin n,A x i k*v.1 k.succ x*coordinateDerivative i τ.1 x)=∫ x,g x*τ.1 x := by
    apply weak_compact_equation_congr_on_domain (fun x hx=>(hAeq x (hDsub x hx)).symm)
      (u:=v.1) (f:=fun x=>|(fderiv ℝ ψ x).det| *f (ψ x)) (g:=g)
    · filter_upwards [hgin] with x hx hxD
      exact (hx (hD1 x hxD)).symm
    · intro ξ hξ
      exact hweak ξ (hξ.trans hDhalf)
    · exact hτ
  have hAmAE (i k:Fin n) : AEStronglyMeasurable (fun x=>A x i k) volume := (hAm i k).aestronglyMeasurable
  have hAbAE (i k:Fin n) : ∀ᵐ x∂volume, |A x i k| ≤ max K lam := ae_of_all _ (fun x=>hAb x i k)
  have hK' : 0 ≤ max K lam := hK.trans (le_max_left _ _)
  refine ⟨ψ,v,A,g,lam,max K lam,L,hψ,hlam,hK',he,hval,hgrad,hAm,hAb,hAell,hAL,hAeq,hgin,?_⟩
  intro τ
  rw [← variableJetEnergy_integral A hAmAE hK' hAbAE]
  exact weak_divergence_equation_all_dirichlet_tests A hAmAE hK' hAbAE v.1 g hweak' τ

end GaussianTilt.MomentMapLinearDirichlet
