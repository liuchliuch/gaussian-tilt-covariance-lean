import GaussianTilt.MomentMapLinearDirichletVariableWeakBoundaryRegularity
import GaussianTilt.MomentMapLinearDirichletVariableWeakPhysicalValue

/-! # Constructed C²,α boundary fields for the actual physical weak Poisson solution -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 1000

/-- The true physical H₀¹ solution acquires an actual C²,α closed-boundary
jet in a constructed smooth inverse chart. The entire weak regularity,
tangential derivative existence, higher weak equations and normal recovery
are discharged from the physical PDE and original Hölder datum. -/
theorem exists_curved_weak_boundary_C2_holder [NeZero n]
    {w:E n → ℝ} (hw:ContDiff ℝ ∞ w) (a:E n) (j:Fin n)
    (hj:fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0)
    {s:ℝ} (hs:0<s)
    (hInv:∀ z∈Metric.closedBall (0:E n) (2*s),
      z∈(regularLevelFlatteningChart hw a j hj).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z)
    (u:dirichletSobolev (chartPhysicalDomain w a)) (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (hu:∀v:dirichletSobolev (chartPhysicalDomain w a),
      dirichletEnergy (chartPhysicalDomain w a) u v=inner ℝ f (dirichletValue (chartPhysicalDomain w a) v))
    {f₀ u₀:CoordinateSpace n → ℝ} {α:ℝ} (hα:0<α) (hα1:α<1)
    (hfH:BoundedHolderOn α f₀ univ)
    (hfAE:∀ᵐx∂volume,x∈chartPhysicalDomain w a → f x=f₀ x)
    (hu₀:Continuous u₀)
    (huAE:∀ᵐx∂volume,x∈chartPhysicalDomain w a → u₀ x=u.1 0 x)
    (huZero:∀x,x∉chartPhysicalDomain w a → u₀ x=0) :
    ∃ψ:CoordinateSpace n → CoordinateSpace n,ContDiff ℝ ∞ ψ ∧
      (∀y∈rawChartClosedBall (n:=n) 1,ψ=ᶠ[𝓝 y] scaledRawInverseChart hw a j hj s) ∧
      ∃r:ℝ,0<r ∧ r≤1/16 ∧ ∃Q:CoordinateSpace n → CoordinateSpace n,
      ∃H:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ,
        ContDiffOn ℝ 2 (u₀ ∘ ψ) (coordinateClosedHalfBall j r) ∧
        ContinuousOn Q (coordinateClosedHalfBall j r) ∧ ContinuousOn H (coordinateClosedHalfBall j r) ∧
        BoundedHolderOn α H (coordinateClosedHalfBall j r) ∧
        (∀x∈coordinateClosedHalfBall j r,HasFDerivWithinAt (u₀ ∘ ψ) (coordinateCovector (Q x)) (coordinateClosedHalfBall j r) x) ∧
        ∀k x,x∈coordinateClosedHalfBall j r →
          HasFDerivWithinAt (fun y=>Q y k) (coordinateCovector (H x k)) (coordinateClosedHalfBall j r) x := by
  obtain ⟨ψ,v,A,g,lam₀,K,L,hψ,hlam₀,hK,he,hval,hgrad,hAm,hAb,hEll,hLip,hAeq,hg,hweak⟩ :=
    exists_uniform_flattened_weak_poisson hw a j hj hs hInv u f hu
  obtain ⟨g₀,hg₀H,hg₀AE,hg₀val⟩ := flattened_scalar_load_holder_representative hw a j hj hs hInv hψ he
    f g hg hfAE hα.le hα1.le hfH
  obtain ⟨v₀,hv₀c,hv₀AE,hv₀zero,hv₀val⟩ := flattened_value_continuous_representative hw a j hj hs hInv hψ he
    u v hval hu₀ huAE huZero
  have hvAE:∀ᵐx∂volume,x∈coordinateHalfBall j (1/4) → (u₀ ∘ ψ) x=v.1 0 x := by
    filter_upwards [hv₀AE] with x hx hxU
    change u₀ (ψ x)=_
    rw [← hv₀val x]
    exact hx hxU
  have hgH:BoundedHolderOn α g₀ (coordinateClosedHalfBall j (1/4)) := hg₀H.mono inter_subset_left
  have hAmAE (i k:Fin n) : AEStronglyMeasurable (fun x=>A x i k) volume := (hAm i k).aestronglyMeasurable
  have hAbAE (i k:Fin n) : ∀ᵐx∂volume,|A x i k|≤K := ae_of_all _ (fun x=>hAb x i k)
  obtain ⟨lam,Λ,hlam,hΛ,hE⟩ := actual_flattening_euclidean_ellipticity hw a j hj hs hInv hψ he hAeq
  obtain ⟨D,hD,hMod⟩ := euclidean_entry_modulus_of_coordinate_lipschitz hLip
  have hxS (x:KernelSpace n) (hx:‖x‖≤1/4) : dirichletCoordinateEquiv n x∈rawChartClosedBall (n:=n) (1/4) := by
    change ‖(coordinateEquiv n).symm (coordinateEquiv n x)‖≤1/4
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  have hCoeff:WeakBallCoefficientBounds A K (1/4) lam Λ D 1 := {
    nonneg := hK
    measurable := hAmAE
    bound := hAbAE
    positive := fun x hx=>(hE x hx).1
    lower := fun x hx z=>((hE x hx).2 z).1
    upper := fun x hx z=>((hE x hx).2 z).2
    holder := by
      intro x hx y hy i k
      simpa only [Real.rpow_one] using hMod x (hxS x hx) y (hxS y hy) i k }
  have hAsAll := contDiffOn_actual_flattening_coefficients hw a j hj hs hInv hψ he hAeq
  have hAs (i k:Fin n) : ContDiffOn ℝ ∞ (fun x=>A x i k) (rawChartBall (n:=n) (1/4)) :=
    contDiffOn_pi.mp (contDiffOn_pi.mp hAsAll i) k
  have hEq:∀τ:dirichletSobolev (coordinateHalfBall j (1/4)),
      variableJetEnergy A hCoeff.measurable hCoeff.nonneg hCoeff.bound v.1 τ.1=
        inner ℝ g (dirichletValue (coordinateHalfBall j (1/4)) τ) := by
    intro τ
    rw [variableJetEnergy_integral]
    exact hweak τ
  obtain ⟨r,hr,hrmax,Q,H,hC2,hQc,hHc,hHH,hDu,hDG⟩ :=
    exists_scalar_weak_boundary_C2_holder j hlam hΛ.le hD hCoeff hAs hlam₀ (ae_of_all _ hEll) hLip
      v g hEq hα hα1 hgH hg₀AE (hu₀.comp hψ.continuous).continuousOn hvAE
  exact ⟨ψ,hψ,he,r,hr,hrmax,Q,H,hC2,hQc,hHc,hHH,hDu,hDG⟩

end GaussianTilt.MomentMapLinearDirichlet
