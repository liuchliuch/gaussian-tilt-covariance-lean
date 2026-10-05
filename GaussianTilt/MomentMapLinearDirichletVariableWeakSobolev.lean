import GaussianTilt.MomentMapLinearDirichletVariableWeakPullbackJet

/-! # The actual H₀¹ chart pullback, obtained by closing genuine compact tests

No classical derivative of the weak input is assumed. Its output value
and all weak gradient coordinates are identified literally almost everywhere.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff BigOperators Topology
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 1000

 def localizedSobolevPullbackJet {S : Set (CoordinateSpace n)} (hS : MeasurableSet S)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : ContDiff ℝ ∞ ψ) {C : ℝ} (hC : 0≤C)
    (hmap : (volume.restrict S).map ψ≤ENNReal.ofReal (C^2) • volume) (a : smoothCompactCore n) :
    SobolevJet (volume : Measure (CoordinateSpace n)) →L[ℝ] SobolevJet (volume : Measure (CoordinateSpace n)) :=
  sobolevJetPullback (localizedL2Pullback hS hψ.continuous.measurable hC hmap a)
    (fun i=>localizedL2Pullback hS hψ.continuous.measurable hC hmap (smoothCompactDerivative i a))
    (fun i j=>localizedL2Pullback hS hψ.continuous.measurable hC hmap (smoothCompactChartCoefficient a hψ i j))

 theorem localizedSobolevPullbackJet_mem {Ω Ω' S : Set (CoordinateSpace n)}
    (hS : MeasurableSet S) {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : ContDiff ℝ ∞ ψ)
    {C : ℝ} (hC : 0≤C) (hmap : (volume.restrict S).map ψ≤ENNReal.ofReal (C^2) • volume)
    (a : smoothCompactCore n) (haS : tsupport a.1⊆S)
    (hchart : ∀ x∈tsupport a.1, ψ x∈Ω → x∈Ω') (u : dirichletSobolev Ω) :
    localizedSobolevPullbackJet hS hψ hC hmap a u.1∈dirichletSobolev Ω' := by
  let P := localizedSobolevPullbackJet hS hψ hC hmap a
  have hclosed : IsClosed (P ⁻¹' (dirichletSobolev Ω' : Set (SobolevJet (volume : Measure (CoordinateSpace n))))) :=
    (LinearMap.range (dirichletJet Ω')).isClosed_topologicalClosure.preimage P.continuous
  have hcore : (LinearMap.range (dirichletJet Ω) : Set (SobolevJet (volume : Measure (CoordinateSpace n))))⊆
      P ⁻¹' (dirichletSobolev Ω' : Set (SobolevJet (volume : Measure (CoordinateSpace n)))) := by
    rintro _ ⟨f,rfl⟩
    change P (smoothCompactJet volume f.1)∈dirichletSobolev Ω'
    rw [show P (smoothCompactJet volume f.1)=smoothCompactJet volume (smoothCompactChartPullback a hψ f.1) from
      sobolevJetPullback_core hS hψ hC hmap a haS f.1]
    apply (LinearMap.range (dirichletJet Ω')).le_topologicalClosure
    exact ⟨⟨smoothCompactChartPullback a hψ f.1,smoothCompactChartPullback_support a hψ f.1 f.2 hchart⟩,rfl⟩
  exact closure_minimal hcore hclosed u.2

/-- A nonlinear smooth chart really pulls back the weak value/gradient
pair to another H₀¹ pair, with the full weak chain rule. -/
theorem exists_dirichletSobolev_chart_pullback {Ω Ω' S : Set (CoordinateSpace n)}
    (hS : MeasurableSet S) {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : ContDiff ℝ ∞ ψ)
    {C : ℝ} (hC : 0≤C) (hmap : (volume.restrict S).map ψ≤ENNReal.ofReal (C^2) • volume)
    (a : smoothCompactCore n) (haS : tsupport a.1⊆S)
    (hchart : ∀ x∈tsupport a.1, ψ x∈Ω → x∈Ω') (u : dirichletSobolev Ω) :
    ∃ v : dirichletSobolev Ω',
      (dirichletValue Ω' v =ᵐ[volume] fun x=>a.1 x*dirichletValue Ω u (ψ x)) ∧
      ∀ i, v.1 i.succ =ᵐ[volume] fun x=>
        coordinateDerivative i a.1 x*dirichletValue Ω u (ψ x)+
          ∑ j, (a.1 x*chartDerivativeEntry ψ i j x)*u.1 j.succ (ψ x) := by
  let P := localizedSobolevPullbackJet hS hψ hC hmap a
  let v : dirichletSobolev Ω' := ⟨P u.1,localizedSobolevPullbackJet_mem hS hψ hC hmap a haS hchart u⟩
  refine ⟨v,?_,?_⟩
  · exact localizedL2Pullback_ae hS hψ.continuous.measurable hC hmap a haS (u.1 0)
  · intro i
    let D := localizedL2Pullback hS hψ.continuous.measurable hC hmap (smoothCompactDerivative i a)
    let A := fun j=>localizedL2Pullback hS hψ.continuous.measurable hC hmap (smoothCompactChartCoefficient a hψ i j)
    have hd := localizedL2Pullback_ae hS hψ.continuous.measurable hC hmap
      (smoothCompactDerivative i a) ((coordinateDerivative_tsupport_subset a.1 i).trans haS) (u.1 0)
    have ha (j:Fin n) := localizedL2Pullback_ae hS hψ.continuous.measurable hC hmap
      (smoothCompactChartCoefficient a hψ i j) ((smoothCompactChartCoefficient_support a hψ i j).trans haS) (u.1 j.succ)
    have hvcoord : v.1 i.succ=D (u.1 0)+∑ j,A j (u.1 j.succ) :=
      sobolevJetPullback_succ _ _ _ u.1 i
    rw [hvcoord]
    filter_upwards [hd,ae_all_iff.mpr ha,Lp_coeFn_finset_sum (fun j=>A j (u.1 j.succ)) Finset.univ,
      Lp.coeFn_add (D (u.1 0)) (∑ j,A j (u.1 j.succ))] with x hd ha hsum hadd
    change (D (u.1 0)+∑ j,A j (u.1 j.succ)) x=_
    simp only [Pi.add_apply] at hadd
    rw [hadd,hd,hsum]
    have hs : (∑ j,A j (u.1 j.succ) x)=
        ∑ j,(a.1 x*chartDerivativeEntry ψ i j x)*u.1 j.succ (ψ x) := by
      apply Finset.sum_congr rfl
      intro j _
      exact ha j
    rw [hs]
    rfl

end GaussianTilt.MomentMapLinearDirichlet
