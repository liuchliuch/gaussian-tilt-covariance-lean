import GaussianTilt.MomentMapLinearDirichletVariableWeakPullbackCore

/-! # Genuine first-order Sobolev jets under a nonlinear localized chart -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff BigOperators Topology
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 1000

lemma localizedL2Pullback_core_ae {S : Set (CoordinateSpace n)} (hS : MeasurableSet S)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : Measurable ψ) {C : ℝ} (hC : 0≤C)
    (hmap : (volume.restrict S).map ψ≤ENNReal.ofReal (C^2) • volume)
    (a : smoothCompactCore n) (haS : tsupport a.1⊆S) (f : smoothCompactCore n) :
    localizedL2Pullback hS hψ hC hmap a (smoothCompactToL2 volume f)=ᵐ[volume]
      fun x=>a.1 x*f.1 (ψ x) := by
  have hq : Measure.QuasiMeasurePreserving ψ (volume.restrict S) volume :=
    ⟨hψ,Measure.absolutelyContinuous_of_le_smul hmap⟩
  have hf₀ : smoothCompactToL2 volume f =ᵐ[volume] f.1 := smoothCompactToL2_ae volume f
  have hf₁ : ∀ᵐ x∂volume.restrict S, smoothCompactToL2 volume f (ψ x)=f.1 (ψ x) :=
    hf₀.comp_tendsto hq.tendsto_ae
  have hf : ∀ᵐ x∂volume, x∈S → smoothCompactToL2 volume f (ψ x)=f.1 (ψ x) :=
    (ae_restrict_iff' hS).mp hf₁
  filter_upwards [localizedL2Pullback_ae hS hψ hC hmap a haS (smoothCompactToL2 volume f),hf] with x hx hf
  rw [hx]
  by_cases hxS : x∈S
  · rw [hf hxS]
  · rw [image_eq_zero_of_notMem_tsupport (fun hh=>hxS (haS hh))]
    simp

lemma Lp_coeFn_finset_sum {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    {μ : Measure X} (F : ι → Lp ℝ 2 μ) (s : Finset ι) :
    ((∑ i∈s, F i : Lp ℝ 2 μ) : X → ℝ)=ᵐ[μ] fun x=>∑ i∈s, F i x := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=μ))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [ih,Lp.coeFn_add (F i) (∑ j∈s,F j)] with x hx hadd
    simp only [Pi.add_apply] at hadd
    rw [hadd,hx]

def sobolevJetPullback
    (M : Lp ℝ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ] Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (D : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ] Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (A : Fin n → Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ] Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    SobolevJet (volume : Measure (CoordinateSpace n)) →L[ℝ] SobolevJet (volume : Measure (CoordinateSpace n)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1)=>Lp ℝ 2 (volume : Measure (CoordinateSpace n)))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Fin.cases
      (M.comp (PiLp.proj 2 (fun _ : Fin (n+1)=>Lp ℝ 2 (volume : Measure (CoordinateSpace n))) 0))
      (fun i=> (D i).comp (PiLp.proj 2 (fun _ : Fin (n+1)=>Lp ℝ 2 (volume : Measure (CoordinateSpace n))) 0)+
        ∑ j, (A i j).comp (PiLp.proj 2 (fun _ : Fin (n+1)=>Lp ℝ 2 (volume : Measure (CoordinateSpace n))) j.succ))))

@[simp] lemma sobolevJetPullback_zero (M D A) (u : SobolevJet (volume : Measure (CoordinateSpace n))) :
    sobolevJetPullback M D A u 0=M (u 0) := rfl

@[simp] lemma sobolevJetPullback_succ (M D A) (u : SobolevJet (volume : Measure (CoordinateSpace n))) (i : Fin n) :
    sobolevJetPullback M D A u i.succ=D i (u 0)+∑ j,A i j (u j.succ) := by
  change D i (u 0)+(∑ j,(A i j).comp
    (PiLp.proj 2 (fun _ : Fin (n+1)=>Lp ℝ 2 (volume : Measure (CoordinateSpace n))) j.succ)) u=_
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,PiLp.proj_apply]

def smoothCompactChartCoefficient (a : smoothCompactCore n)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : ContDiff ℝ ∞ ψ) (i j : Fin n) : smoothCompactCore n := by
  have hD : ContDiff ℝ ∞ (chartDerivativeEntry ψ i j) :=
    (contDiff_apply ℝ ℝ j).comp ((hψ.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const)
  exact ⟨fun x=>a.1 x*chartDerivativeEntry ψ i j x,a.2.1.mul hD,a.2.2.mul_right⟩

lemma smoothCompactChartCoefficient_support (a : smoothCompactCore n)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : ContDiff ℝ ∞ ψ) (i j : Fin n) :
    tsupport (smoothCompactChartCoefficient a hψ i j).1⊆tsupport a.1 := tsupport_mul_subset_left

/-- The constructed continuous jet operator reproduces the actual full
nonlinear chain rule on every genuine compact smooth source test. -/
theorem sobolevJetPullback_core {S : Set (CoordinateSpace n)} (hS : MeasurableSet S)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : ContDiff ℝ ∞ ψ) {C : ℝ} (hC : 0≤C)
    (hmap : (volume.restrict S).map ψ≤ENNReal.ofReal (C^2) • volume)
    (a : smoothCompactCore n) (haS : tsupport a.1⊆S) (f : smoothCompactCore n) :
    sobolevJetPullback (localizedL2Pullback hS hψ.continuous.measurable hC hmap a)
      (fun i=>localizedL2Pullback hS hψ.continuous.measurable hC hmap (smoothCompactDerivative i a))
      (fun i j=>localizedL2Pullback hS hψ.continuous.measurable hC hmap (smoothCompactChartCoefficient a hψ i j))
      (smoothCompactJet volume f)=smoothCompactJet volume (smoothCompactChartPullback a hψ f) := by
  apply PiLp.ext
  intro k
  refine Fin.cases ?_ (fun i=>?_) k
  · simp only [sobolevJetPullback_zero,smoothCompactJet_zero]
    apply Lp.ext
    exact (localizedL2Pullback_core_ae hS hψ.continuous.measurable hC hmap a haS f).trans
      (smoothCompactToL2_ae volume (smoothCompactChartPullback a hψ f)).symm
  · simp only [sobolevJetPullback_succ,smoothCompactJet_zero,smoothCompactJet_succ]
    let D := localizedL2Pullback hS hψ.continuous.measurable hC hmap (smoothCompactDerivative i a)
    let A := fun j=>localizedL2Pullback hS hψ.continuous.measurable hC hmap (smoothCompactChartCoefficient a hψ i j)
    have hd := localizedL2Pullback_core_ae hS hψ.continuous.measurable hC hmap
      (smoothCompactDerivative i a) ((coordinateDerivative_tsupport_subset a.1 i).trans haS) f
    have ha (j:Fin n) := localizedL2Pullback_core_ae hS hψ.continuous.measurable hC hmap
      (smoothCompactChartCoefficient a hψ i j) ((smoothCompactChartCoefficient_support a hψ i j).trans haS)
      (smoothCompactDerivative j f)
    apply Lp.ext
    filter_upwards [hd,ae_all_iff.mpr ha,
      Lp_coeFn_finset_sum (fun j=>A j (smoothCompactToL2 volume (smoothCompactDerivative j f))) Finset.univ,
      Lp.coeFn_add (D (smoothCompactToL2 volume f)) (∑ j,A j (smoothCompactToL2 volume (smoothCompactDerivative j f))),
      smoothCompactToL2_ae volume (smoothCompactDerivative i (smoothCompactChartPullback a hψ f))]
      with x hd ha hsum hadd hout
    simp only [Pi.add_apply] at hadd
    rw [hadd,hd,hsum,hout]
    have hs : (∑ j,A j (smoothCompactToL2 volume (smoothCompactDerivative j f)) x)=
        ∑ j,(a.1 x*chartDerivativeEntry ψ i j x)*coordinateDerivative j f.1 (ψ x) := by
      apply Finset.sum_congr rfl
      intro j _
      exact ha j
    rw [hs]
    exact (smoothCompactChartPullback_derivative a hψ f i x).symm

end GaussianTilt.MomentMapLinearDirichlet
