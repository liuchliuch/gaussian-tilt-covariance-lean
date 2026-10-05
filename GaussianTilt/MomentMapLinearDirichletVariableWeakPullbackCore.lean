import GaussianTilt.MomentMapLinearDirichletVariableWeakMask
import GaussianTilt.MomentMapLinearDirichletLocalization

/-! # Actual compact test pullback and its full first-derivative chain rule -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff BigOperators Topology
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

def smoothCompactPullbackBound (a : smoothCompactCore n) : ℝ :=
  Classical.choose (a.2.2.exists_bound_of_continuous a.2.1.continuous)

lemma smoothCompactPullbackBound_bound (a : smoothCompactCore n) (x : CoordinateSpace n) :
    ‖a.1 x‖≤smoothCompactPullbackBound a :=
  Classical.choose_spec (a.2.2.exists_bound_of_continuous a.2.1.continuous) x

lemma smoothCompactPullbackBound_nonneg (a : smoothCompactCore n) : 0≤smoothCompactPullbackBound a :=
  (norm_nonneg (a.1 0)).trans (smoothCompactPullbackBound_bound a 0)

/-- A localized composition on genuine L² classes, with its multiplier
bound constructed from the actual smooth compact coefficient. -/
def localizedL2Pullback {S : Set (CoordinateSpace n)} (hS : MeasurableSet S)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : Measurable ψ) {C : ℝ} (hC : 0≤C)
    (hmap : (volume.restrict S).map ψ≤ENNReal.ofReal (C^2) • volume)
    (a : smoothCompactCore n) : Lp ℝ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (CoordinateSpace n)) :=
  (boundedL2Multiplier a.2.1.continuous.aestronglyMeasurable
    (smoothCompactPullbackBound_nonneg a) (ae_of_all volume (smoothCompactPullbackBound_bound a))).comp
      (maskedL2Composition hS hψ hC hmap)

lemma localizedL2Pullback_ae {S : Set (CoordinateSpace n)} (hS : MeasurableSet S)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : Measurable ψ) {C : ℝ} (hC : 0≤C)
    (hmap : (volume.restrict S).map ψ≤ENNReal.ofReal (C^2) • volume)
    (a : smoothCompactCore n) (haS : tsupport a.1⊆S)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    localizedL2Pullback hS hψ hC hmap a f =ᵐ[volume] fun x=>a.1 x*f (ψ x) := by
  simp only [localizedL2Pullback,ContinuousLinearMap.comp_apply]
  filter_upwards [boundedL2Multiplier_ae a.2.1.continuous.aestronglyMeasurable
    (smoothCompactPullbackBound_nonneg a) (ae_of_all volume (smoothCompactPullbackBound_bound a))
    (maskedL2Composition hS hψ hC hmap f),
    maskedL2Composition_ae hS hψ hC hmap f] with x hx he
  change _=a.1 x*f (ψ x)
  rw [hx,he]
  by_cases hxS : x∈S
  · rw [indicator_of_mem hxS]
  · rw [indicator_of_notMem hxS,image_eq_zero_of_notMem_tsupport (fun hh=>hxS (haS hh))]
    simp

lemma coordinateDerivative_tsupport_subset (f : CoordinateSpace n → ℝ) (i : Fin n) :
    tsupport (coordinateDerivative i f)⊆tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hn
  exact hx (by simp [coordinateDerivative,fderiv_of_notMem_tsupport ℝ hn])

def chartDerivativeEntry (ψ : CoordinateSpace n → CoordinateSpace n) (i j : Fin n)
    (x : CoordinateSpace n) : ℝ := fderiv ℝ ψ x (Pi.single i 1) j

lemma coordinateDerivative_comp_chart {ψ : CoordinateSpace n → CoordinateSpace n}
    {f : CoordinateSpace n → ℝ} (hψ : Differentiable ℝ ψ) (hf : Differentiable ℝ f)
    (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (f ∘ ψ) x=
      ∑ j, chartDerivativeEntry ψ i j x*coordinateDerivative j f (ψ x) := by
  unfold coordinateDerivative
  rw [fderiv_comp x (hf _) (hψ _)]
  change fderiv ℝ f (ψ x) (fderiv ℝ ψ x (Pi.single i 1))=_
  rw [fderiv_apply_eq_sum_coordinates]
  rfl

def smoothCompactChartPullback (a : smoothCompactCore n)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : ContDiff ℝ ∞ ψ)
    (f : smoothCompactCore n) : smoothCompactCore n :=
  ⟨fun x=>a.1 x*f.1 (ψ x),a.2.1.mul (f.2.1.comp hψ),a.2.2.mul_right⟩

lemma smoothCompactChartPullback_derivative (a : smoothCompactCore n)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : ContDiff ℝ ∞ ψ)
    (f : smoothCompactCore n) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (smoothCompactChartPullback a hψ f).1 x=
      coordinateDerivative i a.1 x*f.1 (ψ x)+
        ∑ j, (a.1 x*chartDerivativeEntry ψ i j x)*coordinateDerivative j f.1 (ψ x) := by
  change coordinateDerivative i (fun x=>a.1 x*f.1 (ψ x)) x=_
  rw [coordinateDerivative_mul (f:=a.1) (g:=fun y=>f.1 (ψ y)) (a.2.1.differentiable (by simp))
    ((f.2.1.comp hψ).differentiable (by simp))]
  have he := coordinateDerivative_comp_chart (hψ.differentiable (by simp))
    (f.2.1.differentiable (by simp)) i x
  change coordinateDerivative i (fun x=>f.1 (ψ x)) x=_ at he
  rw [he,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma tsupport_comp_subset_preimage {ψ : CoordinateSpace n → CoordinateSpace n}
    (hψ : Continuous ψ) (f : CoordinateSpace n → ℝ) : tsupport (f ∘ ψ)⊆ψ ⁻¹' tsupport f := by
  apply closure_minimal _ ((isClosed_tsupport f).preimage hψ)
  intro x hx
  exact subset_closure hx

lemma smoothCompactChartPullback_support (a : smoothCompactCore n)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : ContDiff ℝ ∞ ψ)
    (f : smoothCompactCore n) {Ω Ω' : Set (CoordinateSpace n)} (hf : tsupport f.1⊆Ω)
    (hchart : ∀ x∈tsupport a.1, ψ x∈Ω → x∈Ω') :
    tsupport (smoothCompactChartPullback a hψ f).1⊆Ω' := by
  intro x hx
  have hxa : x∈tsupport a.1 := tsupport_mul_subset_left hx
  have hxf : x∈tsupport (f.1 ∘ ψ) := tsupport_mul_subset_right hx
  exact hchart x hxa (hf (tsupport_comp_subset_preimage hψ.continuous f.1 hxf))

end GaussianTilt.MomentMapLinearDirichlet
