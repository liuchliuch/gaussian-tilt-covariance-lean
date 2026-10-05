import GaussianTilt.MomentMapLinearDirichletWeakGradientClassicalCoordinates
import GaussianTilt.MomentMapLinearDirichletVariableWeakTangentialDifferentiated

/-! # Literal local distributional derivatives and smooth coefficient products -/
noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- The literal local compact-test identity, with its sign fixed. -/
def HasLocalWeakDerivative (U : Set (CoordinateSpace n))
    (f g : CoordinateSpace n→ℝ) (i : Fin n) : Prop :=
  ∀ ψ : smoothCompactCore n, tsupport ψ.1⊆U →
    (∫ x,f x*coordinateDerivative i ψ.1 x)= -(∫ x,g x*ψ.1 x)

lemma continuous_local_mul_compact {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    {f ψ : CoordinateSpace n→ℝ} (hf : ContinuousOn f U) (hψ : Continuous ψ)
    (hs : tsupport ψ⊆U) : Continuous (fun x=>f x*ψ x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x∈U
  · exact (hf.continuousAt (hU.mem_nhds hx)).mul hψ.continuousAt
  · apply (continuousAt_const (y:=(0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun hh=>hx (hs hh))] with y hy
    simp only [hy,Pi.zero_apply,mul_zero]

lemma integrable_local_mul_compact {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    {f ψ : CoordinateSpace n→ℝ} (hf : ContinuousOn f U) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆U) :
    Integrable (fun x=>f x*ψ x) volume :=
  (continuous_local_mul_compact hU hf hψ hs).integrable_of_hasCompactSupport hc.mul_left

lemma contDiff_local_mul_compact {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    {f ψ : CoordinateSpace n→ℝ} (hf : ContDiffOn ℝ ∞ f U) (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ⊆U) : ContDiff ℝ ∞ (fun x=>f x*ψ x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x∈U
  · exact (hf.contDiffAt (hU.mem_nhds hx)).mul hψ.contDiffAt
  · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun hh=>hx (hs hh))] with y hy
    simp only [hy,Pi.zero_apply,mul_zero]

/-- A coefficient need only be smooth on the genuine test domain. Its
product with an interior compact test is globally smooth and compact. -/
def localCoefficientTest {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    {a : CoordinateSpace n→ℝ} (ha : ContDiffOn ℝ ∞ a U)
    (ψ : smoothCompactCore n) (hψ : tsupport ψ.1⊆U) : smoothCompactCore n :=
  ⟨fun x=>a x*ψ.1 x,contDiff_local_mul_compact hU ha ψ.2.1 hψ,ψ.2.2.mul_left⟩

lemma localCoefficientTest_support {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    {a : CoordinateSpace n→ℝ} (ha : ContDiffOn ℝ ∞ a U)
    (ψ : smoothCompactCore n) (hψ : tsupport ψ.1⊆U) :
    tsupport (localCoefficientTest hU ha ψ hψ).1⊆U := tsupport_mul_subset_right.trans hψ

lemma localCoefficientTest_derivative {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    {a : CoordinateSpace n→ℝ} (ha : ContDiffOn ℝ ∞ a U)
    (ψ : smoothCompactCore n) (hψ : tsupport ψ.1⊆U) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (localCoefficientTest hU ha ψ hψ).1 x=
      coordinateDerivative i a x*ψ.1 x+a x*coordinateDerivative i ψ.1 x := by
  by_cases hx : x∈U
  · have hd := ((ha.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.mul
      (ψ.2.1.differentiable (by simp) x).hasFDerivAt
    change fderiv ℝ (a*ψ.1) x (Pi.single i 1)=_
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    change a x*coordinateDerivative i ψ.1 x+ψ.1 x*coordinateDerivative i a x=_
    ring
  · have hs : x∉tsupport ψ.1 := fun hh=>hx (hψ hh)
    have hz : ψ.1 x=0 := image_eq_zero_of_notMem_tsupport hs
    have hd : coordinateDerivative i ψ.1 x=0 := by
      unfold coordinateDerivative
      rw [fderiv_of_notMem_tsupport ℝ hs]
      simp
    have ht : x∉tsupport (localCoefficientTest hU ha ψ hψ).1 :=
      fun hh=>hx (localCoefficientTest_support hU ha ψ hψ hh)
    unfold coordinateDerivative
    rw [fderiv_of_notMem_tsupport ℝ ht]
    change 0=coordinateDerivative i a x*ψ.1 x+a x*coordinateDerivative i ψ.1 x
    rw [hz,hd,mul_zero,mul_zero,add_zero]

lemma continuousOn_coordinateDerivative_local {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    {a : CoordinateSpace n→ℝ} (ha : ContDiffOn ℝ ∞ a U) (i : Fin n) :
    ContinuousOn (coordinateDerivative i a) U := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_iff_continuousAt.mpr
  intro x
  have hc := ((ha.contDiffAt (hU.mem_nhds x.2)).fderiv_right (m:=∞) (by simp)).continuousAt
  exact (hc.clm_apply continuousAt_const).comp continuous_subtype_val.continuousAt

/-- The actual weak product rule follows by testing against a·ψ. -/
theorem HasLocalWeakDerivative.mul_smooth {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    {f g a : CoordinateSpace n→ℝ} {i : Fin n}
    (hfg : HasLocalWeakDerivative U f g i) (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (ha : ContDiffOn ℝ ∞ a U) :
    HasLocalWeakDerivative U (fun x=>a x*f x)
      (fun x=>coordinateDerivative i a x*f x+a x*g x) i := by
  intro ψ hψ
  have hh := hfg (localCoefficientTest hU ha ψ hψ) (localCoefficientTest_support hU ha ψ hψ)
  have hI₁ := integrable_local_mul_compact hU (hf.mul (continuousOn_coordinateDerivative_local hU ha i))
    ψ.2.1.continuous ψ.2.2 hψ
  have hI₂ := integrable_local_mul_compact hU (hf.mul ha.continuousOn)
    (smooth_coordinateDerivative ψ.2.1 i).continuous (ψ.2.2.fderiv_apply (𝕜:=ℝ) _)
    ((coordinateDerivative_tsupport_subset ψ.1 i).trans hψ)
  have hI₃ := integrable_local_mul_compact hU (ha.continuousOn.mul hg) ψ.2.1.continuous ψ.2.2 hψ
  have hleft : (∫ x,f x*coordinateDerivative i (localCoefficientTest hU ha ψ hψ).1 x)=
      (∫ x,(f x*coordinateDerivative i a x)*ψ.1 x)+
      ∫ x,(f x*a x)*coordinateDerivative i ψ.1 x := by
    rw [← integral_add hI₁ hI₂]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only
    rw [localCoefficientTest_derivative]
    ring
  have hright : (∫ x,g x*(localCoefficientTest hU ha ψ hψ).1 x)=∫ x,(a x*g x)*ψ.1 x := by
    apply integral_congr_ae
    apply ae_of_all
    intro x
    change g x*(a x*ψ.1 x)=(a x*g x)*ψ.1 x
    ring
  rw [hleft,hright] at hh
  have hL : (∫ x,(a x*f x)*coordinateDerivative i ψ.1 x)=∫ x,(f x*a x)*coordinateDerivative i ψ.1 x := by
    apply integral_congr_ae
    apply ae_of_all
    intro x
    ring
  have hR : (∫ x,(coordinateDerivative i a x*f x+a x*g x)*ψ.1 x)=
      (∫ x,(f x*coordinateDerivative i a x)*ψ.1 x)+(∫ x,(a x*g x)*ψ.1 x) := by
    rw [← integral_add hI₁ hI₃]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    ring
  rw [hL,hR]
  linarith

end GaussianTilt.MomentMapLinearDirichlet
