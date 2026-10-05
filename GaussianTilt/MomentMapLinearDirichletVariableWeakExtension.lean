import GaussianTilt.MomentMapLinearDirichletVariableWeakCoefficients
import GaussianTilt.MomentMapLinearDirichletVariableLoads

/-! # Globally bounded coefficient and load representatives of a chart patch -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 1000

/-- Outside the working patch use the fixed positive scalar matrix. -/
def ellipticPatchExtension (S:Set (CoordinateSpace n))
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (lam:ℝ) (x:CoordinateSpace n)  := 
  by classical exact if x ∈ S then A x else lam • (1:Matrix (Fin n) (Fin n) ℝ)

lemma ellipticPatchExtension_eq {S:Set (CoordinateSpace n)}
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (lam:ℝ) {x:CoordinateSpace n} (hx:x ∈ S) :
    ellipticPatchExtension S A lam x=A x  := by
  classical
  exact if_pos hx

lemma ellipticPatchExtension_measurable {S : Set (CoordinateSpace n)} (hS : MeasurableSet S)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i k, Measurable (fun x => A x i k)) (lam : ℝ) (i k : Fin n) :
    Measurable (fun x => ellipticPatchExtension S A lam x i k) := by
  classical
  have hh : Measurable (S.piecewise (fun x => A x i k) (fun _ => (lam • (1 : Matrix (Fin n) (Fin n) ℝ)) i k)) :=
    (hA i k).piecewise hS measurable_const
  convert hh using 1
  funext x
  by_cases hx : x ∈ S <;> simp [ellipticPatchExtension, Set.piecewise, hx]

lemma ellipticPatchExtension_bound {S:Set (CoordinateSpace n)}
    {A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {lam K:ℝ} (hlam:0 ≤ lam)
    (hA: ∀  x  ∈  S,  ∀  i k, |A x i k| ≤ K) (x:CoordinateSpace n) (i k:Fin n) :
    |ellipticPatchExtension S A lam x i k| ≤ max K lam  :=  by
  by_cases hx:x ∈ S
  · rw [ellipticPatchExtension_eq A lam hx]
    exact (hA x hx i k).trans (le_max_left _ _)
  · simp only [ellipticPatchExtension,if_neg hx,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
    split_ifs
    · simpa only [mul_one,abs_of_nonneg hlam] using le_max_right K lam
    · simpa only [mul_zero,abs_zero] using hlam.trans (le_max_right K lam)

lemma ellipticPatchExtension_elliptic {S:Set (CoordinateSpace n)}
    {A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {lam:ℝ}
    (hell: ∀  x  ∈  S,  ∀  z : Fin n  →  ℝ, lam*( ∑  i, (z i)^2) ≤ z ⬝ᵥ (A x *ᵥ z))
    (x:CoordinateSpace n) (z:Fin n → ℝ) :
    lam*( ∑  i, (z i)^2) ≤ z ⬝ᵥ (ellipticPatchExtension S A lam x *ᵥ z)  :=  by
  by_cases hx:x ∈ S
  · rw [ellipticPatchExtension_eq A lam hx]
    exact hell x hx z
  · simp only [ellipticPatchExtension,if_neg hx,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul]
    simp only [dotProduct,smul_eq_mul,← sq]
    exact le_rfl

lemma measurable_divergenceChartCoefficient {F ψ : CoordinateSpace n → CoordinateSpace n}
    (hF : ContDiff ℝ ∞ F) (hψ : ContDiff ℝ ∞ ψ) (i k : Fin n) :
    Measurable (fun x => divergenceChartCoefficient F ψ x i k) := by
  apply Continuous.measurable
  change Continuous (fun x => |(fderiv ℝ ψ x).det| * ∑ l, chartJacobian F (ψ x) i l * chartJacobian F (ψ x) k l)
  exact (contDiff_chartJacobian_det hψ).continuous.abs.mul
    (continuous_finset_sum Finset.univ (fun l _ => ((contDiff_chartJacobian_entry hF i l).continuous.comp hψ.continuous).mul
      ((contDiff_chartJacobian_entry hF k l).continuous.comp hψ.continuous)))

/-- The actual Jacobian-weighted load is L² on every compact chart patch,
by the proved measure-distortion bound, with its literal representative. -/
theorem exists_masked_jacobian_load {S:Set (CoordinateSpace n)} (hS:IsCompact S)
    {ψ:CoordinateSpace n → CoordinateSpace n} (hψ:ContDiff ℝ ∞ ψ)
    {C:ℝ} (hC:0 ≤ C) (hmap:(volume.restrict S).map ψ ≤ ENNReal.ofReal (C^2) • volume)
    (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n))) :
     ∃ g:Lp ℝ 2 (volume:Measure (CoordinateSpace n)),
      g=ᵐ[volume] S.indicator (fun x=>|(fderiv ℝ ψ x).det| *f (ψ x))  :=  by
  let a  :=  S.indicator (fun x=>|(fderiv ℝ ψ x).det|)
  have ham : AEStronglyMeasurable a volume  := 
    ((contDiff_chartJacobian_det hψ).continuous.abs.measurable.indicator hS.measurableSet).aestronglyMeasurable
  obtain ⟨B,hB⟩  :=  hS.exists_bound_of_continuousOn
    ((contDiff_chartJacobian_det hψ).continuous.abs.continuousOn)
  have hab :  ∀ᵐ x∂volume,|a x| ≤ max B 0  :=  by
    apply ae_of_all
    intro x
    by_cases hx:x ∈ S
    · simpa only [a,indicator_of_mem hx,Real.norm_eq_abs] using (hB x hx).trans (le_max_left B 0)
    · simp only [a,indicator_of_notMem hx,abs_zero]
      exact le_max_right _ _
  let p  :=  maskedL2Composition hS.measurableSet hψ.continuous.measurable hC hmap f
  let g  :=  boundedL2Multiplier ham (le_max_right B 0) hab p
  refine ⟨g,?_⟩
  filter_upwards [boundedL2Multiplier_ae ham (le_max_right B 0) hab p,
    maskedL2Composition_ae hS.measurableSet hψ.continuous.measurable hC hmap f] with x hx hp
  change g x=_
  rw [show g x=a x*p x from hx,hp]
  by_cases hs:x ∈ S
  · simp only [a,indicator_of_mem hs]
  · simp only [a,indicator_of_notMem hs,mul_zero]

end GaussianTilt.MomentMapLinearDirichlet
