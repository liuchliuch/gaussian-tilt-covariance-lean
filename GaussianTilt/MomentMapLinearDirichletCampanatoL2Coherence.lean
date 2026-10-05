import GaussianTilt.MomentMapLinearDirichletFlatJetBounds

/-!
# Genuine mean-square coherence of constant weak-field approximants

The estimates below start from actual Bochner integrals of squared errors.
They control differences of approximating constants on a shared positive-
measure subset, without pointwise bounds or a representative assumption.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet

lemma norm_sub_sq_le_two_errors {F : Type*} [NormedAddCommGroup F]
    (a b z : F) : ‖a-b‖^2 ≤ 2*‖z-a‖^2+2*‖z-b‖^2 := by
  have ht : ‖a-b‖ ≤ ‖z-a‖+‖z-b‖ := by
    have he : a-b = (a-z)+(z-b) := by abel
    calc
      _ = ‖(a-z)+(z-b)‖ := congrArg norm he
      _ ≤ ‖a-z‖+‖z-b‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev a z]
  nlinarith [norm_nonneg (a-b),norm_nonneg (z-a),norm_nonneg (z-b),
    sq_nonneg (‖z-a‖-‖z-b‖)]

/-- A true shared-volume estimate for two L² approximating constants. -/
theorem l2_constant_coherence_sq {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    {μ : Measure X} {S : Set X} (hS : μ S ≠ ∞) (f : X → F) (a b : F)
    (ha : IntegrableOn (fun x => ‖f x-a‖^2) S μ)
    (hb : IntegrableOn (fun x => ‖f x-b‖^2) S μ) :
    μ.real S*‖a-b‖^2 ≤ 2*(∫ x in S, ‖f x-a‖^2 ∂μ)+2*(∫ x in S, ‖f x-b‖^2 ∂μ) := by
  have hc : IntegrableOn (fun _ : X => ‖a-b‖^2) S μ := integrableOn_const hS
  have ht := integral_mono hc ((ha.const_mul 2).add (hb.const_mul 2))
    (fun x => norm_sub_sq_le_two_errors a b (f x))
  simpa only [Pi.add_apply,integral_const,Measure.restrict_apply_univ,smul_eq_mul,
    integral_add (ha.const_mul 2) (hb.const_mul 2),integral_const_mul,measureReal_def] using ht

/-- The square-error bound is converted to a true norm bound, with no
square root or pointwise representative supplied as a premise. -/
theorem l2_constant_coherence {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    {μ : Measure X} {S : Set X} (hS : μ S ≠ ∞) {m E : ℝ}
    (hm : 0 < m) (hmS : m ≤ μ.real S) (hE : 0 ≤ E) (f : X → F) (a b : F)
    (ha : IntegrableOn (fun x => ‖f x-a‖^2) S μ)
    (hb : IntegrableOn (fun x => ‖f x-b‖^2) S μ)
    (hea : (∫ x in S, ‖f x-a‖^2 ∂μ) ≤ E)
    (heb : (∫ x in S, ‖f x-b‖^2 ∂μ) ≤ E) :
    ‖a-b‖ ≤ 2*Real.sqrt (E/m) := by
  have hs := l2_constant_coherence_sq hS f a b ha hb
  have hmnorm := mul_le_mul_of_nonneg_right hmS (sq_nonneg ‖a-b‖)
  have hdiv : 0 ≤ E/m := div_nonneg hE hm.le
  have hroot := Real.sq_sqrt hdiv
  have hroot0 := Real.sqrt_nonneg (E/m)
  have hd : E/m*m = E := div_mul_cancel₀ E hm.ne'
  have hsq : ‖a-b‖^2 ≤ 4*(E/m) := by
    apply (mul_le_mul_right hm).mp
    nlinarith
  nlinarith [norm_nonneg (a-b)]

/-- Errors on larger sets restrict to an actual common subset. This is the
form used for nested radii and overlapping balls at different centers. -/
theorem l2_constant_coherence_on_overlap {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    {μ : Measure X} {S A B : Set X} (hS : μ S ≠ ∞)
    (hSA : S ⊆ A) (hSB : S ⊆ B) {m E : ℝ}
    (hm : 0 < m) (hmS : m ≤ μ.real S) (hE : 0 ≤ E) (f : X → F) (a b : F)
    (ha : IntegrableOn (fun x => ‖f x-a‖^2) A μ)
    (hb : IntegrableOn (fun x => ‖f x-b‖^2) B μ)
    (hea : (∫ x in A, ‖f x-a‖^2 ∂μ) ≤ E)
    (heb : (∫ x in B, ‖f x-b‖^2 ∂μ) ≤ E) :
    ‖a-b‖ ≤ 2*Real.sqrt (E/m) := by
  apply l2_constant_coherence hS hm hmS hE f a b (ha.mono_set hSA) (hb.mono_set hSB)
  · exact (setIntegral_mono_set ha (ae_of_all _ (fun x => sq_nonneg ‖f x-a‖)) (ae_of_all _ (fun _ hx => hSA hx))).trans hea
  · exact (setIntegral_mono_set hb (ae_of_all _ (fun x => sq_nonneg ‖f x-b‖)) (ae_of_all _ (fun _ hx => hSB hx))).trans heb

end GaussianTilt.MomentMapLinearDirichlet
