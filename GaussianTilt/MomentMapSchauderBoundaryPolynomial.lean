import GaussianTilt.MomentMapSchauderBoundaryRescale
import GaussianTilt.MomentMapCampanatoHalfBallJets

/-! # Actual derivatives of the symmetric boundary polynomial -/
noncomputable section
set_option maxSynthPendingDepth 1000
open Set InnerProductSpace
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def operatorBilinear (T : KernelSpace n →L[ℝ] KernelSpace n) :
    KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ :=
  ((toDual ℝ (KernelSpace n)).toContinuousLinearEquiv.toContinuousLinearMap).comp T

@[simp] lemma operatorBilinear_apply (T : KernelSpace n →L[ℝ] KernelSpace n) (v w : KernelSpace n) :
    operatorBilinear T v w=inner ℝ (T v) w := rfl

lemma norm_operatorBilinear (T : KernelSpace n →L[ℝ] KernelSpace n) : ‖operatorBilinear T‖=‖T‖ := by
  apply le_antisymm
  · apply (operatorBilinear T).opNorm_le_bound (norm_nonneg T)
    intro v
    rw [show ‖operatorBilinear T v‖=‖T v‖ from (toDual ℝ (KernelSpace n)).norm_map (T v)]
    exact T.le_opNorm v
  · apply T.opNorm_le_bound (norm_nonneg (operatorBilinear T))
    intro v
    rw [← (toDual ℝ (KernelSpace n)).norm_map (T v)]
    exact (operatorBilinear T).le_opNorm v

lemma operatorBilinear_sub (T S : KernelSpace n →L[ℝ] KernelSpace n) :
    operatorBilinear (T-S)=operatorBilinear T-operatorBilinear S := by
  ext v w
  simp only [operatorBilinear_apply,ContinuousLinearMap.sub_apply,inner_sub_left]

lemma quadraticJet_eq_flatTaylorPolynomial (p : KernelSpace n) (T : KernelSpace n →L[ℝ] KernelSpace n) :
    quadraticJet 0 p 0 T=flatTaylorPolynomial (toDual ℝ (KernelSpace n) p) (operatorBilinear T) := by
  funext x
  simp only [quadraticJet,flatTaylorPolynomial,sub_zero,zero_add,operatorBilinear_apply]
  rfl

lemma contDiff_quadraticJet_zero (p : KernelSpace n) (T : KernelSpace n →L[ℝ] KernelSpace n) :
    ContDiff ℝ ∞ (quadraticJet 0 p 0 T) := by
  rw [quadraticJet_eq_flatTaylorPolynomial]
  exact contDiff_flatTaylorPolynomial _ _

lemma fderiv_quadraticJet_zero (p : KernelSpace n) (T : KernelSpace n →L[ℝ] KernelSpace n)
    (hT : ∀ v w, inner ℝ (T v) w=inner ℝ v (T w)) (x : KernelSpace n) :
    fderiv ℝ (quadraticJet 0 p 0 T) x=toDual ℝ (KernelSpace n) (p+T x) := by
  ext v
  rw [quadraticJet_eq_flatTaylorPolynomial,fderiv_flatTaylorPolynomial]
  change inner ℝ p v+(1/2:ℝ)*(inner ℝ (T v) x+inner ℝ (T x) v)=inner ℝ (p+T x) v
  have hs : inner ℝ (T v) x=inner ℝ (T x) v := (hT v x).trans (real_inner_comm _ _)
  rw [hs,inner_add_left]
  ring

lemma secondFrechet_quadraticJet_zero (p : KernelSpace n) (T : KernelSpace n →L[ℝ] KernelSpace n)
    (hT : ∀ v w, inner ℝ (T v) w=inner ℝ v (T w)) (x : KernelSpace n) :
    fderiv ℝ (fderiv ℝ (quadraticJet 0 p 0 T)) x=operatorBilinear T := by
  have he : fderiv ℝ (quadraticJet 0 p 0 T) =fun y => toDual ℝ (KernelSpace n) (p+T y) :=
    funext (fderiv_quadraticJet_zero p T hT)
  rw [he]
  exact (((toDual ℝ (KernelSpace n)).toContinuousLinearEquiv.hasFDerivAt).comp x
    (T.hasFDerivAt.const_add p)).fderiv

lemma secondFrechet_sub_at {u v : KernelSpace n → ℝ} {x : KernelSpace n}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    fderiv ℝ (fderiv ℝ (fun y => u y-v y)) x=
      fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ v) x := by
  simp only [sub_eq_add_neg]
  rw [secondFrechet_add_at hu hv.neg]
  have he : fderiv ℝ (fun y => -v y)=fun y => -fderiv ℝ v y := funext (fun y => fderiv_fun_neg)
  rw [he,fderiv_fun_neg]

end GaussianTilt.MomentMapSchauder
