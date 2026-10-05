import GaussianTilt.MomentMapLinearDirichletVariableWeakTangentialVectorLoad
import GaussianTilt.MomentMapLinearDirichletVariableWeakLocalData
import GaussianTilt.MomentMapSchauderBoundedHolder

/-! # Actual Hölder forcing moduli for the two weak-boundary regularity passes -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 1000

lemma boundedHolderOn_lower_exponent {X Y:Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {S:Set X} {f:X→Y} {α β:ℝ} (hβ:0≤β) (hβα:β≤α)
    (hf:BoundedHolderOn α f S) : BoundedHolderOn β f S := by
  obtain ⟨C,hC,hb,hh⟩ := hf
  refine ⟨2*C,by positivity,fun x hx=>(hb x hx).trans (by linarith),?_⟩
  intro x hx y hy
  by_cases hd:‖x-y‖≤1
  · have hp := Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (x-y)) hd hβ hβα
    exact (hh x hx y hy).trans ((mul_le_mul_of_nonneg_left hp hC).trans
      (mul_le_mul_of_nonneg_right (by linarith : C≤2*C) (Real.rpow_nonneg (norm_nonneg _) _)))
  · have hn := (norm_sub_le (f x) (f y)).trans (add_le_add (hb x hx) (hb y hy))
    have hp := Real.one_le_rpow (le_of_not_ge hd) hβ
    nlinarith

lemma boundedHolderOn_comp_lipschitz {X Y Z:Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    {S:Set X} {T:Set Y} {f:Y→Z} {ψ:X→Y} {α:ℝ} (hα:0≤α)
    (hf:BoundedHolderOn α f T) {L:ℝ≥0} (hψ:LipschitzOnWith L ψ S) (hmap:MapsTo ψ S T) :
    BoundedHolderOn α (f ∘ ψ) S := by
  obtain ⟨C,hC,hb,hh⟩ := hf
  let K:ℝ := C*(1+(L:ℝ)^α)
  have hK:0≤K := by dsimp [K]; positivity
  have hCK:C≤K := by dsimp [K]; nlinarith [Real.rpow_nonneg L.coe_nonneg α]
  refine ⟨K,hK,fun x hx=>(hb _ (hmap hx)).trans hCK,?_⟩
  intro x hx y hy
  have hp := Real.rpow_le_rpow (norm_nonneg (ψ x-ψ y)) (hψ.norm_sub_le hx hy) hα
  rw [Real.mul_rpow L.coe_nonneg (norm_nonneg (x-y))] at hp
  have ht := (hh _ (hmap hx) _ (hmap hy)).trans (mul_le_mul_of_nonneg_left hp hC)
  change ‖f (ψ x)-f (ψ y)‖≤K*‖x-y‖^α
  apply ht.trans
  dsimp [K]
  nlinarith [Real.rpow_nonneg (norm_nonneg (x-y)) α]

/-- Continuity of an actual derivative field on a compact convex patch
makes the field Lipschitz there, including its boundary. No boundary
extension or pre-existing Lipschitz assumption is needed. -/
lemma boundedHolderOn_of_continuous_within_derivative {X Y:Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {S:Set X} (hS:IsCompact S) (hc:Convex ℝ S) {f:X→Y} {Df:X→X→L[ℝ]Y}
    (hf:∀x∈S,HasFDerivWithinAt f (Df x) S x) (hDf:ContinuousOn Df S)
    {α:ℝ} (hα:0≤α) (hα1:α≤1) : BoundedHolderOn α f S := by
  have hfc:ContinuousOn f S := fun x hx=>(hf x hx).continuousWithinAt
  obtain ⟨B,hB⟩ := hS.exists_bound_of_continuousOn hfc
  obtain ⟨D,hD⟩ := hS.exists_bound_of_continuousOn hDf
  let M := max B 0
  let L := max D 0
  have hM:0≤M := le_max_right _ _
  have hL:0≤L := le_max_right _ _
  have hb:∀x∈S,‖f x‖≤M := fun x hx=>(hB x hx).trans (le_max_left _ _)
  have hd:∀x∈S,‖Df x‖≤L := fun x hx=>(hD x hx).trans (le_max_left _ _)
  have hLip:∀x∈S,∀y∈S,‖f x-f y‖≤L*‖x-y‖ := fun x hx y hy=>
    hc.norm_image_sub_le_of_norm_hasFDerivWithin_le hf hd hy hx
  refine ⟨L+2*M,by positivity,fun x hx=>(hb x hx).trans (by linarith),?_⟩
  simpa only [Real.one_rpow,mul_one] using
    holder_bound_of_sup_and_lipschitz hM hL hα hα1 zero_lt_one hb hLip

/-- The genuine Jacobian-weighted chart forcing preserves the exponent
of the original scalar datum on compact convex coordinate patches. -/
theorem boundedHolderOn_chart_scalar_forcing {V S:Set (CoordinateSpace n)}
    (hV:IsOpen V) (hS:IsCompact S) (hc:Convex ℝ S) (hSV:S⊆V)
    {F ψ:CoordinateSpace n → CoordinateSpace n} (hF:ContDiff ℝ ∞ F) (hψ:ContDiff ℝ ∞ ψ)
    (hleft:∀ x ∈ V, F (ψ x)=x) {f:CoordinateSpace n → ℝ} {α:ℝ} (hα:0≤α) (hα1:α≤1)
    (hf:BoundedHolderOn α f (ψ '' S)) :
    BoundedHolderOn α (fun x=>|(fderiv ℝ ψ x).det| * f (ψ x)) S := by
  obtain ⟨L,hLip⟩ := exists_lipschitzOnWith_compact_convex_of_contDiffOn isOpen_univ hS hc
    (subset_univ S) (hψ.of_le (by simp)).contDiffOn
  have hcomp := boundedHolderOn_comp_lipschitz hα hf hLip (fun x hx=>mem_image_of_mem ψ hx)
  have hd : ContDiffOn ℝ ∞ (fun x=>|(fderiv ℝ ψ x).det|) V :=
    (contDiff_chartJacobian_det hψ).contDiffOn.abs (fun x hx=>
      jacobian_ne_zero_of_local_left_inverse hV (hF.differentiable (by simp))
        (hψ.differentiable (by simp)).differentiableOn hleft hx)
  obtain ⟨B,hB,hbd,hh⟩ := exists_contDiffOn_holder_bound_on_compact_convex hV
    (hd.of_le (by simp)) hS hc hSV hα hα1
  exact (show BoundedHolderOn α (fun x=>|(fderiv ℝ ψ x).det|) S from ⟨B,hB.le,hbd,hh⟩).mul hcomp

def differentiatedLoadFunction {X:Type*} (a:Fin n) (f:X→ℝ)
    (D:X→Matrix (Fin n) (Fin n) ℝ) (q:X→Fin n→ℝ) (x:X) (i:Fin n) : ℝ :=
  -(if i=a then f x else 0)-∑k:Fin n,D x i k*q x k

/-- Hölder regularity of the literal differentiated divergence load.
This is used first at the smaller exponent, and again at the original
forcing exponent after the actual first-pass Hessian gives Lipschitz gradient. -/
theorem boundedHolderOn_differentiatedLoad {X:Type*} [NormedAddCommGroup X]
    {S:Set X} (a:Fin n) {f:X→ℝ} {D:X→Matrix (Fin n) (Fin n) ℝ} {q:X→Fin n→ℝ} {α:ℝ}
    (hf:BoundedHolderOn α f S) (hD:∀i k,BoundedHolderOn α (fun x=>D x i k) S)
    (hq:∀k,BoundedHolderOn α (fun x=>q x k) S) :
    ∀i,BoundedHolderOn α (fun x=>differentiatedLoadFunction a f D q x i) S := by
  intro i
  have hs : BoundedHolderOn α (fun x=>∑k:Fin n,D x i k*q x k) S :=
    BoundedHolderOn.finset_sum Finset.univ (fun k _=>(hD i k).mul (hq k))
  have hif : BoundedHolderOn α (fun x=>if i=a then f x else 0) S := by
    by_cases hi:i=a
    · simpa only [if_pos hi] using hf
    · simpa only [if_neg hi] using (BoundedHolderOn.const (E:=X) (S:=S) (α:=α) (0:ℝ))
  exact hif.neg.sub hs

end GaussianTilt.MomentMapLinearDirichlet
