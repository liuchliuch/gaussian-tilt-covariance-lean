import GaussianTilt.MomentMapClassicalDirichletMixedBarrier

/-! # Generic actual elliptic barrier bounds for continuous boundary fields -/
noncomputable section
open Set Filter Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- A continuous field, smooth only in the interior, is controlled by its
actual lower elliptic forcing and an actual positive defining barrier. -/
theorem classical_dirichlet_upper_bound_with_barrier [NeZero n]
    {S : Set (CoordinateSpace n)} (hS : IsCompact S) {f w : CoordinateSpace n → ℝ}
    (hfc : ContinuousOn f S) (hwc : ContinuousOn w S)
    (hf : ∀ x ∈ interior S, ContDiffAt ℝ 2 f x)
    (hw : ∀ x ∈ interior S, ContDiffAt ℝ 2 w x)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ x ∈ interior S, (A x).PosDef)
    {K c B : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hLf : ∀ x ∈ interior S, -K ≤ linearizedMA (A x) f x)
    (hLw : ∀ x ∈ interior S, c ≤ linearizedMA (A x) w x)
    (hfb : ∀ x ∈ frontier S, f x ≤ B) (hwb : ∀ x ∈ frontier S, w x ≤ 0) :
    ∀ x ∈ S, f x ≤ B-(K/c)*w x := by
  have hC : 0 ≤ K/c := div_nonneg hK hc.le
  have hCc : (K/c)*c = K := div_mul_cancel₀ _ hc.ne'
  have hmax : ∀ x ∈ S, f x-B+(K/c)*w x ≤ 0 := by
    apply classical_dirichlet_maximum_principle hS
      ((hfc.sub continuousOn_const).add (continuousOn_const.mul hwc))
      (fun x hx => ((hf x hx).sub contDiffAt_const).add (contDiffAt_const.mul (hw x hx))) hA
    · intro x hx
      rw [linearizedMA_add_at _ ((hf x hx).sub contDiffAt_const) (contDiffAt_const.mul (hw x hx)),
        linearizedMA_sub_at _ (hf x hx) contDiffAt_const,linearizedMA_const,
        linearizedMA_const_mul_at _ (hw x hx)]
      have h := mul_le_mul_of_nonneg_left (hLw x hx) hC
      linarith [hLf x hx]
    · intro x hx
      have h := mul_nonpos_of_nonneg_of_nonpos hC (hwb x hx)
      linarith [hfb x hx]
  intro x hx
  linarith [hmax x hx]

/-- The corresponding two-sided estimate applies to intrinsic derivative
fields whose boundary values are bounded rather than zero. -/
theorem classical_dirichlet_abs_bound_with_barrier [NeZero n]
    {S : Set (CoordinateSpace n)} (hS : IsCompact S) {f w : CoordinateSpace n → ℝ}
    (hfc : ContinuousOn f S) (hwc : ContinuousOn w S)
    (hf : ∀ x ∈ interior S, ContDiffAt ℝ 2 f x)
    (hw : ∀ x ∈ interior S, ContDiffAt ℝ 2 w x)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ x ∈ interior S, (A x).PosDef)
    {K c B : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hLf : ∀ x ∈ interior S, |linearizedMA (A x) f x| ≤ K)
    (hLw : ∀ x ∈ interior S, c ≤ linearizedMA (A x) w x)
    (hfb : ∀ x ∈ frontier S, |f x| ≤ B) (hwb : ∀ x ∈ frontier S, w x ≤ 0) :
    ∀ x ∈ S, |f x| ≤ B-(K/c)*w x := by
  have hp := classical_dirichlet_upper_bound_with_barrier hS hfc hwc hf hw hA hK hc
    (fun x hx => (abs_le.mp (hLf x hx)).1) hLw
    (fun x hx => (le_abs_self _).trans (hfb x hx)) hwb
  have hm := classical_dirichlet_upper_bound_with_barrier hS (continuousOn_const.mul hfc) hwc
    (fun x hx => contDiffAt_const.mul (hf x hx)) hw hA hK hc
    (f := fun x => (-1:ℝ)*f x)
    (fun x hx => by rw [linearizedMA_const_mul_at _ (hf x hx)]; linarith [(abs_le.mp (hLf x hx)).2]) hLw
    (fun x hx => by have h := (abs_le.mp (hfb x hx)).1; linarith) hwb
  intro x hx
  apply abs_le.mpr
  constructor <;> linarith [hp x hx,hm x hx]

end GaussianTilt.MomentMapRegularity
