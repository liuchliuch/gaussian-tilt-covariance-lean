import GaussianTilt.MomentMapLinearDirichletVariableWeakClosedGeometry

/-! # Actual common boundary patches for the finite family of tangential fields -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 1000

lemma exists_common_positive_radius {ι:Type*} [Fintype ι]
    {R:ℝ} (hR:0<R) (r:ι→ℝ) (hr:∀i,0<r i) :
    ∃s:ℝ,0<s ∧ s<R ∧ ∀i,s<r i := by
  classical
  let f:Option ι→ℝ := fun i=>i.elim R r
  have hf:∀i,0<f i := by intro i; cases i <;> simp only [f,Option.elim] <;> aesop
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image Finset.univ f ⟨none,Finset.mem_univ _⟩
  refine ⟨f i/2,div_pos (hf i) (by norm_num),?_,?_⟩
  · have hm := hmin none (Finset.mem_univ _)
    change f i≤R at hm
    linarith [hf i]
  · intro k
    have hm := hmin (some k) (Finset.mem_univ _)
    change f i≤r k at hm
    linarith [hf i]

def assembledTangentRows (j:Fin n)
    (Q:{k:Fin n//k≠j} → CoordinateSpace n → CoordinateSpace n)
    (x:CoordinateSpace n) (k i:Fin n) : ℝ :=
  if hk:k≠j then Q ⟨k,hk⟩ x i else 0

/-- Finite selection constructs a genuine common positive closed patch.
The unused normal row is set to zero; every tangential row keeps its actual
AE weak-gradient identity and its proved Hölder exponent. -/
theorem exists_common_tangential_field_patch (j:Fin n) {R:ℝ} (hR:0<R)
    (r:{k:Fin n//k≠j} → ℝ) (hr:∀k,0<r k)
    (W:{k:Fin n//k≠j} → VolumeJet n)
    (Q:{k:Fin n//k≠j} → CoordinateSpace n → CoordinateSpace n)
    {β:ℝ} (hQc:∀k,ContinuousOn (Q k) (coordinateClosedHalfBall j (r k)))
    (hQH:∀k,BoundedHolderOn β (Q k) (coordinateClosedHalfBall j (r k)))
    (hQAE:∀k i,∀ᵐx∂volume,x∈coordinateHalfBall j (r k) → Q k x i=W k i.succ x) :
    ∃s:ℝ,0<s ∧ s<R ∧
      BoundedHolderOn β (assembledTangentRows j Q) (coordinateClosedHalfBall j s) ∧
      (∀k i,ContinuousOn (fun x=>assembledTangentRows j Q x k i) (coordinateClosedHalfBall j s)) ∧
      (∀k (hk:k≠j) i,∀ᵐx∂volume,x∈coordinateHalfBall j s → assembledTangentRows j Q x k i=W ⟨k,hk⟩ i.succ x) ∧
      ∀x i,assembledTangentRows j Q x j i=0 := by
  obtain ⟨s,hs,hsR,hsr⟩ := exists_common_positive_radius hR r hr
  have hsmall (k:{k:Fin n//k≠j}) : coordinateClosedHalfBall j s⊆coordinateClosedHalfBall j (r k) :=
    coordinateClosedHalfBall_mono j (hsr k).le
  have hentry (k i:Fin n) : BoundedHolderOn β (fun x=>assembledTangentRows j Q x k i) (coordinateClosedHalfBall j s) := by
    by_cases hk:k≠j
    · simpa only [assembledTangentRows,dif_pos hk] using
        ((hQH ⟨k,hk⟩).mono (hsmall ⟨k,hk⟩)).map (ContinuousLinearMap.proj i)
    · simpa only [assembledTangentRows,dif_neg hk] using
        (BoundedHolderOn.const (E:=CoordinateSpace n) (S:=coordinateClosedHalfBall j s) (α:=β) (0:ℝ))
  refine ⟨s,hs,hsR,BoundedHolderOn.pi (fun k=>BoundedHolderOn.pi (hentry k)),?_,?_,?_⟩
  · intro k i
    by_cases hk:k≠j
    · simpa only [assembledTangentRows,dif_pos hk] using
        (continuous_apply i).comp_continuousOn ((hQc ⟨k,hk⟩).mono (hsmall ⟨k,hk⟩))
    · simpa only [assembledTangentRows,dif_neg hk] using
        (continuousOn_const : ContinuousOn (fun _:CoordinateSpace n=>(0:ℝ)) (coordinateClosedHalfBall j s))
  · intro k hk i
    filter_upwards [hQAE ⟨k,hk⟩ i] with x hx hxS
    rw [assembledTangentRows,dif_pos hk]
    exact hx (coordinateHalfBall_radius_mono j (hsr ⟨k,hk⟩).le hxS)
  · intro x i
    simp [assembledTangentRows]

end GaussianTilt.MomentMapLinearDirichlet
