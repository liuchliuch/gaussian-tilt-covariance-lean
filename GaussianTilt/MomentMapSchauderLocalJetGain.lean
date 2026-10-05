import GaussianTilt.MomentMapSchauderMultilinearCoordinates

/-! # Local highest-jet Hölder reconstruction after the scalar Schauder gain -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2200000
open Set
open scoped ContDiff Gradient
namespace GaussianTilt.MomentMapSchauder

lemma boundedHolderOn_iteratedFDeriv_succ {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S : Set E} {α : ℝ} {d : ℕ}
    (hf : BoundedHolderOn α (iteratedFDeriv ℝ d (fderiv ℝ f)) S) :
    BoundedHolderOn α (iteratedFDeriv ℝ (d+1) f) S := by
  have hh := hf.map (continuousMultilinearCurryRightEquiv' ℝ d E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
  apply hh.congr
  intro x hx
  exact (iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := f) (x := x)).symm

lemma boundedHolderOn_iteratedFDeriv_three {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S : Set E} {α : ℝ}
    (hf : BoundedHolderOn α (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) S) :
    BoundedHolderOn α (iteratedFDeriv ℝ 3 f) S := by
  have h0 : BoundedHolderOn α (iteratedFDeriv ℝ 0 (fderiv ℝ (fderiv ℝ (fderiv ℝ f)))) S :=
    hf.map (continuousMultilinearCurryFin0 ℝ E (E →L[ℝ] E →L[ℝ] E →L[ℝ] F)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact boundedHolderOn_iteratedFDeriv_succ (f := f)
    (boundedHolderOn_iteratedFDeriv_succ (f := fderiv ℝ f)
      (boundedHolderOn_iteratedFDeriv_succ (f := fderiv ℝ (fderiv ℝ f)) h0))

open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma scalarDerivativeJet_cons_three (k : ℕ) {φ : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ (↑(k+4) : WithTop ℕ∞) φ)
    (w : Fin (k+1) → KernelSpace n) (a b c x : KernelSpace n) :
    iteratedFDeriv ℝ (k+4) φ x (Fin.cons a (Fin.cons b (Fin.cons c w)))=
      fderiv ℝ (fderiv ℝ (fderiv ℝ (scalarDerivativeJet (k+1) φ w))) x a b c := by
  have hc : ContDiff ℝ 3 (scalarDerivativeJet (k+1) φ w) :=
    contDiff_scalarDerivativeJet (k+1) 3 (by convert hφ using 1 <;> congr 1 <;> omega) w
  have hc2 : ContDiff ℝ 2 (scalarDerivativeJet (k+1) φ w) := hc.of_le (by norm_num)
  have h3 : ContDiff ℝ (↑(k+3) : WithTop ℕ∞) φ := hφ.of_le (by exact_mod_cast (show k+3 ≤ k+4 by omega))
  have h2 : ContDiff ℝ (↑(k+2) : WithTop ℕ∞) φ := hφ.of_le (by exact_mod_cast (show k+2 ≤ k+4 by omega))
  change scalarDerivativeJet (k+4) φ (Fin.cons a (Fin.cons b (Fin.cons c w))) x=_
  rw [scalarDerivativeJet_succ hφ]
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [scalarDerivativeJet_succ h3]
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [scalarDerivativeJet_succ h2]
  simp only [Fin.cons_zero, Fin.tail_cons]
  have he : kernelDirectionalDerivative b (kernelDirectionalDerivative c (scalarDerivativeJet (k+1) φ w))=
      fun y => fderiv ℝ (fderiv ℝ (scalarDerivativeJet (k+1) φ w)) y b c := by
    funext y
    exact directionalHessian_eq_secondFrechet hc2 y c b
  rw [he]
  have hD := ((hc.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiable le_rfl x
  unfold kernelDirectionalDerivative
  rw [fderiv_clm_apply_const_apply (hD.clm_apply (differentiableAt_const _)), fderiv_clm_apply_const_apply hD]

/-- Finite canonical-basis reconstruction converts the actual scalar-jet
gains into a Hölder estimate for the full next source derivative tensor. -/
theorem exists_source_next_holderJetOn [NeZero n] (k : ℕ)
    {φ V : KernelSpace n → ℝ} (hφ : ContDiff ℝ (↑(k+3) : WithTop ℕ∞) φ)
    (hφnext : ContDiff ℝ (↑(k+4) : WithTop ℕ∞) φ)
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hV : ContDiffOn ℝ (↑(k+3) : WithTop ℕ∞) V Ω)
    (hmap : ∀ x, gradient φ x ∈ Ω) (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (euclideanHessianMatrix φ x).det= -φ x+V (gradient φ x))
    (a : KernelSpace n) {R α : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1)
    (hφj : HolderJetOn α (k+3) φ (Metric.closedBall a (2*R))) :
    ∃ r : ℝ, 0 < r ∧ HolderJetOn α (k+4) φ (Metric.closedBall a (2*r)) := by
  let f : (Fin (k+4) → Fin n) → KernelSpace n → ℝ := fun q x =>
    iteratedFDeriv ℝ (k+4) φ x (fun i => EuclideanSpace.basisFun (Fin n) ℝ (q i))
  have hcoords : ∀ q, ∃ r : ℝ, 0 < r ∧ BoundedHolderOn α (f q) (Metric.closedBall a r) := by
    intro q
    let z : Fin (k+4) → KernelSpace n := fun i => EuclideanSpace.basisFun (Fin n) ℝ (q i)
    let w := Fin.tail (Fin.tail (Fin.tail z))
    obtain ⟨r, C, hr, _, hC, _, hb, hh⟩ :=
      exists_source_jet_third_order_holder k hφ hΩ hV hmap hpos hMA a hR hα hα1 hφj w
    have hsub : Metric.closedBall a (r/2) ⊆ Metric.ball a r := Metric.closedBall_subset_ball (by linarith)
    have hfield : BoundedHolderOn α
        (fderiv ℝ (fderiv ℝ (fderiv ℝ (scalarDerivativeJet (k+1) φ w)))) (Metric.closedBall a (r/2)) :=
      ⟨C, hC.le, fun x hx => hb x (hsub hx), fun x hx y hy => hh x (hsub hx) y (hsub hy)⟩
    let L := (ContinuousLinearMap.apply ℝ ℝ (Fin.tail (Fin.tail z) 0)).comp
      ((ContinuousLinearMap.apply ℝ (KernelSpace n →L[ℝ] ℝ) (Fin.tail z 0)).comp
        (ContinuousLinearMap.apply ℝ (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) (z 0)))
    refine ⟨r/2, by linarith, (hfield.map L).congr ?_⟩
    intro x hx
    have hz : Fin.cons (z 0) (Fin.cons (Fin.tail z 0) (Fin.cons (Fin.tail (Fin.tail z) 0) w))=z := by
      dsimp [w]
      simp only [Fin.cons_self_tail]
    have he := scalarDerivativeJet_cons_three k hφnext w (z 0) (Fin.tail z 0) (Fin.tail (Fin.tail z) 0) x
    rw [hz] at he
    exact he.symm
  obtain ⟨r, hr, hcommon⟩ := exists_common_closedBall_holder a hcoords
  have htop : BoundedHolderOn α (iteratedFDeriv ℝ (k+4) φ) (Metric.closedBall a r) :=
    boundedHolderOn_multilinear_of_basis (k+4) hcommon
  have hj := holderJetOn_of_top hφnext (isCompact_closedBall a r) (convex_closedBall a r) hα.le hα1.le htop
  refine ⟨r/2, by linarith, ?_⟩
  convert hj using 1
  congr 1
  ring

end GaussianTilt.MomentMapSchauder
