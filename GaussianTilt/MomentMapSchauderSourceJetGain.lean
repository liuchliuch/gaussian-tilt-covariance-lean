import GaussianTilt.MomentMapSchauderSourceHolderJets

/-! # Actual higher scalar source-jet Schauder gains -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2000000
open Set Matrix
open scoped ContDiff Gradient Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Each actual directional source jet gains a derivative from the true
repeated PDE. Coefficient and forcing C¹,α estimates are all derived from
the currently available highest source jet. -/
theorem exists_source_jet_third_order_holder [NeZero n] (k : ℕ)
    {φ V : KernelSpace n → ℝ} (hφ : ContDiff ℝ (↑(k+3) : WithTop ℕ∞) φ)
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hV : ContDiffOn ℝ (↑(k+3) : WithTop ℕ∞) V Ω)
    (hmap : ∀ x, gradient φ x ∈ Ω) (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (euclideanHessianMatrix φ x).det= -φ x+V (gradient φ x))
    (a : KernelSpace n) {R α : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1)
    (hφj : HolderJetOn α (k+3) φ (Metric.closedBall a (2*R)))
    (w : Fin (k+1) → KernelSpace n) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ R ∧ 0 < C ∧
      ContDiffOn ℝ 3 (scalarDerivativeJet (k+1) φ w) (Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (scalarDerivativeJet (k+1) φ w))) x‖ ≤ C) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (scalarDerivativeJet (k+1) φ w))) x-
          fderiv ℝ (fderiv ℝ (fderiv ℝ (scalarDerivativeJet (k+1) φ w))) y‖ ≤ C*‖x-y‖^α) := by
  let S := Metric.closedBall a (2*R)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hSc : Convex ℝ S := convex_closedBall _ _
  let A := fun x => (euclideanHessianMatrix φ x)⁻¹
  let u := scalarDerivativeJet (k+1) φ w
  let d := Fin.init w
  let v := w (Fin.last k)
  let f := iteratedEllipticForcing A (kernelDirectionalDerivative v φ)
    (kernelDirectionalDerivative v (sourceRHS φ V)) k d
  have hφ3 : ContDiff ℝ 3 φ := hφ.of_le (by exact_mod_cast (show 3 ≤ k+3 by omega))
  have hAc : ∀ i j, ContDiff ℝ 1 (fun x => A x i j) :=
    contDiff_matrix_inv_field (contDiff_euclideanHessianMatrix_entry hφ3) (fun x => (hpos x).det_pos.ne')
  have hAj := source_inverse_holderJetOn (m := k+1) (by omega)
    (by convert hφ using 1 <;> congr 1 <;> omega) (by convert hφj using 1 <;> omega)
    hpos hS hSc hα.le hα1.le
  have hforce := source_iterated_forcing_holderJetOn_one k hφ hφj hΩ hV hmap hpos hS hSc hα.le hα1.le d v
  have huc : ContDiff ℝ 2 u :=
    contDiff_scalarDerivativeJet (k+1) 2 (by convert hφ using 1 <;> congr 1 <;> omega) w
  have huj : HolderJetOn α 2 u S :=
    holderJetOn_scalarDerivativeJet (k+1) 2 (by convert hφ using 1 <;> congr 1 <;> omega)
      (by convert hφj using 1 <;> omega) w
  obtain ⟨Hu, hHu, _, huH⟩ := huj.fderiv.fderiv.value
  obtain ⟨Hf, hHf, _, hfH⟩ := hforce.2.fderiv.value
  let DA : KernelSpace n → Matrix (Fin n) (Fin n) (KernelSpace n →L[ℝ] ℝ) :=
    fun x i j => fderiv ℝ (fun z => A z i j) x
  have hDA : BoundedHolderOn α DA S :=
    BoundedHolderOn.pi (fun i => BoundedHolderOn.pi (fun j =>
      ((hAj i j).mono_order (show 1 ≤ k+1 by omega)).fderiv.value))
  obtain ⟨HA, hHA, _, hDAH⟩ := hDA
  have hAH : ∀ x ∈ S, ∀ y ∈ S, ∀ i j,
      ‖fderiv ℝ (fun z => A z i j) x-fderiv ℝ (fun z => A z i j) y‖ ≤ HA*‖x-y‖^α := by
    intro x hx y hy i j
    exact (Matrix.norm_entry_le_entrywise_sup_norm (DA x-DA y) (i := i) (j := j)).trans (hDAH x hx y hy)
  have heq : ∀ x, euclideanEllipticOperator (A x) u x=f x := by
    intro x
    have hh := source_iterated_elliptic_equation k hφ hpos hMA d v x
    have hw : Fin.snoc d v=w := Fin.snoc_init_self w
    rw [hw] at hh
    exact hh
  exact exists_linear_third_order_holder huc hforce.1 hAc a hR hHu hHf hHA hα hα1
    (fun x _ => (hpos x).inv) (fun x _ => heq x) hAH huH hfH

end GaussianTilt.MomentMapSchauder
