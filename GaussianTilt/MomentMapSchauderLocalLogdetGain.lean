import GaussianTilt.MomentMapSchauderLocalEquation
import GaussianTilt.MomentMapSchauderLocalReconstruction

/-! # Higher scalar jet gain for a genuinely local constant-logdet equation -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2200000
open Set Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

theorem exists_local_logdet_jet_third_order [NeZero n] (k : ℕ)
    {φ : KernelSpace n → ℝ} (hφ : ContDiff ℝ (↑(k+3) : WithTop ℕ∞) φ)
    (a : KernelSpace n) {R α c : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ Metric.ball a (4*R), (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x ∈ Metric.ball a (4*R), Real.log (euclideanHessianMatrix φ x).det=c)
    (hφj : HolderJetOn α (k+3) φ (Metric.closedBall a (2*R)))
    (w : Fin (k+1) → KernelSpace n) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ R ∧ 0 < C ∧
      ContDiffOn ℝ 3 (scalarDerivativeJet (k+1) φ w) (Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (scalarDerivativeJet (k+1) φ w))) x‖ ≤ C) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (scalarDerivativeJet (k+1) φ w))) x-
          fderiv ℝ (fderiv ℝ (fderiv ℝ (scalarDerivativeJet (k+1) φ w))) y‖ ≤ C*‖x-y‖^α) := by
  let U := Metric.ball a (4*R)
  let T := Metric.ball a R
  let S := Metric.closedBall a (2*(R/4))
  have hS : IsCompact S := isCompact_closedBall _ _
  have hSc : Convex ℝ S := convex_closedBall _ _
  have hST : S ⊆ T := Metric.closedBall_subset_ball (by linarith)
  have hTU : T ⊆ U := Metric.ball_subset_ball (by linarith)
  have hSU : S ⊆ U := hST.trans hTU
  have hSbig : S ⊆ Metric.closedBall a (2*R) := Metric.closedBall_subset_closedBall (by linarith)
  have hφj' := hφj.mono_set hSbig
  let χ := scaledInteriorCutoff a R
  let A := cutoffCoefficient 1 (fun y => (euclideanHessianMatrix φ y)⁻¹) χ
  have hsχ : tsupport χ ⊆ U := (tsupport_scaledInteriorCutoff_subset a hR).trans
    (Metric.closedBall_subset_ball (by linarith))
  have hAc : ∀ i j, ContDiff ℝ (↑(k+1) : WithTop ℕ∞) (fun x => A x i j) :=
    contDiff_cutoff_inverse_coefficients (by convert hφ using 1 <;> congr 1 <;> omega)
      (contDiff_infty.mp (scaledInteriorCutoff_contDiff a R) (k+1)) Metric.isOpen_ball hsχ hpos
  have hAe : ∀ x ∈ T, A x=(euclideanHessianMatrix φ x)⁻¹ := fun x hx =>
    cutoffCoefficient_eq_of_one (scaledInteriorCutoff_one hR
      (Metric.mem_closedBall.mp (Metric.ball_subset_closedBall hx)))
  have hInvj := local_source_inverse_holderJetOn (m := k+1) (by omega)
    (by convert hφ using 1 <;> congr 1 <;> omega) Metric.isOpen_ball
    (by convert hφj' using 1 <;> omega) hpos hS hSc hSU hα.le hα1.le
  have hAj : ∀ i j, HolderJetOn α (k+1) (fun x => A x i j) S := by
    intro i j
    exact (hInvj i j).congr_of_eqOn_open Metric.isOpen_ball hST
      (fun x hx => congrFun (congrFun (hAe x hx).symm i) j)
  let d := Fin.init w
  let v := w (Fin.last k)
  let u := scalarDerivativeJet (k+1) φ w
  let f := iteratedEllipticForcing A (kernelDirectionalDerivative v φ) (fun _ => 0) k d
  have hDφ : ContDiff ℝ (↑(k+2) : WithTop ℕ∞) (kernelDirectionalDerivative v φ) :=
    contDiff_kernelDirectionalDerivative (by simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc] using hφ) v
  have hDφj : HolderJetOn α (k+2) (kernelDirectionalDerivative v φ) S :=
    HolderJetOn.directional (by convert hφ using 1 <;> congr 1 <;> omega)
      (by convert hφj' using 1 <;> omega) v
  have hzeroj : HolderJetOn α (k+1) (fun _ : KernelSpace n => (0 : ℝ)) S :=
    holderJetOn_of_contDiff_one_more contDiff_const hS hSc hα.le hα1.le
  have hfc : ContDiff ℝ 1 f := contDiff_iteratedEllipticForcing k 1
    (by convert hDφ using 1 <;> congr 1 <;> omega) hAc contDiff_const d
  have hfj : HolderJetOn α 1 f S := holderJetOn_iteratedEllipticForcing k 1
    (by convert hDφ using 1 <;> congr 1 <;> omega) (by convert hDφj using 1 <;> omega)
    hAc hAj contDiff_const hzeroj hS hSc hα.le hα1.le d
  have huc : ContDiff ℝ 2 u := contDiff_scalarDerivativeJet (k+1) 2
    (by convert hφ using 1 <;> congr 1 <;> omega) w
  have huj : HolderJetOn α 2 u S := holderJetOn_scalarDerivativeJet (k+1) 2
    (by convert hφ using 1 <;> congr 1 <;> omega) (by convert hφj' using 1 <;> omega) w
  obtain ⟨Hu, hHu, _, huH⟩ := huj.fderiv.fderiv.value
  obtain ⟨Hf, hHf, _, hfH⟩ := hfj.fderiv.value
  let DA : KernelSpace n → Matrix (Fin n) (Fin n) (KernelSpace n →L[ℝ] ℝ) :=
    fun x i j => fderiv ℝ (fun z => A z i j) x
  have hDA : BoundedHolderOn α DA S := BoundedHolderOn.pi (fun i => BoundedHolderOn.pi
    (fun j => ((hAj i j).mono_order (show 1 ≤ k+1 by omega)).fderiv.value))
  obtain ⟨HA, hHA, _, hDAH⟩ := hDA
  have hAH : ∀ x ∈ S, ∀ y ∈ S, ∀ i j,
      ‖fderiv ℝ (fun z => A z i j) x-fderiv ℝ (fun z => A z i j) y‖ ≤ HA*‖x-y‖^α := by
    intro x hx y hy i j
    exact (Matrix.norm_entry_le_entrywise_sup_norm (DA x-DA y) (i := i) (j := j)).trans (hDAH x hx y hy)
  have hAc1 : ∀ i j, ContDiff ℝ 1 (fun x => A x i j) := fun i j =>
    (hAc i j).of_le (by exact_mod_cast (show 1 ≤ k+1 by omega))
  have heq : ∀ x ∈ S, euclideanEllipticOperator (A x) u x=f x := by
    intro x hx
    have hh := local_logdet_iterated_equation k hφ hAc1 Metric.isOpen_ball
      (fun y hy => hpos y (hTU hy)) (fun y hy => hMA y (hTU hy)) hAe d v (hST hx)
    have hw : Fin.snoc d v=w := Fin.snoc_init_self w
    rw [hw] at hh
    exact hh
  have hApos : ∀ x ∈ S, (A x).PosDef := by
    intro x hx
    rw [hAe x (hST hx)]
    exact (hpos x (hSU hx)).inv
  obtain ⟨r, C, hr, hrR, hC, hc, hb, hh⟩ := exists_linear_third_order_holder huc hfc hAc1 a
    (by positivity : 0 < R/4) hHu hHf hHA hα hα1 hApos heq hAH huH hfH
  exact ⟨r, C, hr, by linarith, hC, hc, hb, hh⟩

theorem contDiffAt_local_logdet_succ [NeZero n] (k : ℕ)
    {φ : KernelSpace n → ℝ} (hφ : ContDiff ℝ (↑(k+3) : WithTop ℕ∞) φ)
    (a : KernelSpace n) {R α c : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ Metric.ball a (4*R), (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x ∈ Metric.ball a (4*R), Real.log (euclideanHessianMatrix φ x).det=c)
    (hφj : HolderJetOn α (k+3) φ (Metric.closedBall a (2*R))) :
    ContDiffAt ℝ (↑(k+4) : WithTop ℕ∞) φ a := by
  have hs (w : Fin (k+1) → KernelSpace n) : ContDiffAt ℝ 3 (scalarDerivativeJet (k+1) φ w) a := by
    obtain ⟨r, C, hr, _, _, hc, _⟩ := exists_local_logdet_jet_third_order k hφ a hR hα hα1 hpos hMA hφj w
    exact hc.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hh := contDiffAt_multilinear_of_apply (k+1) hs
  have hg := contDiffAt_of_contDiffAt_iteratedFDeriv (k+1) 3
    (hφ.of_le (by exact_mod_cast (show k+1 ≤ k+3 by omega))) hh
  convert hg using 1 <;> congr 1 <;> omega

end GaussianTilt.MomentMapSchauder
