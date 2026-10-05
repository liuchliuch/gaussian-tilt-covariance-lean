import GaussianTilt.MomentMapSchauderForcingHolderJets
import GaussianTilt.MomentMapSchauderInverseHolder

/-! # Actual nonlinear source coefficients and forcing have Hölder jets -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2200000
open Set Matrix InnerProductSpace
open scoped ContDiff Gradient Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ} {α : ℝ} {S : Set (KernelSpace n)}

lemma contDiffAt_matrix_inverse_entry {k : WithTop ℕ∞} {A : Matrix (Fin n) (Fin n) ℝ}
    (hdet : A.det ≠ 0) (i j : Fin n) :
    ContDiffAt ℝ k (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹ i j) A := by
  have he (a b : Fin n) : ContDiff ℝ k (fun M : Matrix (Fin n) (Fin n) ℝ => M a b) := by fun_prop
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((contDiff_matrix_det_field he).contDiffAt.inv hdet).mul
    (contDiff_matrix_adjugate_field he i j).contDiffAt

/-- All finite inverse-Hessian Hölder jets are derived from the actual
source jets and matrix inverse formula. -/
theorem source_inverse_holderJetOn {m : ℕ} (hm : 1 ≤ m) {φ : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ (↑(m+2) : WithTop ℕ∞) φ) (hφj : HolderJetOn α (m+2) φ S)
    (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (hS : IsCompact S) (hSc : Convex ℝ S) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∀ i j, HolderJetOn α m (fun x => (euclideanHessianMatrix φ x)⁻¹ i j) S := by
  have hHc (i j : Fin n) : ContDiff ℝ (m : WithTop ℕ∞) (fun x => euclideanHessianMatrix φ x i j) :=
    contDiff_euclideanHessianMatrix_entry hφ i j
  have hHj (i j : Fin n) : HolderJetOn α m (fun x => euclideanHessianMatrix φ x i j) S :=
    holderJetOn_secondFrechet_entry hφ hφj _ _
  have hH : ContDiff ℝ (m : WithTop ℕ∞) (euclideanHessianMatrix φ) :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (hHc i))
  have hHJ : HolderJetOn α m (euclideanHessianMatrix φ) S :=
    HolderJetOn.pi (fun i => contDiff_pi.mpr (hHc i)) (fun i => HolderJetOn.pi (hHc i) (hHj i))
  intro i j
  exact holderJetOn_comp_smooth hH (hH.of_le (by exact_mod_cast hm))
    (fun x => contDiffAt_matrix_inverse_entry (k := (↑(m+1) : WithTop ℕ∞)) (hpos x).det_pos.ne' i j)
    hS hSc hα hα1 hHJ

/-- The actual source nonlinearity has all finite Hölder jets available
from the source. Smoothness of the target is only used on its open domain. -/
theorem sourceRHS_holderJetOn {m : ℕ} (hm : 1 ≤ m) {φ V : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ (↑(m+1) : WithTop ℕ∞) φ) (hφj : HolderJetOn α (m+1) φ S)
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hV : ContDiffOn ℝ (↑(m+1) : WithTop ℕ∞) V Ω)
    (hmap : ∀ x, gradient φ x ∈ Ω)
    (hS : IsCompact S) (hSc : Convex ℝ S) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ContDiff ℝ (m : WithTop ℕ∞) (sourceRHS φ V) ∧ HolderJetOn α m (sourceRHS φ V) S := by
  have hDφ : ContDiff ℝ (m : WithTop ℕ∞) (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  let L := (toDual ℝ (KernelSpace n)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hGc : ContDiff ℝ (m : WithTop ℕ∞) (gradient φ) := L.contDiff.comp hDφ
  have hGj : HolderJetOn α m (gradient φ) S := hφj.fderiv.linear_map hDφ L
  have hVc : ContDiff ℝ (m : WithTop ℕ∞) (V ∘ gradient φ) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact ((hV.contDiffAt (hΩ.mem_nhds (hmap x))).of_le (by exact_mod_cast (Nat.le_succ m))).comp x hGc.contDiffAt
  have hVj := holderJetOn_comp_smooth hGc (hGc.of_le (by exact_mod_cast hm))
    (fun x => hV.contDiffAt (hΩ.mem_nhds (hmap x))) hS hSc hα hα1 hGj
  have hφc : ContDiff ℝ (m : WithTop ℕ∞) φ := hφ.of_le (by exact_mod_cast (Nat.le_succ m))
  have hφj' := hφj.mono_order (Nat.le_succ m)
  exact ⟨hφc.neg.add hVc, HolderJetOn.add hφc.neg hVc (hφj'.neg hφc) hVj⟩

/-- The exact iterated source forcing has a true C¹,α bound, derived from
only the inductively available highest source jet and the smooth target. -/
theorem source_iterated_forcing_holderJetOn_one (k : ℕ) {φ V : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ (↑(k+3) : WithTop ℕ∞) φ) (hφj : HolderJetOn α (k+3) φ S)
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hV : ContDiffOn ℝ (↑(k+3) : WithTop ℕ∞) V Ω)
    (hmap : ∀ x, gradient φ x ∈ Ω) (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (hS : IsCompact S) (hSc : Convex ℝ S) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (d : Fin k → KernelSpace n) (v : KernelSpace n) :
    ContDiff ℝ 1 (iteratedEllipticForcing (fun y => (euclideanHessianMatrix φ y)⁻¹)
      (kernelDirectionalDerivative v φ) (kernelDirectionalDerivative v (sourceRHS φ V)) k d) ∧
    HolderJetOn α 1 (iteratedEllipticForcing (fun y => (euclideanHessianMatrix φ y)⁻¹)
      (kernelDirectionalDerivative v φ) (kernelDirectionalDerivative v (sourceRHS φ V)) k d) S := by
  have hHc (i j : Fin n) : ContDiff ℝ (↑(k+1) : WithTop ℕ∞) (fun x => euclideanHessianMatrix φ x i j) := by
    apply contDiff_euclideanHessianMatrix_entry
    convert hφ using 1 <;> congr 1 <;> omega
  have hAc := contDiff_matrix_inv_field hHc (fun x => (hpos x).det_pos.ne')
  have hAj := source_inverse_holderJetOn (m := k+1) (by omega)
    (by convert hφ using 1 <;> congr 1 <;> omega) (by convert hφj using 1 <;> omega)
    hpos hS hSc hα hα1
  have hg := sourceRHS_holderJetOn (m := k+2) (by omega)
    (by convert hφ using 1 <;> congr 1 <;> omega) (by convert hφj using 1 <;> omega)
    hΩ (by convert hV using 1 <;> congr 1 <;> omega) hmap hS hSc hα hα1
  have huc : ContDiff ℝ (↑(k+2) : WithTop ℕ∞) (kernelDirectionalDerivative v φ) :=
    contDiff_kernelDirectionalDerivative (by simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc] using hφ) v
  have huj : HolderJetOn α (k+2) (kernelDirectionalDerivative v φ) S :=
    HolderJetOn.directional (by convert hφ using 1 <;> congr 1 <;> omega)
      (by convert hφj using 1 <;> omega) v
  have hfc : ContDiff ℝ (↑(k+1) : WithTop ℕ∞) (kernelDirectionalDerivative v (sourceRHS φ V)) :=
    contDiff_kernelDirectionalDerivative (by simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc] using hg.1) v
  have hfj : HolderJetOn α (k+1) (kernelDirectionalDerivative v (sourceRHS φ V)) S :=
    HolderJetOn.directional (by convert hg.1 using 1 <;> congr 1 <;> omega)
      (by convert hg.2 using 1 <;> omega) v
  exact ⟨source_iterated_forcing_contDiff_one k hφ hg.1 hpos d v,
    holderJetOn_iteratedEllipticForcing k 1 (by convert huc using 1 <;> congr 1 <;> omega)
      (by convert huj using 1 <;> omega) hAc hAj hfc hfj hS hSc hα hα1 d⟩

end GaussianTilt.MomentMapSchauder
