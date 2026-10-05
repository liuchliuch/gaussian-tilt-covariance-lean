import GaussianTilt.MomentMapSchauderLocalPatch

/-! # Smooth cutoff coefficient extensions from local inverse Hessians -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000
open Set Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder

lemma holderJetOn_of_contDiff_one_more {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {k : ℕ} {f : E → F} (hf : ContDiff ℝ (↑(k+1) : WithTop ℕ∞) f)
    {S : Set E} (hS : IsCompact S) (hSc : Convex ℝ S) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    HolderJetOn α k f S := by
  intro j hj
  apply boundedHolderOn_of_contDiff _ hS hSc hα hα1
  apply hf.iteratedFDeriv_right
  exact_mod_cast (show 1+j ≤ k+1 by omega)

theorem holderJetOn_comp_smoothOn {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α : ℝ} {k : ℕ} {f : E → F} {g : F → G}
    (hf : ContDiff ℝ (k : WithTop ℕ∞) f) (hf₁ : ContDiff ℝ 1 f)
    {U S : Set E} (hU : IsOpen U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ (↑(k+1) : WithTop ℕ∞) g (f x))
    (hS : IsCompact S) (hSc : Convex ℝ S) (hsub : S ⊆ U)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hjets : HolderJetOn α k f S) :
    HolderJetOn α k (g ∘ f) S := by
  intro j hj
  apply boundedHolderOn_iteratedFDeriv_comp
    (fun x _ => hf.contDiffAt.of_le (by exact_mod_cast hj))
    (fun x hx => (hg x (hsub hx)).of_le (by exact_mod_cast (show j ≤ k+1 by omega)))
    (hjets.mono_order hj)
  intro m hm
  have hc : ContDiffOn ℝ 1 (fun x => iteratedFDeriv ℝ m g (f x)) U := by
    intro x hx
    exact (((hg x hx).iteratedFDeriv_right (by exact_mod_cast (show 1+m ≤ k+1 by omega))).comp x
      hf₁.contDiffAt).contDiffWithinAt
  obtain ⟨C, hC, hb, hh⟩ := exists_contDiffOn_holder_bound_on_compact_convex hU hc hS hSc hsub hα hα1
  exact ⟨C, hC.le, hb, hh⟩

open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

theorem local_source_inverse_holderJetOn {m : ℕ} (hm : 1 ≤ m) {φ : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ (↑(m+2) : WithTop ℕ∞) φ)
    {U S : Set (KernelSpace n)} (hU : IsOpen U) (hφj : HolderJetOn α (m+2) φ S)
    (hpos : ∀ x ∈ U, (euclideanHessianMatrix φ x).PosDef)
    (hS : IsCompact S) (hSc : Convex ℝ S) (hsub : S ⊆ U)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
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
  exact holderJetOn_comp_smoothOn hH (hH.of_le (by exact_mod_cast hm)) hU
    (fun x hx => contDiffAt_matrix_inverse_entry (k := (↑(m+1) : WithTop ℕ∞)) (hpos x hx).det_pos.ne' i j)
    hS hSc hsub hα hα1 hHJ

/-- An explicit globally Cᵐ matrix field agrees with the true inverse
Hessian on the cutoff plateau. Positivity is used only on the local domain. -/
theorem contDiff_cutoff_inverse_coefficients {m : ℕ} {φ χ : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ (↑(m+2) : WithTop ℕ∞) φ) (hχ : ContDiff ℝ (m : WithTop ℕ∞) χ)
    {U : Set (KernelSpace n)} (hU : IsOpen U) (hs : tsupport χ ⊆ U)
    (hpos : ∀ x ∈ U, (euclideanHessianMatrix φ x).PosDef) :
    ∀ i j, ContDiff ℝ (m : WithTop ℕ∞)
      (fun x => cutoffCoefficient 1 (fun y => (euclideanHessianMatrix φ y)⁻¹) χ x i j) := by
  have hH : ContDiff ℝ (m : WithTop ℕ∞) (euclideanHessianMatrix φ) :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (contDiff_euclideanHessianMatrix_entry hφ i))
  intro i j
  have hc : ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => (euclideanHessianMatrix φ x)⁻¹ i j-(1 : Matrix (Fin n) (Fin n) ℝ) i j) U := by
    intro x hx
    exact (((contDiffAt_matrix_inverse_entry (k := (m : WithTop ℕ∞)) (hpos x hx).det_pos.ne' i j).comp x
      hH.contDiffAt).sub contDiffAt_const).contDiffWithinAt
  have hp := contDiff_cutoff_mul_of_contDiffOn hU hc hχ hs
  exact contDiff_const.add hp

end GaussianTilt.MomentMapSchauder
