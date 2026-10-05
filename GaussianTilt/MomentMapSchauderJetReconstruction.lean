import GaussianTilt.MomentMapSchauderSourceJetGain
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! # Reconstruction of actual source regularity from scalar derivative jets -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2000000
open Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
universe u

/-- Finite-dimensional multilinear-map-valued fields are genuinely smooth
when all fixed evaluations are smooth. This is derived by currying and the
actual finite-dimensional linear-map theorem. -/
theorem contDiff_multilinear_of_apply {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (k : ℕ) {m : WithTop ℕ∞} {f : G → ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F}
    (hf : ∀ v : Fin k → E, ContDiff ℝ m (fun x => f x v)) : ContDiff ℝ m f := by
  induction k with
  | zero =>
    let L := continuousMultilinearCurryFin0 ℝ E F
    have hh : ContDiff ℝ m (fun x => L (f x)) := by
      convert hf (fun _ => (0 : E)) using 1
    convert L.symm.contDiff.comp hh using 1
    funext x
    exact (L.symm_apply_apply (f x)).symm
  | succ k ih =>
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) F
    have hh : ContDiff ℝ m (fun x => L (f x)) := by
      apply contDiff_clm_apply_iff.mpr
      intro e
      apply ih
      intro v
      exact hf (Fin.cons e v)
    convert L.symm.contDiff.comp hh using 1
    funext x
    exact (L.symm_apply_apply (f x)).symm

/-- Smoothness of an actual iterated derivative upgrades the original
function by that many orders; no chosen jet integrability is assumed. -/
theorem contDiff_of_contDiff_iteratedFDeriv {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k m : ℕ) {f : E → F} (hf : ContDiff ℝ (k : WithTop ℕ∞) f)
    (htop : ContDiff ℝ (m : WithTop ℕ∞) (iteratedFDeriv ℝ k f)) :
    ContDiff ℝ (↑(k+m) : WithTop ℕ∞) f := by
  induction k generalizing F with
  | zero =>
    let L := continuousMultilinearCurryFin0 ℝ E F
    have hh := L.contDiff.comp htop
    convert hh using 1
    · simp
  | succ k ih =>
    have hDf : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
    let L := continuousMultilinearCurryRightEquiv' ℝ k E F
    have hDtop : ContDiff ℝ (m : WithTop ℕ∞) (iteratedFDeriv ℝ k (fderiv ℝ f)) := by
      have hh := L.contDiff.comp htop
      convert hh using 1
      funext x
      dsimp only [Function.comp_apply]
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
      exact (L.apply_symm_apply _).symm
    have hD := ih hDf hDtop
    have hd : Differentiable ℝ f := hf.differentiable (by exact_mod_cast (show 1 ≤ k+1 by omega))
    have hh : ContDiff ℝ ((↑(k+m) : WithTop ℕ∞)+1) f := by
      rw [contDiff_succ_iff_fderiv]
      exact ⟨hd, by simp, hD⟩
    have he : (↑(k+1+m) : WithTop ℕ∞) = (↑(k+m) : WithTop ℕ∞)+1 := by
      calc
        (↑(k+1+m) : WithTop ℕ∞) = ↑((k+m)+1) := by congr 1; omega
        _ = (↑(k+m) : WithTop ℕ∞)+1 := by simp
    rw [he]
    exact hh

open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- The higher source PDE and scalar Schauder gain imply genuine global
C^{k+4} regularity. No higher derivative of the original source is assumed. -/
theorem moment_source_contDiff_succ [NeZero n] (k : ℕ)
    {φ V : KernelSpace n → ℝ} (hφ : ContDiff ℝ (↑(k+3) : WithTop ℕ∞) φ)
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hV : ContDiffOn ℝ (↑(k+3) : WithTop ℕ∞) V Ω)
    (hmap : ∀ x, gradient φ x ∈ Ω) (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (euclideanHessianMatrix φ x).det= -φ x+V (gradient φ x))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hloc : ∀ a : KernelSpace n, ∃ R : ℝ, 0 < R ∧ HolderJetOn α (k+3) φ (Metric.closedBall a (2*R))) :
    ContDiff ℝ (↑(k+4) : WithTop ℕ∞) φ := by
  have hscalar (w : Fin (k+1) → KernelSpace n) : ContDiff ℝ 3 (scalarDerivativeJet (k+1) φ w) := by
    apply contDiff_iff_contDiffAt.mpr
    intro a
    obtain ⟨R, hR, hj⟩ := hloc a
    obtain ⟨r, C, hr, _, _, hc, _⟩ := exists_source_jet_third_order_holder k hφ hΩ hV hmap hpos hMA
      a hR hα hα1 hj w
    exact hc.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hfield : ContDiff ℝ 3 (iteratedFDeriv ℝ (k+1) φ) := contDiff_multilinear_of_apply (k+1) hscalar
  have hh := contDiff_of_contDiff_iteratedFDeriv (k+1) 3
    (hφ.of_le (by exact_mod_cast (show k+1 ≤ k+3 by omega))) hfield
  convert hh using 1 <;> congr 1 <;> omega

end GaussianTilt.MomentMapSchauder
