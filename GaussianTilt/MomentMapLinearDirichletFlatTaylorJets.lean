import GaussianTilt.MomentMapLinearDirichletHarmonicTaylorLocal
import GaussianTilt.MomentMapLinearDirichletFlatteningChainRule

/-! # Genuine zero-plane constraints on the reflected harmonic Taylor jet -/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Restriction to actual straight lines in the boundary plane proves
both tangential Taylor coefficients vanish. -/
lemma flat_zero_plane_taylor_jets (j : Fin n) {h : KernelSpace n → ℝ}
    (hh : ContDiffAt ℝ 2 h 0) (hzero : ∀ x, x j = 0 → h x = 0)
    (z : KernelSpace n) (hz : z j = 0) :
    fderiv ℝ h 0 z = 0 ∧ fderiv ℝ (fderiv ℝ h) 0 z z = 0 := by
  let P : ℝ →L[ℝ] KernelSpace n := (ContinuousLinearMap.id ℝ ℝ).smulRight z
  have hP (t : ℝ) : P t = t • z := rfl
  have he : h ∘ P = (fun _ : ℝ => 0) := by
    funext t
    apply hzero
    simp [hP, hz]
  have hhat : ContDiffAt ℝ 2 h (P 0) := by simpa using hh
  have hfirst := ((hhat.differentiableAt (by norm_num)).hasFDerivAt.comp 0 P.hasFDerivAt).fderiv
  have hfirst1 := congrArg (fun A : ℝ →L[ℝ] ℝ => A 1) hfirst
  rw [he] at hfirst1
  have hlin : fderiv ℝ P = fun _ => P := funext (fun _ => P.fderiv)
  have hsecond := secondFrechet_comp_at hhat P.contDiff.contDiffAt (1 : ℝ) 1
  rw [he, hlin] at hsecond
  constructor
  · simpa [P] using hfirst1.symm
  · simpa [P] using hsecond.symm

lemma directionalHessian_eq_secondFrechet_at {h : KernelSpace n → ℝ} {x : KernelSpace n}
    (hh : ContDiffAt ℝ 2 h x) (v w : KernelSpace n) :
    directionalHessian h x v w = fderiv ℝ (fderiv ℝ h) x w v := by
  have hd := (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  unfold directionalHessian
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

lemma kernelLaplacian_eq_trace_at {h : KernelSpace n → ℝ} {x : KernelSpace n}
    (hh : ContDiffAt ℝ 2 h x) :
    kernelLaplacian h x = ∑ i : Fin n,
      fderiv ℝ (fderiv ℝ h) x (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  simp only [kernelLaplacian, directionalHessian_eq_secondFrechet_at hh]

/-- The literal reflected Taylor polynomial vanishes on the whole plane. -/
lemma flat_harmonic_taylor_zero_on_plane (j : Fin n) {h : KernelSpace n → ℝ}
    (hh : ContDiffAt ℝ 2 h 0) (hzero : ∀ x, x j = 0 → h x = 0)
    (z : KernelSpace n) (hz : z j = 0) :
    fderiv ℝ h 0 z + (1/2 : ℝ) * fderiv ℝ (fderiv ℝ h) 0 z z = 0 := by
  obtain ⟨h1, h2⟩ := flat_zero_plane_taylor_jets j hh hzero z hz
  rw [h1, h2, mul_zero, add_zero]

def flatTaylorPolynomial (A : KernelSpace n →L[ℝ] ℝ)
    (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) (x : KernelSpace n) : ℝ :=
  A x + (1/2 : ℝ) * B x x

lemma contDiff_flatTaylorPolynomial (A : KernelSpace n →L[ℝ] ℝ)
    (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) : ContDiff ℝ ∞ (flatTaylorPolynomial A B) :=
  A.contDiff.add (contDiff_const.mul (B.contDiff.clm_apply contDiff_id))

lemma fderiv_flatTaylorPolynomial (A : KernelSpace n →L[ℝ] ℝ)
    (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) (x v : KernelSpace n) :
    fderiv ℝ (flatTaylorPolynomial A B) x v = A v + (1/2 : ℝ) * (B v x + B x v) := by
  have h := A.hasFDerivAt.add ((B.hasFDerivAt.clm_apply (hasFDerivAt_id x)).const_mul (1/2 : ℝ))
  change HasFDerivAt (flatTaylorPolynomial A B) _ x at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, ContinuousLinearMap.flip_apply, id_eq]
  ring

lemma directionalHessian_flatTaylorPolynomial (A : KernelSpace n →L[ℝ] ℝ)
    (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) (x v w : KernelSpace n) :
    directionalHessian (flatTaylorPolynomial A B) x v w = (1/2 : ℝ) * (B v w + B w v) := by
  have he : (fun y => fderiv ℝ (flatTaylorPolynomial A B) y v) =
      fun y => A v + (1/2 : ℝ) * (B v y + B y v) := funext (fun y => fderiv_flatTaylorPolynomial A B y v)
  have h := (((B v).hasFDerivAt.add (B.hasFDerivAt.clm_apply (hasFDerivAt_const v x))).const_mul
    (1/2 : ℝ)).const_add (A v)
  change HasFDerivAt (fun y => A v + (1/2 : ℝ) * (B v y + B y v)) _ x at h
  unfold directionalHessian
  rw [he, h.fderiv]
  simp
  ring

lemma kernelLaplacian_flatTaylorPolynomial (A : KernelSpace n →L[ℝ] ℝ)
    (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) (x : KernelSpace n) :
    kernelLaplacian (flatTaylorPolynomial A B) x =
      ∑ i : Fin n, B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  unfold kernelLaplacian
  apply Finset.sum_congr rfl
  intro i _
  rw [directionalHessian_flatTaylorPolynomial]
  ring

lemma flatTaylorPolynomial_harmonic {h : KernelSpace n → ℝ}
    (hh : ContDiffAt ℝ 2 h 0) (hhar : kernelLaplacian h 0 = 0) (x : KernelSpace n) :
    kernelLaplacian (flatTaylorPolynomial (fderiv ℝ h 0) (fderiv ℝ (fderiv ℝ h) 0)) x = 0 := by
  rw [kernelLaplacian_flatTaylorPolynomial, ← kernelLaplacian_eq_trace_at hh, hhar]

end GaussianTilt.MomentMapLinearDirichlet
