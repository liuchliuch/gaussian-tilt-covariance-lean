import GaussianTilt.MomentMapClassicalDirichletGeometryHessian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # Actual smooth boundary curves and zero-boundary jets

The level set is flattened by a map whose derivative is the identity.
The inverse function theorem then constructs the tangent curves; no
boundary-jet identity or classical PDE solvability is assumed.
-/
noncomputable section
open Set Filter
open scoped Topology ContDiff Gradient
namespace GaussianTilt.MomentMapRegularity
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A prescribed tangent vector is the derivative of an actual local C²
curve in the regular level set. -/
theorem exists_curve_in_regular_level {w : X → ℝ} {x : X}
    (hw : ContDiffAt ℝ 2 w x) {e v : X}
    (he : fderiv ℝ w x e = 1) (hv : fderiv ℝ w x v = 0) :
    ∃ γ : ℝ → X, γ 0 = x ∧ ContDiffAt ℝ 2 γ 0 ∧ HasDerivAt γ v 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), w (γ t) = w x := by
  let ℓ := fderiv ℝ w x
  let F := fun y => y + (w y-w x-ℓ (y-x)) • e
  have hF : ContDiffAt ℝ 2 F x := contDiffAt_id.add
    (((hw.sub contDiffAt_const).sub (ℓ.contDiff.contDiffAt.comp x
      (contDiffAt_id.sub contDiffAt_const))).smul contDiffAt_const)
  have hlin : HasFDerivAt (fun y => ℓ (y-x)) ℓ x := by
    simpa only [ContinuousLinearMap.comp_id] using ℓ.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x)
  have hd := (hasFDerivAt_id x).fun_add
    ((((hw.differentiableAt (by norm_num)).hasFDerivAt.sub_const (w x)).fun_sub hlin).smul_const e)
  have hFd : HasFDerivAt F (ContinuousLinearEquiv.refl ℝ (X) : X →L[ℝ] X) x := by
    have hz : (fderiv ℝ w x-ℓ).smulRight e = 0 := by ext z; simp [ℓ]
    simpa only [hz, add_zero] using hd
  have hFx : F x = x := by simp [F]
  let c := hF.toOpenPartialHomeomorph F hFd (by norm_num)
  have hcx : x ∈ c.source := hF.mem_toOpenPartialHomeomorph_source hFd (by norm_num)
  have hcF : (c : X → X) = F := rfl
  have hct : x ∈ c.target := by
    have hh := c.map_source hcx
    rwa [hcF, hFx] at hh
  have hci : c.symm x = x := by
    have hh := c.left_inv hcx
    rwa [hcF, hFx] at hh
  have hcd : HasFDerivAt c.symm (ContinuousLinearEquiv.refl ℝ (X) : X →L[ℝ] X) x := by
    simpa using c.hasFDerivAt_symm (f' := ContinuousLinearEquiv.refl ℝ (X)) hct (by
      rw [hci, hcF]
      exact hFd)
  have hcs : ContDiffAt ℝ 2 c.symm x := by
    apply c.contDiffAt_symm (f₀' := ContinuousLinearEquiv.refl ℝ (X)) hct
    · rw [hci,hcF]
      exact hFd
    · rw [hci,hcF]
      exact hF
  let γ := fun t : ℝ => c.symm (x+t • v)
  have hl : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) x).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hγd : HasDerivAt γ v 0 := by
    have hcd' : HasFDerivAt c.symm (ContinuousLinearEquiv.refl ℝ (X) : X →L[ℝ] X)
        (x+(0 : ℝ) • v) := by simpa using hcd
    exact hcd'.comp_hasDerivAt 0 hl
  have hγs : ContDiffAt ℝ 2 γ 0 := by
    have hcs' : ContDiffAt ℝ 2 c.symm (x+(0 : ℝ) • v) := by simpa using hcs
    exact hcs'.comp 0 (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hlevel (y : X) : ℓ (F y-x) = w y-w x := by
    dsimp [F]
    rw [show y+(w y-w x-ℓ (y-x)) • e-x = (y-x)+(w y-w x-ℓ (y-x)) • e by abel,
      map_add, map_smul]
    change ℓ (y-x)+(w y-w x-ℓ (y-x))*ℓ e = w y-w x
    rw [he]
    ring
  refine ⟨γ, by simpa [γ] using hci, hγs, hγd, ?_⟩
  have ht : ∀ᶠ t in 𝓝 (0 : ℝ), x+t • v ∈ c.target :=
    hl.continuousAt (c.open_target.mem_nhds (by simpa using hct))
  filter_upwards [ht] with t ht
  have hh := c.right_inv ht
  change F (γ t) = x+t • v at hh
  have hi := hlevel (γ t)
  rw [hh, add_sub_cancel_left, map_smul, hv, smul_zero] at hi
  linarith

end GaussianTilt.MomentMapRegularity
