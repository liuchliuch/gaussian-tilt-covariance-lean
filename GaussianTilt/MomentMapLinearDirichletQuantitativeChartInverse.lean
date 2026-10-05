import GaussianTilt.MomentMapLinearDirichletQuantitativeChartGeometry

/-! # Actual derivative inverse identities on the constructed chart -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

theorem regularLevel_chart_derivative_inverse {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    {z : KernelSpace n} (hz : z ∈ (regularLevelFlatteningChart hw a j hj).target)
    (hg : DifferentiableAt ℝ (regularLevelFlatteningChart hw a j hj).symm z) :
    (fderiv ℝ (flatteningMap w a j) ((regularLevelFlatteningChart hw a j hj).symm z)).comp
      (fderiv ℝ (regularLevelFlatteningChart hw a j hj).symm z)=ContinuousLinearMap.id ℝ (KernelSpace n) ∧
    (fderiv ℝ (regularLevelFlatteningChart hw a j hj).symm z).comp
      (fderiv ℝ (flatteningMap w a j) ((regularLevelFlatteningChart hw a j hj).symm z))=
        ContinuousLinearMap.id ℝ (KernelSpace n) := by
  let Ψ := regularLevelFlatteningChart hw a j hj
  let g := Ψ.symm
  have hΦ := (contDiff_flatteningMap hw a j).differentiable (by simp)
  have hr : (fun y => flatteningMap w a j (g y)) =ᶠ[𝓝 z] (fun y => y) := by
    filter_upwards [Ψ.open_target.mem_nhds hz] with y hy
    exact Ψ.right_inv hy
  have hdr := (hr.fderiv (𝕜 := ℝ)).self_of_nhds
  change fderiv ℝ ((flatteningMap w a j) ∘ g) z=fderiv ℝ id z at hdr
  rw [fderiv_comp z (hΦ (g z)) hg,fderiv_id] at hdr
  refine ⟨hdr,?_⟩
  have hgz : g z ∈ Ψ.source := Ψ.map_target hz
  have hl : (fun y => g (flatteningMap w a j y)) =ᶠ[𝓝 (g z)] (fun y => y) := by
    filter_upwards [Ψ.open_source.mem_nhds hgz] with y hy
    exact Ψ.left_inv hy
  have hback : flatteningMap w a j (g z)=z := Ψ.right_inv hz
  have hgd : DifferentiableAt ℝ g (flatteningMap w a j (g z)) := by rw [hback]; exact hg
  have hdl := (hl.fderiv (𝕜 := ℝ)).self_of_nhds
  change fderiv ℝ (g ∘ flatteningMap w a j) (g z)=fderiv ℝ id (g z) at hdl
  rw [fderiv_comp (g z) hgd (hΦ (g z)),fderiv_id,hback] at hdl
  exact hdl

/-- The bounded actual inverse derivative gives the genuine lower metric
bound on the forward derivative, with no singular-value hypothesis. -/
lemma norm_le_inverse_bound_mul_norm_forward
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (J : X →L[ℝ] Y) (G : Y →L[ℝ] X) (hGJ : G.comp J=ContinuousLinearMap.id ℝ X)
    {C : ℝ} (hG : ‖G‖ ≤ C) (v : X) : ‖v‖ ≤ C*‖J v‖ := by
  have he := congrArg (fun T : X →L[ℝ] X => T v) hGJ
  change G (J v)=v at he
  calc
    ‖v‖ = ‖G (J v)‖ := congrArg norm he.symm
    _ ≤ ‖G‖*‖J v‖ := G.le_opNorm _
    _ ≤ C*‖J v‖ := mul_le_mul_of_nonneg_right hG (norm_nonneg _)

end GaussianTilt.MomentMapLinearDirichlet
