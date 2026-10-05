import GaussianTilt.MomentMapClassicalDirichletContinuationFirstOrder

/-! # Actual parameter-uniform second spatial derivatives of the log forcing -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateDerivative_dirichletContinuationDensity {w : CoordinateSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (t : ℝ) (x : CoordinateSpace n) (i : Fin n) :
    coordinateDerivative i (dirichletContinuationDensity w t) x =
      (1-t)*coordinateDerivative i (fun y => (coordinateHessian w y).det) x := by
  have hg := contDiff_matrix_det (smooth_coordinateHessian hw)
  unfold dirichletContinuationDensity
  rw [coordinateDerivative_add_at ((hg.differentiable (by simp) x).const_mul (1-t)) (differentiableAt_const t),
    coordinateDerivative_const_mul_at (hg.differentiable (by simp) x)]
  simp [coordinateDerivative]

lemma coordinateHessian_dirichletContinuationDensity {w : CoordinateSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (t : ℝ) (x : CoordinateSpace n) (i j : Fin n) :
    coordinateHessian (dirichletContinuationDensity w t) x i j =
      (1-t)*coordinateHessian (fun y => (coordinateHessian w y).det) x i j := by
  have hg := contDiff_matrix_det (smooth_coordinateHessian hw)
  change coordinateDerivative j (coordinateDerivative i (dirichletContinuationDensity w t)) x = _
  rw [show coordinateDerivative i (dirichletContinuationDensity w t) =
    (fun y => (1-t)*coordinateDerivative i (fun y => (coordinateHessian w y).det) y) from
      funext (fun y => coordinateDerivative_dirichletContinuationDensity hw t y i)]
  exact coordinateDerivative_const_mul_at
    ((smooth_coordinateDerivative hg i).differentiable (by simp) x) (1-t) j

/-- Every actual log-forcing Hessian entry is uniformly bounded on the
compact body for all homotopy parameters. -/
theorem dirichletContinuationDensity_uniform_log_hessian
    {S : Set (CoordinateSpace n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {w : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (hH : ∀ x ∈ S, (coordinateHessian w x).PosDef) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ S, ∀ i j,
      |coordinateHessian (fun y => Real.log (dirichletContinuationDensity w t y)) x i j| ≤ K := by
  obtain ⟨c,C,hc,hC,hbounds⟩ := dirichletContinuationDensity_uniform_bounds hS hSn hw hH
  let g := fun y => (coordinateHessian w y).det
  have hg : ContDiff ℝ ∞ g := contDiff_matrix_det (smooth_coordinateHessian hw)
  have hc1 : Continuous (coordinateGradient g) := continuous_pi (fun i => (smooth_coordinateDerivative hg i).continuous)
  have hc2 : Continuous (fun x => fun i j : Fin n => coordinateHessian g x i j) := continuous_pi (fun i =>
    continuous_pi (fun j => (smooth_coordinateHessian hg i j).continuous))
  obtain ⟨J₀,hJ₀⟩ := hS.exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨L₀,hL₀⟩ := hS.exists_bound_of_continuousOn hc2.continuousOn
  let J := max J₀ 0
  let L := max L₀ 0
  have hJ : 0 ≤ J := le_max_right _ _
  have hL : 0 ≤ L := le_max_right _ _
  have hgb1 (x : CoordinateSpace n) (hx : x ∈ S) (i : Fin n) : |coordinateDerivative i g x| ≤ J :=
    (norm_le_pi_norm (coordinateGradient g x) i).trans ((hJ₀ x hx).trans (le_max_left _ _))
  have hgb2 (x : CoordinateSpace n) (hx : x ∈ S) (i j : Fin n) : |coordinateHessian g x i j| ≤ L :=
    ((norm_le_pi_norm (coordinateHessian g x i) j).trans (norm_le_pi_norm (fun i j : Fin n => coordinateHessian g x i j) i)).trans
      ((hL₀ x hx).trans (le_max_left _ _))
  refine ⟨L/c+J^2/c^2, add_nonneg (div_nonneg hL hc.le) (div_nonneg (sq_nonneg _) (sq_nonneg _)), ?_⟩
  intro t ht x hx i j
  have ht01 : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  have ht1 : 1-t ≤ 1 := by linarith [ht.1]
  have hfpos := dirichletContinuationDensity_pos ht (hH x hx)
  have hf2 : ContDiffAt ℝ 2 (dirichletContinuationDensity w t) x :=
    (contDiffAt_const.mul (contDiff_infty.mp hg 2).contDiffAt).add contDiffAt_const
  have hb1 (a : Fin n) : |coordinateDerivative a (dirichletContinuationDensity w t) x| ≤ J := by
    rw [coordinateDerivative_dirichletContinuationDensity hw,abs_mul,abs_of_nonneg ht01]
    exact (mul_le_mul ht1 (hgb1 x hx a) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hb2 : |coordinateHessian (dirichletContinuationDensity w t) x i j| ≤ L := by
    rw [coordinateHessian_dirichletContinuationDensity hw,abs_mul,abs_of_nonneg ht01]
    exact (mul_le_mul ht1 (hgb2 x hx i j) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [coordinateHessian_log_at hf2 hfpos.ne']
  apply (abs_sub _ _).trans
  apply add_le_add
  · rw [abs_div,abs_of_pos hfpos]
    exact (div_le_div_of_nonneg_right hb2 hfpos.le).trans
      (div_le_div_of_nonneg_left hL hc (hbounds t ht x hx).1)
  · rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg (dirichletContinuationDensity w t x))]
    have hprod : |coordinateDerivative i (dirichletContinuationDensity w t) x| *
        |coordinateDerivative j (dirichletContinuationDensity w t) x| ≤ J^2 := by
      simpa only [pow_two] using mul_le_mul (hb1 i) (hb1 j) (abs_nonneg _) hJ
    have hc2 : c^2 ≤ (dirichletContinuationDensity w t x)^2 :=
      (sq_le_sq₀ hc.le hfpos.le).mpr (hbounds t ht x hx).1
    exact (div_le_div_of_nonneg_right hprod (sq_nonneg _)).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hc) hc2)

end GaussianTilt.MomentMapRegularity
