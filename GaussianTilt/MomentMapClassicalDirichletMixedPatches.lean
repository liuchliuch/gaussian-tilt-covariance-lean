import GaussianTilt.MomentMapClassicalDirichletMixedBarrier

/-!
# Actual quadratic boundary patches

The patch function is an explicit Euclidean coordinate polynomial. Its true
Hessian is the identity, and the boundary split supplies the boundary data
for the mixed derivative comparison barrier.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The actual coordinate quadratic, centered at a boundary point. -/
def boundaryPatchQuadratic (z y : CoordinateSpace n) : ℝ :=
  ∑ i, (y i - z i)^2 / 2

lemma boundaryPatchQuadratic_nonneg (z y : CoordinateSpace n) :
    0 ≤ boundaryPatchQuadratic z y :=
  Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (by norm_num))

@[simp] lemma boundaryPatchQuadratic_self (z : CoordinateSpace n) :
    boundaryPatchQuadratic z z = 0 := by simp [boundaryPatchQuadratic]

lemma contDiff_boundaryPatchQuadratic (z : CoordinateSpace n) {k : WithTop ℕ∞} :
    ContDiff ℝ k (boundaryPatchQuadratic z) := by
  unfold boundaryPatchQuadratic
  fun_prop

lemma coordinateDerivative_boundaryPatchQuadratic (z y : CoordinateSpace n) (i : Fin n) :
    coordinateDerivative i (boundaryPatchQuadratic z) y = y i - z i := by
  unfold boundaryPatchQuadratic
  rw [coordinateDerivative_sum _ (fun a => by fun_prop)]
  have hd (a : Fin n) : coordinateDerivative i (fun x : CoordinateSpace n => x a - z a) y =
      if i = a then 1 else 0 := by
    unfold coordinateDerivative
    rw [fderiv_sub_const]
    exact coordinateDerivative_coordinate i a y
  have hh (a : Fin n) : coordinateDerivative i
      (fun x : CoordinateSpace n => (x a - z a)^2 / 2) y =
      (y a - z a) * (if i = a then 1 else 0) := by
    rw [coordinateDerivative_half_sq_at (by fun_prop), hd]
  simp_rw [hh]
  simp

lemma coordinateHessian_boundaryPatchQuadratic (z y : CoordinateSpace n) :
    coordinateHessian (boundaryPatchQuadratic z) y = 1 := by
  ext i j
  change coordinateDerivative j (coordinateDerivative i (boundaryPatchQuadratic z)) y = _
  rw [show coordinateDerivative i (boundaryPatchQuadratic z) =
    (fun x => x i - z i) from funext (fun x => coordinateDerivative_boundaryPatchQuadratic z x i)]
  unfold coordinateDerivative
  rw [fderiv_sub_const]
  simpa only [Matrix.one_apply, eq_comm] using coordinateDerivative_coordinate j i y

lemma fderiv_boundaryPatchQuadratic_self (z e : CoordinateSpace n) :
    fderiv ℝ (boundaryPatchQuadratic z) z e = 0 := by
  rw [fderiv_apply_eq_sum_coordinates]
  simp [coordinateDerivative_boundaryPatchQuadratic]

lemma linearizedMA_boundaryPatchQuadratic (A : Matrix (Fin n) (Fin n) ℝ)
    (z y : CoordinateSpace n) :
    linearizedMA A (boundaryPatchQuadratic z) y = A.trace := by
  simp [linearizedMA, coordinateHessian_boundaryPatchQuadratic]

/-- Lower defining Hessian bounds give exactly the needed trace barrier. -/
lemma linearizedMA_lower_of_hessian_lower {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) {w : CoordinateSpace n → ℝ} {x : CoordinateSpace n} {κ : ℝ}
    (hw : (coordinateHessian w x - κ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) :
    κ * A.trace ≤ linearizedMA A w x := by
  have h := trace_mul_nonneg_of_posSemidef A _ hA hw
  simpa only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul, sub_nonneg, linearizedMA] using h

/-- The real patch boundary lies on either the original boundary or the
artificial quadratic level. This derives the comparison boundary condition. -/
lemma mixed_patch_boundary_bound {S : Set (CoordinateSpace n)} (hS : IsClosed S)
    {T : CoordinateSpace n → ℝ} {z : CoordinateSpace n} {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hb : ∀ y ∈ frontier S, boundaryPatchQuadratic z y ≤ r → T y = 0)
    (hT : ∀ y ∈ S, boundaryPatchQuadratic z y = r → |T y| ≤ C) :
    ∀ y ∈ frontier (S ∩ {x | boundaryPatchQuadratic z x ≤ r}),
      |T y| ≤ (C / r) * boundaryPatchQuadratic z y := by
  intro y hy
  rcases frontier_inter_subset _ _ hy with h | h
  · have hc : IsClosed {x | boundaryPatchQuadratic z x ≤ r} :=
      isClosed_le (contDiff_boundaryPatchQuadratic z (k := 0)).continuous continuous_const
    have hq : y ∈ {x | boundaryPatchQuadratic z x ≤ r} := hc.closure_eq ▸ h.2
    rw [hb y h.1 hq, abs_zero]
    exact mul_nonneg (div_nonneg hC hr.le) (boundaryPatchQuadratic_nonneg _ _)
  · have hq : boundaryPatchQuadratic z y = r :=
      frontier_le_subset_eq (contDiff_boundaryPatchQuadratic z (k := 0)).continuous continuous_const h.2
    rw [hq, div_mul_cancel₀ _ hr.ne']
    exact hT y (hS.closure_eq ▸ h.1) hq

/-- An actual centered quadratic patch gives a boundary normal derivative
estimate, with no inward-path or artificial-boundary premise left over. -/
theorem mixed_boundary_estimate_on_quadratic_patch [NeZero n]
    {w T : CoordinateSpace n → ℝ} (hwc : Continuous w)
    (hS : IsCompact {y | w y ≤ 0}) {z e : CoordinateSpace n}
    (hw0 : w z = 0) (hT0 : T z = 0)
    (hwd : DifferentiableAt ℝ w z) (hTd : DifferentiableAt ℝ T z)
    (hwe : 0 < fderiv ℝ w z e)
    {r C M κ : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hM : 0 ≤ M) (hκ : 0 < κ)
    (hTc : ContinuousOn T ({y | w y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}))
    (hbT : ∀ y ∈ frontier {y | w y ≤ 0}, boundaryPatchQuadratic z y ≤ r → T y = 0)
    (hTbound : ∀ y ∈ {y | w y ≤ 0}, boundaryPatchQuadratic z y = r → |T y| ≤ C)
    (hT2 : ∀ y ∈ interior ({y | w y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}),
      ContDiffAt ℝ 2 T y)
    (hw2 : ∀ y ∈ interior ({y | w y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}),
      ContDiffAt ℝ 2 w y)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ y ∈ interior ({y | w y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}), (A y).PosDef)
    (hLT : ∀ y ∈ interior ({y | w y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}),
      |linearizedMA (A y) T y| ≤ M * (A y).trace)
    (hHw : ∀ y ∈ interior ({y | w y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}),
      (coordinateHessian w y - κ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) :
    |fderiv ℝ T z e| ≤ ((C / r + M) / κ) * fderiv ℝ w z e := by
  let P := {y | w y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}
  have hqc := (contDiff_boundaryPatchQuadratic z (k := 2)).continuous
  have hP : IsCompact P := hS.inter_right (isClosed_le hqc continuous_const)
  have hbound : ∀ y ∈ P, |T y| ≤ (C/r) * boundaryPatchQuadratic z y -
      ((C/r+M)/κ) * w y := by
    apply mixed_derivative_patch_barrier hP hTc
      hwc.continuousOn hqc.continuousOn hT2 hw2
      (fun _ _ => (contDiff_boundaryPatchQuadratic z).contDiffAt) hA hM
      (div_nonneg hC hr.le) hκ hLT
      (fun y hy => linearizedMA_lower_of_hessian_lower (hA y hy).posSemidef (hHw y hy))
      (fun y _ => (linearizedMA_boundaryPatchQuadratic _ _ _).le)
      (mixed_patch_boundary_bound hS.isClosed hr hC hbT hTbound)
    intro y hy
    exact (hP.isClosed.closure_eq ▸ hy.1).1
  apply mixed_derivative_boundary_slope_bound hTd hwd
    ((contDiff_boundaryPatchQuadratic z (k := 2)).differentiable (by norm_num) z)
    hT0 hw0 (boundaryPatchQuadratic_self z) (fderiv_boundaryPatchQuadratic_self z e)
    (eventually_in_defining_patch hwd hqc.continuousAt hw0 hwe (by simpa using hr)) hbound

end GaussianTilt.MomentMapRegularity
