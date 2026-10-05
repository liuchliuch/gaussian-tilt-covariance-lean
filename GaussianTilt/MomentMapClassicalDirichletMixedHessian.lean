import GaussianTilt.MomentMapClassicalDirichletMixedPatches

/-! # From the actual tangential field derivative to mixed Hessian entries -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- An actual normalized transverse vector at a regular coordinate chart. -/
def coordinateTransverse (w : CoordinateSpace n → ℝ) (z : CoordinateSpace n) (j : Fin n) :
    CoordinateSpace n := (coordinateDerivative j w z)⁻¹ • (Pi.single j 1 : CoordinateSpace n)

lemma fderiv_coordinateTransverse_self {w : CoordinateSpace n → ℝ}
    {z : CoordinateSpace n} {j : Fin n} (hj : coordinateDerivative j w z ≠ 0) :
    fderiv ℝ w z (coordinateTransverse w z j) = 1 := by
  simp only [coordinateTransverse, map_smul, smul_eq_mul]
  exact inv_mul_cancel₀ hj

lemma coordinateDerivative_bound_of_transverse_bound {w T : CoordinateSpace n → ℝ}
    {z : CoordinateSpace n} {j : Fin n} (hj : coordinateDerivative j w z ≠ 0)
    {B : ℝ} (h : |fderiv ℝ T z (coordinateTransverse w z j)| ≤ B) :
    |coordinateDerivative j T z| ≤ B * |coordinateDerivative j w z| := by
  have hd : |coordinateDerivative j T z| =
      |fderiv ℝ T z (coordinateTransverse w z j)| * |coordinateDerivative j w z| := by
    simp only [coordinateTransverse, map_smul, smul_eq_mul, abs_mul, abs_inv]
    change _ = |coordinateDerivative j w z|⁻¹ * |coordinateDerivative j T z| *
      |coordinateDerivative j w z|
    field_simp
  rw [hd]
  exact mul_le_mul_of_nonneg_right h (abs_nonneg _)

lemma coordinateDerivative_tangential_field {u β : CoordinateSpace n → ℝ}
    {z : CoordinateSpace n} (hu : ContDiffAt ℝ 2 u z) (hβ : DifferentiableAt ℝ β z)
    (a j : Fin n) :
    coordinateDerivative j (fun y => coordinateDerivative a u y - β y * coordinateDerivative j u y) z =
      coordinateHessian u z a j - β z * coordinateHessian u z j j -
        coordinateDerivative j β z * coordinateDerivative j u z := by
  have hua := (contDiffAt_coordinateDerivative hu (m := 1) (by norm_num) a).differentiableAt le_rfl
  have huj := (contDiffAt_coordinateDerivative hu (m := 1) (by norm_num) j).differentiableAt le_rfl
  have hsub : coordinateDerivative j (fun y => coordinateDerivative a u y - β y * coordinateDerivative j u y) z =
      coordinateDerivative j (coordinateDerivative a u) z -
        coordinateDerivative j (fun y => β y * coordinateDerivative j u y) z := by
    exact congrArg (fun D : CoordinateSpace n →L[ℝ] ℝ => D (Pi.single j 1))
      (fderiv_fun_sub hua (hβ.fun_mul huj))
  rw [hsub, coordinateDerivative_mul_at hβ huj]
  change coordinateHessian u z a j - _ = _
  change _ - (coordinateDerivative j β z * coordinateDerivative j u z +
    β z * coordinateHessian u z j j) = _
  ring

/-- The field derivative bound is exactly the missing adapted mixed entry,
up to a first-derivative error from the fixed defining chart. -/
theorem adapted_mixed_hessian_bound {u β : CoordinateSpace n → ℝ}
    {z : CoordinateSpace n} (hu : ContDiffAt ℝ 2 u z) (hβ : DifferentiableAt ℝ β z)
    (a j : Fin n) {K B M : ℝ} (hB : 0 ≤ B)
    (hT : |coordinateDerivative j
      (fun y => coordinateDerivative a u y - β y * coordinateDerivative j u y) z| ≤ K)
    (hb : |coordinateDerivative j β z| ≤ B) (hg : |coordinateDerivative j u z| ≤ M) :
    |coordinateHessian u z a j - β z * coordinateHessian u z j j| ≤ K + B * M := by
  have he := coordinateDerivative_tangential_field hu hβ a j
  have hm : |coordinateDerivative j β z * coordinateDerivative j u z| ≤ B * M := by
    rw [abs_mul]
    exact mul_le_mul hb hg (abs_nonneg _) hB
  calc
    _ = |coordinateDerivative j
        (fun y => coordinateDerivative a u y - β y * coordinateDerivative j u y) z +
        coordinateDerivative j β z * coordinateDerivative j u z| := by rw [he]; ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hT hm)

/-- The genuine quadratic-patch estimate converted to the adapted mixed
entry used by the Schur complement. -/
theorem adapted_mixed_hessian_bound_of_patch [NeZero n]
    {u w β : CoordinateSpace n → ℝ} (hwc : Continuous w)
    (hS : IsCompact {y | w y ≤ 0}) {z : CoordinateSpace n} (a j : Fin n)
    (hw0 : w z = 0) (hwd : DifferentiableAt ℝ w z)
    (hj : coordinateDerivative j w z ≠ 0)
    (hu : ContDiffAt ℝ 2 u z) (hβ : DifferentiableAt ℝ β z)
    {r C M κ B₁ G : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hκ : 0 < κ) (hB₁ : 0 ≤ B₁)
    (hβ1 : |coordinateDerivative j β z| ≤ B₁) (hug : |coordinateDerivative j u z| ≤ G)
    (hT0 : coordinateDerivative a u z - β z * coordinateDerivative j u z = 0)
    (hTc : ContinuousOn (fun y => coordinateDerivative a u y - β y * coordinateDerivative j u y)
      ({y | w y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}))
    (hbT : ∀ y ∈ frontier {y | w y ≤ 0}, boundaryPatchQuadratic z y ≤ r →
      coordinateDerivative a u y - β y * coordinateDerivative j u y = 0)
    (hTbound : ∀ y ∈ {y | w y ≤ 0}, boundaryPatchQuadratic z y = r →
      |coordinateDerivative a u y - β y * coordinateDerivative j u y| ≤ C)
    (hT2 : ∀ y ∈ interior ({y | w y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}),
      ContDiffAt ℝ 2 (fun y => coordinateDerivative a u y - β y * coordinateDerivative j u y) y)
    (hw2 : ∀ y ∈ interior ({y | w y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}), ContDiffAt ℝ 2 w y)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ y ∈ interior ({y | w y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}), (A y).PosDef)
    (hLT : ∀ y ∈ interior ({y | w y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}),
      |linearizedMA (A y) (fun y => coordinateDerivative a u y - β y * coordinateDerivative j u y) y|
        ≤ M * (A y).trace)
    (hHw : ∀ y ∈ interior ({y | w y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}),
      (coordinateHessian w y - κ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) :
    |coordinateHessian u z a j - β z * coordinateHessian u z j j| ≤
      ((C/r+M)/κ) * |coordinateDerivative j w z| + B₁ * G := by
  have hTd : DifferentiableAt ℝ
      (fun y => coordinateDerivative a u y - β y * coordinateDerivative j u y) z :=
    ((contDiffAt_coordinateDerivative hu (m := 1) (by norm_num) a).differentiableAt le_rfl).sub
      (hβ.fun_mul ((contDiffAt_coordinateDerivative hu (m := 1) (by norm_num) j).differentiableAt le_rfl))
  have ht := mixed_boundary_estimate_on_quadratic_patch hwc hS hw0 hT0 hwd hTd
    (show 0 < fderiv ℝ w z (coordinateTransverse w z j) by rw [fderiv_coordinateTransverse_self hj]; norm_num)
    hr hC hM hκ hTc hbT hTbound hT2 hw2 hA hLT hHw
  rw [fderiv_coordinateTransverse_self hj, mul_one] at ht
  exact adapted_mixed_hessian_bound hu hβ a j hB₁
    (coordinateDerivative_bound_of_transverse_bound hj ht) hβ1 hug

end GaussianTilt.MomentMapRegularity
