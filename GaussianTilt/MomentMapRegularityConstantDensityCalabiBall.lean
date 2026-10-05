import GaussianTilt.MomentMapRegularityConstantDensityCalabiCutoff
import GaussianTilt.MomentMapRegularityConstantDensityNormalized
import GaussianTilt.LetwinQuadraticDuality

/-! # Explicit Euclidean-ball cutoff for Calabi's cubic energy estimate -/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def calabiBallCutoff (c : CoordinateSpace n) (R : ℝ) (x : CoordinateSpace n) : ℝ :=
  R^2 - matrixQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) (x - c)

lemma contDiff_calabiBallCutoff (c : CoordinateSpace n) (R : ℝ) :
    ContDiff ℝ ∞ (calabiBallCutoff c R) :=
  contDiff_const.sub ((contDiff_matrixQuadratic 1).comp (contDiff_id.sub contDiff_const))

lemma calabiBallCutoff_eq_norm (c : CoordinateSpace n) (R : ℝ) (x : CoordinateSpace n) :
    calabiBallCutoff c R x = R^2 - ‖(coordinateEquiv n).symm x - (coordinateEquiv n).symm c‖^2 := by
  unfold calabiBallCutoff matrixQuadratic
  rw [Matrix.one_mulVec, EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, Pi.sub_apply, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (x i - c i) * (x i - c i) = (x i - c i)^2
  ring

lemma coordinateDerivative_calabiBallCutoff (c : CoordinateSpace n) (R : ℝ)
    (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (calabiBallCutoff c R) x = -2 * (x i - c i) := by
  have he : coordinateDerivative i (fun y => matrixQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) (y - c)) x =
      coordinateDerivative i (matrixQuadratic 1) (x - c) := by
    simp only [coordinateDerivative, sub_eq_add_neg, fderiv_comp_add_right]
  change (fderiv ℝ (fun y => R^2 - matrixQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) (y-c)) x) (Pi.single i 1) = _
  rw [fderiv_const_sub]
  change -coordinateDerivative i (fun y => matrixQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) (y-c)) x = _
  rw [he, coordinateDerivative_matrixQuadratic 1 Matrix.isSymm_one, Matrix.one_mulVec]
  simp only [Pi.sub_apply]
  ring

lemma coordinateGradient_calabiBallCutoff (c : CoordinateSpace n) (R : ℝ) (x : CoordinateSpace n) :
    coordinateGradient (calabiBallCutoff c R) x = (-2 : ℝ) • (x-c) := by
  ext i
  exact coordinateDerivative_calabiBallCutoff c R i x

lemma coordinateHessian_calabiBallCutoff (c : CoordinateSpace n) (R : ℝ) (x : CoordinateSpace n) :
    coordinateHessian (calabiBallCutoff c R) x = (-2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  change coordinateDerivative j (coordinateDerivative i (calabiBallCutoff c R)) x = _
  rw [show coordinateDerivative i (calabiBallCutoff c R) = (fun y => -2 * (y i - c i)) from
    funext (coordinateDerivative_calabiBallCutoff c R i)]
  rw [coordinateDerivative_const_mul (show Differentiable ℝ (fun y : CoordinateSpace n => y i - c i) by fun_prop)]
  have hc : coordinateDerivative j (fun y : CoordinateSpace n => y i - c i) x =
      coordinateDerivative j (fun y : CoordinateSpace n => y i) x := by
    simp only [coordinateDerivative, fderiv_sub_const]
  rw [hc, coordinateDerivative_apply]
  by_cases hij : i = j <;> simp [hij, eq_comm]

lemma linearizedMA_calabiBallCutoff (A : Matrix (Fin n) (Fin n) ℝ)
    (c : CoordinateSpace n) (R : ℝ) (x : CoordinateSpace n) :
    linearizedMA A (calabiBallCutoff c R) x = -2 * trace A := by
  simp only [linearizedMA, coordinateHessian_calabiBallCutoff, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

/-- An explicit interior bound for any actual smooth function satisfying
Calabi's quadratic differential inequality on a Euclidean ball. The cutoff
and all its derivative constants are constructed here. -/
theorem calabi_ball_center_bound
    {F : CoordinateSpace n → ℝ} (hF : ContDiff ℝ 2 F)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (c : CoordinateSpace n) {R κ Λ : ℝ} (hR : 0 < R) (hκ : 0 < κ) (hΛ : 0 ≤ Λ)
    (hA : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R → (A y).PosSemidef)
    (hEll : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      ∀ v : CoordinateSpace n, v ⬝ᵥ (A y *ᵥ v) ≤ Λ * ‖(coordinateEquiv n).symm v‖^2)
    (hLF : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      κ * (F y)^2 ≤ linearizedMA (A y) F y) :
    F c ≤ ((4 * (n : ℝ) + 24) * Λ) / (κ * R^2) := by
  let e := coordinateEquiv n
  let S := e '' Metric.closedBall (e.symm c) R
  let η := calabiBallCutoff c R
  have hS : IsCompact S := (isCompact_closedBall _ _).image e.continuous
  have hSi : interior S = e '' Metric.ball (e.symm c) R := by
    change interior (e.toHomeomorph '' Metric.closedBall (e.symm c) R) = _
    rw [← e.toHomeomorph.image_interior, interior_closedBall _ hR.ne']
    rfl
  have hSf : frontier S = e '' Metric.sphere (e.symm c) R := by
    change frontier (e.toHomeomorph '' Metric.closedBall (e.symm c) R) = _
    rw [← e.toHomeomorph.image_frontier, frontier_closedBall _ hR.ne']
    rfl
  have hnear {y : CoordinateSpace n} (hy : y ∈ interior S) : ‖e.symm y - e.symm c‖ < R := by
    rw [hSi] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simpa only [e.symm_apply_apply, Metric.mem_ball, dist_eq_norm] using hz
  have hzero : ∀ y ∈ frontier S, η y = 0 := by
    intro y hy
    rw [hSf] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hnorm : ‖z-e.symm c‖ = R := by simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    dsimp only [η]
    rw [calabiBallCutoff_eq_norm]
    change R^2 - ‖e.symm (e z) - e.symm c‖^2 = 0
    rw [e.symm_apply_apply, hnorm, sub_self]
  have hηpos : ∀ y ∈ interior S, 0 < η y := by
    intro y hy
    dsimp only [η]
    rw [calabiBallCutoff_eq_norm]
    have hh := hnear hy
    nlinarith [norm_nonneg (e.symm y - e.symm c)]
  have hηB : ∀ y ∈ interior S, η y ≤ R^2 := by
    intro y _
    dsimp only [η]
    rw [calabiBallCutoff_eq_norm]
    exact sub_le_self _ (sq_nonneg _)
  have htr {y : CoordinateSpace n} (hy : y ∈ interior S) : trace (A y) ≤ (n : ℝ) * Λ := by
    have hdiag (i : Fin n) : A y i i ≤ Λ := by
      have hh := hEll y (hnear hy) (Pi.single i 1)
      simpa [Matrix.mulVec_single_one, single_dotProduct, Matrix.col, e, coordinateEquiv,
        EuclideanSpace.norm_eq, PiLp.norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq] using hh
    calc
      trace (A y) ≤ ∑ _i : Fin n, Λ := Finset.sum_le_sum (fun i _ => hdiag i)
      _ = _ := by simp
  have hLη : ∀ y ∈ interior S, -(2 * (n : ℝ) * Λ) ≤ linearizedMA (A y) η y := by
    intro y hy
    rw [linearizedMA_calabiBallCutoff]
    nlinarith [htr hy]
  have hΓ : ∀ y ∈ interior S,
      coordinateGradient η y ⬝ᵥ (A y *ᵥ coordinateGradient η y) ≤ 4 * Λ * R^2 := by
    intro y hy
    rw [coordinateGradient_calabiBallCutoff]
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    have he := hEll y (hnear hy) (y-c)
    have hsq : ‖e.symm (y-c)‖^2 ≤ R^2 := by
      rw [map_sub]
      have hh := hnear hy
      nlinarith [norm_nonneg (e.symm y - e.symm c)]
    have hh := mul_le_mul_of_nonneg_left hsq hΛ
    nlinarith
  have hbound := calabi_cutoff_bound_on_compact hS
    (contDiff_infty.mp (contDiff_calabiBallCutoff c R) 2) hF
    (fun y hy => hA y (hnear hy)) hzero hηpos hκ (sq_nonneg R)
    (by positivity : 0 ≤ 2 * (n : ℝ) * Λ) (by positivity : 0 ≤ 4 * Λ * R^2)
    hηB (fun y hy => hLF y (hnear hy)) hLη hΓ c
    (show c ∈ S from ⟨e.symm c, Metric.mem_closedBall_self hR.le, e.apply_symm_apply c⟩)
  have hηc : calabiBallCutoff c R c = R^2 := by simp [calabiBallCutoff, matrixQuadratic]
  rw [hηc] at hbound
  have hh := (le_div_iff₀ hκ).mp hbound
  apply (le_div_iff₀ (mul_pos hκ (sq_pos_of_pos hR))).mpr
  apply (mul_le_mul_right (sq_pos_of_pos hR)).mp
  nlinarith

end GaussianTilt.MomentMapRegularity
