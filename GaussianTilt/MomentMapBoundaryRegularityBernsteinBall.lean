import GaussianTilt.MomentMapBoundaryRegularityBernsteinCutoff

/-! # Explicit ball estimate for the genuine Bernstein inequality -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinate_square_sum_eq_norm (v : CoordinateSpace n) :
    (∑ i, v i^2) = ‖(coordinateEquiv n).symm v‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rfl

lemma bilinear_square_le_entry_bound (A : Matrix (Fin n) (Fin n) ℝ)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hA : ∀ i j, |A i j| ≤ Λ) (g v : CoordinateSpace n) :
    (g ⬝ᵥ (A *ᵥ v))^2 ≤ (n : ℝ)^2 * Λ^2 * (∑ i, g i^2) * (∑ i, v i^2) := by
  have hcs := square_sum_pair_bound A (fun i j => g i * v j) hΛ hA
  have hsum : (∑ i, ∑ j, (g i * v j)^2) = (∑ i, g i^2) * (∑ j, v j^2) := by
    simp only [mul_pow, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hd : g ⬝ᵥ (A *ᵥ v) = ∑ i, ∑ j, A i j * (g i * v j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hd]
  rw [hsum] at hcs
  nlinarith [hcs]

def bernsteinBallBound (n : ℕ) (Λ κ C R : ℝ) : ℝ :=
  (R^4 + 2*(4*(n:ℝ)*Λ*R^2 + 24*Λ*R^2 + 2*C*R^4)/κ +
    64*(n:ℝ)^2*Λ^2*R^2/κ^2)/R^4

theorem bernstein_ball_center_bound
    {F : CoordinateSpace n → ℝ} (hF : ContDiff ℝ 2 F)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (g : CoordinateSpace n → CoordinateSpace n)
    (c : CoordinateSpace n) {R κ Λ C : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hΛ : 0 ≤ Λ) (hC : 0 ≤ C)
    (hA : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R → (A y).PosSemidef)
    (hEll : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      ∀ v : CoordinateSpace n, v ⬝ᵥ (A y *ᵥ v) ≤ Λ * ‖(coordinateEquiv n).symm v‖^2)
    (hgF : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      (∑ i, g y i^2) ≤ F y)
    (hLF : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      κ*(F y)^2 ≤ linearizedMA (A y) F y +
        2*(g y ⬝ᵥ (A y *ᵥ coordinateGradient F y)) + C*(F y+1)) :
    F c ≤ bernsteinBallBound n Λ κ C R := by
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
  have hcross : ∀ y ∈ interior S,
      (g y ⬝ᵥ (A y *ᵥ coordinateGradient η y))^2 ≤ 4*(n:ℝ)^2*Λ^2*R^2 * F y := by
    intro y hy
    have hdiag (i : Fin n) : A y i i ≤ Λ := by
      have hh := hEll y (hnear hy) (Pi.single i 1)
      simpa [Matrix.mulVec_single_one, single_dotProduct, Matrix.col, e, coordinateEquiv,
        EuclideanSpace.norm_eq, PiLp.norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq] using hh
    have hab := abs_entry_le_of_posSemidef_diagonal_bound (hA y (hnear hy)) hdiag
    have hbound := bilinear_square_le_entry_bound (A y) hΛ hab (g y) (coordinateGradient η y)
    have hηnorm : (∑ i, (coordinateGradient η y i)^2) ≤ 4*R^2 := by
      rw [coordinate_square_sum_eq_norm, coordinateGradient_calabiBallCutoff]
      simp only [map_smul, map_sub, norm_smul, Real.norm_eq_abs, abs_neg, mul_pow]
      norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2), pow_two]
      have hh := hnear hy
      change ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R at hh
      nlinarith [norm_nonneg ((coordinateEquiv n).symm y - (coordinateEquiv n).symm c)]
    have hmul := mul_le_mul (hgF y (hnear hy)) hηnorm (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      ((Finset.sum_nonneg (fun _ _ => sq_nonneg _)).trans (hgF y (hnear hy)))
    have hm := mul_le_mul_of_nonneg_left hmul (show 0 ≤ (n:ℝ)^2*Λ^2 by positivity)
    nlinarith
  have hbound := bernstein_cutoff_bound_on_compact hS
    (contDiff_infty.mp (contDiff_calabiBallCutoff c R) 2) hF g
    (fun y hy => hA y (hnear hy)) hzero hηpos hκ hC (sq_nonneg R)
    (by positivity : 0 ≤ 2*(n:ℝ)*Λ) (by positivity : 0 ≤ 4*Λ*R^2)
    (by positivity : 0 ≤ 4*(n:ℝ)^2*Λ^2*R^2)
    hηB (fun y hy => hLF y (hnear hy)) hLη hΓ hcross c
    (show c ∈ S from ⟨e.symm c, Metric.mem_closedBall_self hR.le, e.apply_symm_apply c⟩)
  have hηc : calabiBallCutoff c R c = R^2 := by simp [calabiBallCutoff, matrixQuadratic]
  rw [hηc] at hbound
  unfold bernsteinBallBound
  apply (le_div_iff₀ (show 0 < R^4 by positivity)).mpr
  convert hbound using 1 <;> ring

end GaussianTilt.MomentMapRegularity
