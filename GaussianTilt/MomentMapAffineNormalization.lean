import GaussianTilt.MomentMapRegularityGeometry

/-!
# Dimension-only affine normalization of compact convex bodies

The normalization is constructed from a largest determinant parallelotope
with one fixed vertex in the interior. No ellipsoid or regularity theorem is
assumed.
-/
noncomputable section
open Set Metric
open scoped Topology BigOperators
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Matrix whose columns are the indicated displacements. -/
def normalizationMatrix (a : E n) (v : Fin n → E n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (v j - a) i

lemma continuous_normalizationMatrix_det (a : E n) :
    Continuous (fun v : Fin n → E n => |(normalizationMatrix a v).det|) := by
  apply Continuous.abs
  apply Continuous.matrix_det
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp
    ((continuous_apply j).sub continuous_const)

/-- A compact full-dimensional set contains a maximum-volume based parallelotope
with nonzero determinant. Convexity is not needed for this step. -/
theorem exists_maximal_normalizationMatrix {S : Set (E n)}
    (hS : IsCompact S) {a : E n} (ha : a ∈ interior S) :
    ∃ v : Fin n → E n, (∀ i, v i ∈ S) ∧ (normalizationMatrix a v).det ≠ 0 ∧
      ∀ w : Fin n → E n, (∀ i, w i ∈ S) →
        |(normalizationMatrix a w).det| ≤ |(normalizationMatrix a v).det| := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  let w : Fin n → E n := fun i => a + (ε / 2) • EuclideanSpace.single i (1 : ℝ)
  have hw : ∀ i, w i ∈ S := by
    intro i
    apply hball
    rw [mem_ball, dist_eq_norm]
    dsimp [w]
    rw [add_sub_cancel_left, norm_smul, EuclideanSpace.norm_single]
    simp only [norm_one, mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hmat : normalizationMatrix a w = Matrix.diagonal (fun _ => ε / 2) := by
    ext i j
    simp [normalizationMatrix, w, Matrix.diagonal, EuclideanSpace.single_apply]
  have hdet : (normalizationMatrix a w).det ≠ 0 := by
    rw [hmat, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => ne_of_gt (half_pos hε))
  let K : Set (Fin n → E n) := univ.pi (fun _ => S)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => hS)
  obtain ⟨v, hv, hmax⟩ := hK.exists_isMaxOn
    (show K.Nonempty from ⟨w, fun i _ => hw i⟩)
    (continuous_normalizationMatrix_det a).continuousOn
  have hle := hmax (show w ∈ K from fun i _ => hw i)
  refine ⟨v, (fun i => hv i (mem_univ i)), ?_, ?_⟩
  · intro hz
    change |(normalizationMatrix a w).det| ≤ |(normalizationMatrix a v).det| at hle
    rw [hz, abs_zero] at hle
    exact (abs_pos.mpr hdet).not_ge hle
  · intro u hu
    exact hmax (show u ∈ K from fun i _ => hu i)

/-- The linear map which sends coordinates to the maximal displacement frame. -/
def normalizationFrame (a : E n) (v : Fin n → E n)
    (h : (normalizationMatrix a v).det ≠ 0) : E n ≃L[ℝ] E n :=
  (Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (normalizationMatrix a v) (isUnit_iff_ne_zero.mpr h)).toContinuousLinearEquiv

lemma normalizationFrame_apply (a : E n) (v : Fin n → E n)
    (h : (normalizationMatrix a v).det ≠ 0) (x : E n) (i : Fin n) :
    normalizationFrame a v h x i = ∑ j, x j * (v j - a) i := by
  change (Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (normalizationMatrix a v) x) i = _
  rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toEuclideanLin_apply]
  simp [Matrix.mulVec, dotProduct, normalizationMatrix, mul_comm]

lemma normalizationFrame_single (a : E n) (v : Fin n → E n)
    (h : (normalizationMatrix a v).det ≠ 0) (j : Fin n) :
    normalizationFrame a v h (EuclideanSpace.single j 1) = v j - a := by
  ext i
  rw [normalizationFrame_apply]
  simp [EuclideanSpace.single_apply]

/-- Maximality forces every coordinate of the body to lie between -1 and 1. -/
theorem normalizationFrame_coordinates_le {S : Set (E n)} {a : E n}
    {v : Fin n → E n} (hv : ∀ i, v i ∈ S)
    (hdet : (normalizationMatrix a v).det ≠ 0)
    (hmax : ∀ w : Fin n → E n, (∀ i, w i ∈ S) →
      |(normalizationMatrix a w).det| ≤ |(normalizationMatrix a v).det|)
    {x : E n} (hx : x ∈ S) (j : Fin n) :
    |(normalizationFrame a v hdet).symm (x - a) j| ≤ 1 := by
  classical
  let L := normalizationFrame a v hdet
  let c := L.symm (x - a)
  have hLc : L c = x - a := L.apply_symm_apply _
  have hcoord (i : Fin n) : (x - a) i = ∑ k, c k * (v k - a) i := by
    rw [← hLc]
    exact normalizationFrame_apply a v hdet c i
  have hmatrix : normalizationMatrix a (Function.update v j x) =
      (normalizationMatrix a v).updateCol j (fun i => (x - a) i) := by
    ext i k
    by_cases hk : k = j <;> simp [normalizationMatrix, hk]
  have hrepl := hmax (Function.update v j x) (by
    intro k
    by_cases hk : k = j <;> simp [Function.update_apply, hk, hx, hv])
  change |(normalizationMatrix a (Function.update v j x)).det| ≤ _ at hrepl
  rw [hmatrix] at hrepl
  have heq : ((normalizationMatrix a v).updateCol j (fun i => (x - a) i)).det =
      c j * (normalizationMatrix a v).det := by
    simp_rw [hcoord]
    exact Matrix.det_updateCol_sum (normalizationMatrix a v) j c
  rw [heq, abs_mul] at hrepl
  have hd : 0 < |(normalizationMatrix a v).det| := abs_pos.mpr hdet
  change |c j| ≤ 1
  nlinarith

/-- Coordinate decomposition in the standard Euclidean basis. -/
lemma normalization_sum_single (x : E n) :
    ∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ) = x := by
  simpa [EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr,
    PiLp.basisFun_apply] using (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr x

/-- The Euclidean norm is bounded by the coordinate one-norm. -/
lemma normalization_norm_le_sum_abs (x : E n) : ‖x‖ ≤ ∑ i : Fin n, |x i| := by
  calc
    ‖x‖ = ‖∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ)‖ := by
      rw [normalization_sum_single]
    _ ≤ ∑ i : Fin n, ‖x i • EuclideanSpace.single i (1 : ℝ)‖ := norm_sum_le _ _
    _ = ∑ i : Fin n, |x i| := by simp [norm_smul, EuclideanSpace.norm_single]

/-- Any convex set containing the standard simplex contains every nonnegative
coordinate vector whose coordinate sum is at most one. -/
lemma normalization_simplex_mem {U : Set (E n)} (hU : Convex ℝ U)
    (h0 : (0 : E n) ∈ U) (he : ∀ i : Fin n, EuclideanSpace.single i (1 : ℝ) ∈ U)
    {x : E n} (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i : Fin n, x i ≤ 1) : x ∈ U := by
  classical
  let w : Option (Fin n) → ℝ := fun i => i.elim (1 - ∑ j, x j) (fun j => x j)
  let z : Option (Fin n) → E n := fun i => i.elim 0 (fun j => EuclideanSpace.single j 1)
  have hw : ∀ i ∈ (Finset.univ : Finset (Option (Fin n))), 0 ≤ w i := by
    rintro (_ | i) _
    · dsimp [w]; linarith
    · exact hx i
  have hw1 : ∑ i : Option (Fin n), w i = 1 := by
    rw [Fintype.sum_option]; dsimp [w]; ring
  have hz : ∀ i ∈ (Finset.univ : Finset (Option (Fin n))), z i ∈ U := by
    rintro (_ | i) _
    · exact h0
    · exact he i
  have hm := hU.sum_mem hw hw1 hz
  simpa [Fintype.sum_option, w, z, normalization_sum_single] using hm

/-- An explicit ball inside the standard simplex, written in scaled coordinates. -/
lemma normalization_unit_ball_simplex {U : Set (E n)} (hU : Convex ℝ U)
    (h0 : (0 : E n) ∈ U) (he : ∀ i : Fin n, EuclideanSpace.single i (1 : ℝ) ∈ U)
    {y : E n} (hy : ‖y‖ ≤ 1) :
    (2 * ((n : ℝ) + 1))⁻¹ • (y + WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))) ∈ U := by
  let d : ℝ := 2 * ((n : ℝ) + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  have hyi (i : Fin n) : |y i| ≤ 1 := by
    have hi : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
    exact hi.trans hy
  apply normalization_simplex_mem hU h0 he
  · intro i
    change 0 ≤ d⁻¹ * (y i + 1)
    exact mul_nonneg (inv_nonneg.mpr hd.le) (by have := (abs_le.mp (hyi i)).1; linarith)
  · change (∑ i : Fin n, d⁻¹ * (y i + 1)) ≤ 1
    rw [← Finset.mul_sum]
    have hs : (∑ i : Fin n, (y i + 1)) ≤ 2 * n := by
      calc
        (∑ i : Fin n, (y i + 1)) ≤ ∑ i : Fin n, (2 : ℝ) := by
          apply Finset.sum_le_sum; intro i _
          have := (abs_le.mp (hyi i)).2
          linarith
        _ = 2 * n := by simp; ring
    rw [← div_eq_inv_mul, div_le_one hd]
    exact hs.trans (by dsimp [d]; linarith)

/-- Every compact full-dimensional convex body admits an affine normalization
between the unit ball and a ball of dimension-only radius. The explicit
constant is deliberately coarse; no sharp John ellipsoid theorem is used. -/
theorem exists_affine_normalization_explicit {S : Set (E n)}
    (hS : IsCompact S) (hc : Convex ℝ S) (hi : (interior S).Nonempty) :
    ∃ a : E n, ∃ T : E n ≃L[ℝ] E n,
      closedBall 0 1 ⊆ (fun x => T (x - a)) '' S ∧
      (fun x => T (x - a)) '' S ⊆ closedBall 0 (3 * ((n : ℝ) + 1) ^ 2) := by
  classical
  obtain ⟨a, ha⟩ := hi
  obtain ⟨v, hv, hdet, hmax⟩ := exists_maximal_normalizationMatrix hS ha
  let L : E n ≃L[ℝ] E n := normalizationFrame a v hdet
  let U : Set (E n) := (fun x => L.symm (x - a)) '' S
  have hU : Convex ℝ U := by
    have ht := (hc.translate (-a)).linear_image L.symm.toLinearMap
    simpa only [image_image, Function.comp_def, neg_add_eq_sub] using ht
  have h0 : (0 : E n) ∈ U := ⟨a, interior_subset ha, by simp⟩
  have he : ∀ i : Fin n, EuclideanSpace.single i (1 : ℝ) ∈ U := by
    intro i
    refine ⟨v i, hv i, ?_⟩
    change L.symm (v i - a) = _
    rw [← normalizationFrame_single a v hdet i]
    exact L.symm_apply_apply _
  let d : ℝ := 2 * ((n : ℝ) + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  let e : E n := WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))
  let b : E n := d⁻¹ • e
  let T : E n ≃L[ℝ] E n := L.symm.trans
    (LinearEquiv.smulOfNeZero ℝ (E n) d hd.ne').toContinuousLinearEquiv
  have hdb : d • b = e := by
    dsimp [b]
    rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
  have hT (x : E n) : T (x - (a + L b)) = d • L.symm (x - a) - e := by
    change d • L.symm (x - (a + L b)) = _
    rw [show x - (a + L b) = (x - a) - L b by abel,
      map_sub, L.symm_apply_apply, smul_sub, hdb]
  refine ⟨a + L b, T, ?_, ?_⟩
  · intro y hy
    have hyn : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
    have hmem : d⁻¹ • (y + e) ∈ U := normalization_unit_ball_simplex hU h0 he hyn
    obtain ⟨x, hx, hxy⟩ := hmem
    refine ⟨x, hx, ?_⟩
    change T (x - (a + L b)) = y
    change L.symm (x - a) = _ at hxy
    rw [hT, hxy, smul_smul, mul_inv_cancel₀ hd.ne', one_smul, add_sub_cancel_right]
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    change ‖T (x - (a + L b))‖ ≤ _
    rw [hT]
    have hcoord (i : Fin n) : |L.symm (x - a) i| ≤ 1 :=
      normalizationFrame_coordinates_le hv hdet hmax hx i
    have hbound (i : Fin n) : |(d • L.symm (x - a) - e) i| ≤ d + 1 := by
      change |d * L.symm (x - a) i - 1| ≤ d + 1
      calc
        |d * L.symm (x - a) i - 1| ≤ |d * L.symm (x - a) i| + |(1 : ℝ)| :=
          abs_sub _ _
        _ = d * |L.symm (x - a) i| + 1 := by rw [abs_mul, abs_of_pos hd, abs_one]
        _ ≤ d * 1 + 1 := by gcongr; exact hcoord i
        _ = d + 1 := by ring
    calc
      ‖d • L.symm (x - a) - e‖ ≤ ∑ i : Fin n, |(d • L.symm (x - a) - e) i| :=
        normalization_norm_le_sum_abs _
      _ ≤ ∑ _i : Fin n, (d + 1) := Finset.sum_le_sum (fun i _ => hbound i)
      _ = (n : ℝ) * (d + 1) := by simp; ring
      _ ≤ 3 * ((n : ℝ) + 1) ^ 2 := by dsimp [d]; nlinarith [sq_nonneg (n : ℝ)]

/-- Dimension-only affine normalization, in a form that can be applied uniformly
to arbitrary compact convex sections. -/
theorem exists_dimension_affine_normalization :
    ∃ C : ℕ → ℝ, ∀ n, 0 < C n ∧
      ∀ S : Set (E n), IsCompact S → Convex ℝ S → (interior S).Nonempty →
        ∃ a : E n, ∃ T : E n ≃L[ℝ] E n,
          closedBall 0 1 ⊆ (fun x => T (x - a)) '' S ∧
          (fun x => T (x - a)) '' S ⊆ closedBall 0 (C n) := by
  refine ⟨fun n => 3 * ((n : ℝ) + 1) ^ 2, ?_⟩
  intro n
  refine ⟨by positivity, ?_⟩
  intro S hS hc hi
  exact exists_affine_normalization_explicit hS hc hi

end GaussianTilt.MomentMapRegularity
