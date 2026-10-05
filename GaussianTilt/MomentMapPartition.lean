import GaussianTilt.MomentMapFenchel

/-! # Polynomial partition control for regular moment-measure targets

The direct variational method for a target with a positive density on an
inner ball does not need an imported functional Santaló inequality. A local
bound on its nonnegative dual potential gives an explicit polynomial upper
bound on the Fenchel partition. The Laplace comparison kernel is integrated
exactly using product coordinates.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators InnerProductSpace
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

lemma integral_laplace_kernel {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, Real.exp (-a * |x|)) = 2 / a := by
  rw [integral_comp_abs (f := fun x => Real.exp (-a * x)), integral_exp_mul_Ioi (neg_neg_of_pos ha) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, mul_one_div]

def laplaceProduct (a : ℝ) (x : E n) : ℝ := ∏ i, Real.exp (-a * |x i|)

lemma integral_laplaceProduct {a : ℝ} (ha : 0 < a) :
    (∫ x : E n, laplaceProduct a x) = (2 / a) ^ n := by
  have h := (PiLp.volume_preserving_ofLp (Fin n)).integral_comp
    (EuclideanSpace.measurableEquiv (Fin n)).measurableEmbedding
    (fun x : Fin n → ℝ => ∏ i, Real.exp (-a * |x i|))
  change (∫ x : E n, laplaceProduct a x) = _ at h
  rw [h, integral_fintype_prod_volume_eq_pow (fun x : ℝ => Real.exp (-a * |x|)),
    integral_laplace_kernel ha, Fintype.card_fin]

lemma integrable_laplaceProduct {a : ℝ} (ha : 0 < a) :
    Integrable (laplaceProduct (n := n) a) := by
  by_contra hn
  have h := integral_laplaceProduct (n := n) ha
  rw [integral_undef hn] at h
  have hp : 0 < (2 / a) ^ n := by positivity
  linarith

lemma laplaceProduct_eq_exp_sum (a : ℝ) (x : E n) :
    laplaceProduct a x = Real.exp (-a * ∑ i, |x i|) := by
  rw [laplaceProduct, ← Real.exp_sum, Finset.mul_sum]

lemma coordinate_abs_sum_le (x : E n) : ∑ i, |x i| ≤ ((n : ℝ) + 1) * ‖x‖ := by
  have h : (∑ i : Fin n, |x i|) ≤ ∑ _i : Fin n, ‖x‖ := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  nlinarith [norm_nonneg x]

theorem fenchel_density_laplace_bound {K : Set (E n)} {u : E n → ℝ} {R r B : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ y ∈ K, 0 ≤ u y)
    (hr : 0 < r) (hB : 0 ≤ B) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hu0 : u 0 = 0) (huB : ∀ y ∈ Metric.closedBall (0 : E n) r, u y ≤ B)
    (x : E n) : Real.exp (-fenchel K u x) ≤ Real.exp 1 *
      laplaceProduct (r / ((B + 1) * ((n : ℝ) + 1))) x := by
  let a := r / ((B + 1) * ((n : ℝ) + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have hscaled := mul_le_mul_of_nonneg_left (coordinate_abs_sum_le x) ha.le
  have heq : a * (((n : ℝ) + 1) * ‖x‖) = r / (B + 1) * ‖x‖ := by
    dsimp [a]
    field_simp
  rw [heq] at hscaled
  have hlin := fenchel_budget_lower_bound hK hu hr hB hball hu0 huB x
  rw [laplaceProduct_eq_exp_sum, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change -fenchel K u x ≤ 1 + -a * ∑ i, |x i|
  linarith

/-- A finite positive source partition is constructed from the actual dual
potential. Its upper bound is polynomial, rather than exponential, in the
inner-ball bound `B`. -/
theorem fenchel_partition_bounds {K : Set (E n)} {u : E n → ℝ} {R r B : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ y ∈ K, 0 ≤ u y)
    (hr : 0 < r) (hB : 0 ≤ B) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hu0 : u 0 = 0) (huB : ∀ y ∈ Metric.closedBall (0 : E n) r, u y ≤ B) :
    Integrable (fun x => Real.exp (-fenchel K u x)) ∧
      0 < (∫ x, Real.exp (-fenchel K u x)) ∧
      (∫ x, Real.exp (-fenchel K u x)) ≤
        Real.exp 1 * (2 * ((B + 1) * ((n : ℝ) + 1)) / r) ^ n := by
  have hKn : K.Nonempty := ⟨0, hball (Metric.mem_closedBall_self hr.le)⟩
  have hcont : Continuous (fun x => Real.exp (-fenchel K u x)) :=
    Real.continuous_exp.comp (fenchel_lipschitz hKn hK hu).continuous.neg
  let a := r / ((B + 1) * ((n : ℝ) + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have hmajor := (integrable_laplaceProduct (n := n) ha).const_mul (Real.exp 1)
  have hbound := fenchel_density_laplace_bound hK hu hr hB hball hu0 huB
  have hi : Integrable (fun x => Real.exp (-fenchel K u x)) := hmajor.mono' hcont.aestronglyMeasurable
    (ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hbound x))
  refine ⟨hi, integral_exp_pos hi, ?_⟩
  have h := integral_mono hi hmajor hbound
  rw [integral_const_mul, integral_laplaceProduct ha] at h
  convert h using 1
  congr 2
  dsimp [a]
  field_simp

end GaussianTilt.MomentMapCoercivity
