import GaussianTilt.EllipticRegularityEnergy

/-! # Constructed Euclidean cutoffs with vanishing gradient energy -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

/-- One fixed genuine compact smooth bump, rescaled in the spatial variable. -/
def ellipticCutoff (n : ℕ) (R : ℝ) (x : CoordinateSpace n) : ℝ :=
  (default : ContDiffBump (0 : CoordinateSpace n)) (R⁻¹ • x)

lemma ellipticCutoff_contDiff (n : ℕ) (R : ℝ) : ContDiff ℝ ∞ (ellipticCutoff n R) :=
  (default : ContDiffBump (0 : CoordinateSpace n)).contDiff.comp (contDiff_const.smul contDiff_id)

lemma ellipticCutoff_nonneg (n : ℕ) (R : ℝ) (x : CoordinateSpace n) :
    0 ≤ ellipticCutoff n R x := (default : ContDiffBump (0 : CoordinateSpace n)).nonneg

lemma ellipticCutoff_le_one (n : ℕ) (R : ℝ) (x : CoordinateSpace n) :
    ellipticCutoff n R x ≤ 1 := (default : ContDiffBump (0 : CoordinateSpace n)).le_one

lemma ellipticCutoff_compact (n : ℕ) {R : ℝ} (hR : R ≠ 0) :
    HasCompactSupport (ellipticCutoff n R) :=
  (default : ContDiffBump (0 : CoordinateSpace n)).hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR))

lemma ellipticCutoff_eq_one {n : ℕ} {R : ℝ} (hR : 0 < R) {x : CoordinateSpace n}
    (hx : ‖x‖ ≤ R) : ellipticCutoff n R x = 1 := by
  apply (default : ContDiffBump (0 : CoordinateSpace n)).one_of_mem_closedBall
  change dist (R⁻¹ • x) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  exact (inv_mul_le_one₀ hR).mpr hx

lemma ellipticCutoff_eq_zero {n : ℕ} {R : ℝ} (hR : 0 < R) {x : CoordinateSpace n}
    (hx : 2 * R ≤ ‖x‖) : ellipticCutoff n R x = 0 := by
  apply (default : ContDiffBump (0 : CoordinateSpace n)).zero_of_le_dist
  change 2 ≤ dist (R⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le),
    ← div_eq_inv_mul]
  exact (le_div_iff₀ hR).mpr hx

lemma coordinateDerivative_comp_smul {n : ℕ} {u : CoordinateSpace n → ℝ}
    (hu : Differentiable ℝ u) (c : ℝ) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => u (c • y)) x = c * coordinateDerivative i u (c • x) := by
  unfold coordinateDerivative
  change (fderiv ℝ (u ∘ (fun y => c • y)) x) (Pi.single i 1) = _
  rw [((hu (c • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul c)).fderiv]
  simp

lemma gradientSquare_comp_smul {n : ℕ} {u : CoordinateSpace n → ℝ}
    (hu : Differentiable ℝ u) (c : ℝ) (x : CoordinateSpace n) :
    gradientSquare (fun y => u (c • y)) x = c ^ 2 * gradientSquare u (c • x) := by
  simp [gradientSquare, coordinateDerivative_comp_smul hu, mul_pow, Finset.mul_sum]

/-- The derivative bound is constructed from the fixed bump; the decay is
exactly quadratic in the spatial scale. -/
theorem ellipticCutoff_gradient_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, ∀ x : CoordinateSpace n,
      gradientSquare (ellipticCutoff n R) x ≤ R⁻¹ ^ 2 * C := by
  let b := (default : ContDiffBump (0 : CoordinateSpace n))
  obtain ⟨C, hC⟩ := (gradientSquare_hasCompactSupport b.hasCompactSupport).exists_bound_of_continuous
    (continuous_gradientSquare b.contDiff)
  refine ⟨max C 0, le_max_right _ _, fun R x => ?_⟩
  change gradientSquare (fun y => b (R⁻¹ • y)) x ≤ _
  rw [gradientSquare_comp_smul ((b.contDiff (n := 1)).differentiable le_rfl)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact (le_abs_self _).trans ((hC _).trans (le_max_left _ _))

lemma ellipticCutoff_eventually_one {n : ℕ} (x : CoordinateSpace n) :
    ∀ᶠ k : ℕ in atTop, ellipticCutoff n ((k : ℝ) + 1) x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with k hk
  apply ellipticCutoff_eq_one (by positivity)
  have : (N : ℝ) ≤ k := by exact_mod_cast hk
  linarith

end GaussianTilt.Letwin
