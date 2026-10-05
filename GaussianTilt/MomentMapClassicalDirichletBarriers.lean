import GaussianTilt.MomentMapClassicalDirichletContinuationData

/-!
# Uniform zero-boundary barriers along the actual continuation path

Positive rescalings of the smooth defining potential are compared with each
classical solution using its true determinant equation. The resulting
bounds are uniform in the continuation parameter.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- A C² function with positive Hessian and zero boundary values is
nonpositive on the compact domain, by the actual elliptic maximum principle. -/
theorem classical_posDef_nonpos_of_zero_boundary [NeZero n]
    {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    {u : CoordinateSpace n → ℝ} (huc : ContinuousOn u S)
    (hu : ∀ x ∈ interior S, ContDiffAt ℝ 2 u x)
    (hH : ∀ x ∈ interior S, (coordinateHessian u x).PosDef)
    (hb : ∀ x ∈ frontier S, u x = 0) : ∀ x ∈ S, u x ≤ 0 := by
  apply classical_dirichlet_maximum_principle hS huc hu (fun x hx => (hH x hx).inv)
  · intro x hx
    simp only [linearizedMA, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hH x hx).det_pos.ne'),
      Matrix.trace_one, Fintype.card_fin]
    positivity
  · exact fun x hx => (hb x hx).le

/-- Uniform scaled defining-function barriers for all parameters of
`det Hess u = (1−t) det Hess w + t`, proved from determinant homogeneity. -/
theorem dirichletContinuation_scaled_barriers [NeZero n]
    {S : Set (CoordinateSpace n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {w : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (hwH : ∀ x ∈ S, (coordinateHessian w x).PosDef)
    (hwb : ∀ x ∈ frontier S, w x = 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : CoordinateSpace n → ℝ,
      ContinuousOn u S → (∀ x ∈ interior S, ContDiffAt ℝ 2 u x) →
      (∀ x ∈ interior S, (coordinateHessian u x).PosDef) →
      (∀ x ∈ frontier S, u x = 0) →
      (∀ x ∈ interior S, (coordinateHessian u x).det = dirichletContinuationDensity w t x) →
      ∀ x ∈ S, b * w x ≤ u x ∧ u x ≤ a * w x := by
  obtain ⟨c, C, hc, hC, hbounds⟩ := dirichletContinuationDensity_uniform_bounds hS hSn hw hwH
  let a := min 1 (c / C)
  let b := max 1 (C / c)
  have ha : 0 < a := lt_min zero_lt_one (div_pos hc hC)
  have hb : 0 < b := zero_lt_one.trans_le (le_max_left _ _)
  have ha1 : a ≤ 1 := min_le_left _ _
  have hb1 : 1 ≤ b := le_max_left _ _
  have hac : a * C ≤ c := (le_div_iff₀ hC).mp (min_le_right _ _)
  have hbc : C ≤ b * c := (div_le_iff₀ hc).mp (le_max_right _ _)
  have hap : a ^ n ≤ a := pow_le_of_le_one ha.le ha1 (NeZero.ne n)
  have hbp : b ≤ b ^ n := le_self_pow₀ hb1 (NeZero.ne n)
  have hw2 : ContDiff ℝ 2 w := contDiff_infty.mp hw 2
  have hscaled (s : ℝ) (x : CoordinateSpace n) :
      (coordinateHessian (fun y => s * w y) x).det = s ^ n * (coordinateHessian w x).det := by
    rw [coordinateHessian_const_mul_at hw2.contDiffAt, Matrix.det_smul, Fintype.card_fin]
  refine ⟨a, b, ha, hb, ?_⟩
  intro t ht u huc hu huH hub hMA
  have hlo (x : CoordinateSpace n) (hx : x ∈ interior S) :
      (coordinateHessian (fun y => a * w y) x).det ≤ (coordinateHessian u x).det := by
    have hd := hbounds 0 (by norm_num) x (interior_subset hx)
    simp only [dirichletContinuationDensity_zero] at hd
    rw [hscaled, hMA x hx]
    calc
      a ^ n * (coordinateHessian w x).det ≤ a * (coordinateHessian w x).det :=
        mul_le_mul_of_nonneg_right hap (hwH x (interior_subset hx)).det_pos.le
      _ ≤ a * C := mul_le_mul_of_nonneg_left hd.2 ha.le
      _ ≤ c := hac
      _ ≤ _ := (hbounds t ht x (interior_subset hx)).1
  have hhi (x : CoordinateSpace n) (hx : x ∈ interior S) :
      (coordinateHessian u x).det ≤ (coordinateHessian (fun y => b * w y) x).det := by
    have hd := hbounds 0 (by norm_num) x (interior_subset hx)
    simp only [dirichletContinuationDensity_zero] at hd
    rw [hscaled, hMA x hx]
    calc
      _ ≤ C := (hbounds t ht x (interior_subset hx)).2
      _ ≤ b * c := hbc
      _ ≤ b * (coordinateHessian w x).det := mul_le_mul_of_nonneg_left hd.1 hb.le
      _ ≤ b ^ n * (coordinateHessian w x).det :=
        mul_le_mul_of_nonneg_right hbp (hwH x (interior_subset hx)).det_pos.le
  have hscaledPD (s : ℝ) (hs : 0 < s) (x : CoordinateSpace n) (hx : x ∈ interior S) :
      (coordinateHessian (fun y => s * w y) x).PosDef := by
    rw [coordinateHessian_const_mul_at hw2.contDiffAt]
    exact (hwH x (interior_subset hx)).smul hs
  have hl := classical_dirichlet_mongeAmpere_comparison hS
    (continuousOn_const.mul hw.continuous.continuousOn) huc
    (fun _ _ => contDiffAt_const.mul hw2.contDiffAt) hu (hscaledPD b hb) huH hhi
    (fun x hx => by simp [hwb x hx, hub x hx])
  have hh := classical_dirichlet_mongeAmpere_comparison hS huc
    (continuousOn_const.mul hw.continuous.continuousOn) hu
    (fun _ _ => contDiffAt_const.mul hw2.contDiffAt) huH (hscaledPD a ha) hlo
    (fun x hx => by simp [hwb x hx, hub x hx])
  exact fun x hx => ⟨hl x hx, hh x hx⟩

/-- The actual solution sup norms stay uniformly bounded along the
continuation path, before any Hessian estimate or solvability argument. -/
theorem dirichletContinuation_uniform_C0_bound [NeZero n]
    {S : Set (CoordinateSpace n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {w : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (hwH : ∀ x ∈ S, (coordinateHessian w x).PosDef)
    (hwb : ∀ x ∈ frontier S, w x = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : CoordinateSpace n → ℝ,
      ContinuousOn u S → (∀ x ∈ interior S, ContDiffAt ℝ 2 u x) →
      (∀ x ∈ interior S, (coordinateHessian u x).PosDef) →
      (∀ x ∈ frontier S, u x = 0) →
      (∀ x ∈ interior S, (coordinateHessian u x).det = dirichletContinuationDensity w t x) →
      ∀ x ∈ S, |u x| ≤ B := by
  obtain ⟨a, b, ha, hb, hbar⟩ := dirichletContinuation_scaled_barriers hS hSn hw hwH hwb
  obtain ⟨W, hW⟩ := hS.exists_bound_of_continuousOn hw.continuous.continuousOn
  refine ⟨b * max W 0, mul_nonneg hb.le (le_max_right _ _), ?_⟩
  intro t ht u huc hu huH hub hMA x hx
  obtain ⟨hlo, _⟩ := hbar t ht u huc hu huH hub hMA x hx
  have hu0 := classical_posDef_nonpos_of_zero_boundary hS huc hu huH hub x hx
  have hwbound : |w x| ≤ max W 0 :=
    (by simpa only [Real.norm_eq_abs] using hW x hx : |w x| ≤ W).trans (le_max_left _ _)
  rw [abs_of_nonpos hu0]
  nlinarith [neg_abs_le (w x)]

end GaussianTilt.MomentMapRegularity
