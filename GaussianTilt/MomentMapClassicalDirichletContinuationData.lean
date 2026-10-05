import GaussianTilt.MomentMapClassicalDirichletOperator

/-!
# Actual right-hand-side control for the fixed-domain continuation path

The homotopy starts at the determinant of the defining potential and ends
at unit density. Intermediate densities are not constant. Their positivity,
smoothness, and uniform logarithmic derivative bounds on the compact
parameter-domain cylinder are proved here from the defining potential.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def dirichletContinuationDensity (w : CoordinateSpace n → ℝ) (t : ℝ) (x : CoordinateSpace n) : ℝ :=
  (1 - t) * (coordinateHessian w x).det + t

@[simp] lemma dirichletContinuationDensity_zero (w : CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    dirichletContinuationDensity w 0 x = (coordinateHessian w x).det := by
  simp [dirichletContinuationDensity]

@[simp] lemma dirichletContinuationDensity_one (w : CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    dirichletContinuationDensity w 1 x = 1 := by
  simp [dirichletContinuationDensity]

lemma contDiff_dirichletContinuationDensity {w : CoordinateSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun z : ℝ × CoordinateSpace n => dirichletContinuationDensity w z.1 z.2) := by
  have hd : ContDiff ℝ ∞ (fun x => (coordinateHessian w x).det) :=
    contDiff_matrix_det (smooth_coordinateHessian hw)
  exact ((contDiff_const.sub contDiff_fst).mul (hd.comp contDiff_snd)).add contDiff_fst

lemma dirichletContinuationDensity_pos {w : CoordinateSpace n → ℝ}
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : CoordinateSpace n}
    (hH : (coordinateHessian w x).PosDef) : 0 < dirichletContinuationDensity w t x := by
  have hd := hH.det_pos
  dsimp [dirichletContinuationDensity]
  by_cases ht1 : t = 1
  · simp [ht1]
  · have hlt : t < 1 := lt_of_le_of_ne ht.2 ht1
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hd) ht.1

/-- Uniform positive lower and upper forcing bounds, derived by compact
extrema of the actual defining Hessian determinant. -/
theorem dirichletContinuationDensity_uniform_bounds {S : Set (CoordinateSpace n)}
    (hS : IsCompact S) (hSn : S.Nonempty) {w : CoordinateSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (hH : ∀ x ∈ S, (coordinateHessian w x).PosDef) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ S,
      c ≤ dirichletContinuationDensity w t x ∧ dirichletContinuationDensity w t x ≤ C := by
  have hd : Continuous (fun x => (coordinateHessian w x).det) :=
    (contDiff_matrix_det (smooth_coordinateHessian hw)).continuous
  obtain ⟨a, ha, hmin⟩ := hS.exists_isMinOn hSn hd.continuousOn
  obtain ⟨b, hb, hmax⟩ := hS.exists_isMaxOn hSn hd.continuousOn
  let c := min (coordinateHessian w a).det 1
  let C := max (coordinateHessian w b).det 1
  have hc : 0 < c := lt_min (hH a ha).det_pos zero_lt_one
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨c, C, hc, hC, ?_⟩
  intro t ht x hx
  have hlo : c ≤ (coordinateHessian w x).det := (min_le_left _ _).trans (hmin hx)
  have hhi : (coordinateHessian w x).det ≤ C := (hmax hx).trans (le_max_left _ _)
  have hc1 : c ≤ 1 := min_le_right _ _
  have hC1 : 1 ≤ C := le_max_right _ _
  dsimp [dirichletContinuationDensity]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hlo),
      mul_nonneg ht.1 (sub_nonneg.mpr hc1)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hhi),
      mul_nonneg ht.1 (sub_nonneg.mpr hC1)]

/-- All actual joint derivatives of the logarithmic forcing are uniformly
bounded on `[0,1]×S`. In particular, general-RHS Pogorelov and Calabi
calculations can use these bounds; the constant-density cancellations are
not applied at intermediate continuation parameters. -/
theorem dirichletContinuationDensity_uniform_log_derivatives {S : Set (CoordinateSpace n)}
    (hS : IsCompact S) {w : CoordinateSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (hH : ∀ x ∈ S, (coordinateHessian w x).PosDef) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ S,
      ‖iteratedFDeriv ℝ k
        (fun z : ℝ × CoordinateSpace n => Real.log (dirichletContinuationDensity w z.1 z.2)) (t, x)‖ ≤ B := by
  let K : Set (ℝ × CoordinateSpace n) := Icc (0 : ℝ) 1 ×ˢ S
  have hK : IsCompact K := isCompact_Icc.prod hS
  have hlog : ∀ z ∈ K, ContDiffAt ℝ ∞
      (fun z : ℝ × CoordinateSpace n => Real.log (dirichletContinuationDensity w z.1 z.2)) z := by
    intro z hz
    exact (contDiff_dirichletContinuationDensity hw).contDiffAt.log
      (dirichletContinuationDensity_pos hz.1 (hH _ hz.2)).ne'
  have hderiv : ContinuousOn (iteratedFDeriv ℝ k
      (fun z : ℝ × CoordinateSpace n => Real.log (dirichletContinuationDensity w z.1 z.2))) K := by
    intro z hz
    exact ((hlog z hz).iteratedFDeriv_right (m := 0) (by simpa using (show (k : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hderiv
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro t ht x hx
  exact (hB (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)

end GaussianTilt.MomentMapRegularity
