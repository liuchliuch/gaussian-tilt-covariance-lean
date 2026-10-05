import GaussianTilt.LetwinAbsolute
import GaussianTilt.LetwinTensorMetric

/-! # Letwin's regular quadratic Hessian trace bound -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ContDiff
namespace GaussianTilt.Letwin

open scoped MatrixOrder in
/-- The positive-semidefinite case of Letwin theorem 2.5. Every integral,
energy comparison, mean identity, and functional Brascamp--Lieb step is proved. -/
theorem regular_mongeAmpere_trace_bound_posSemidef {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hc : ConvexOn ℝ univ φ)
    (hH : ∀ x, (coordinateHessian φ x).PosDef)
    {K U : Set (CoordinateSpace n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (hV : ContDiffOn ℝ 2 V U) (hVc : ConvexOn ℝ U V)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (hiso : covarianceMatrix (potentialMeasure φ) (coordinateGradient φ) = 1)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef) :
    (∫ x, Matrix.trace (B * coordinateHessian φ x * B * coordinateHessian φ x) ∂potentialMeasure φ) ≤
      2 * Matrix.trace (B ^ 2) := by
  let R := CFC.sqrt B
  have hRp : R.PosSemidef := (CFC.sqrt_nonneg B).posSemidef
  have hR : R.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hRp.isHermitian
  have hBs : B.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hB.isHermitian
  have hRR : R * R = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  obtain ⟨hqi, hei, hpi, hri, hidentity⟩ :=
    integrated_hessian_trace_energy hφ hc hH hK hU hKU hgrad hV hVc hMA S hHb R hR
  have hcompare : (∫ x, hessianSandwichEnergy R φ x ∂potentialMeasure φ) ≤
      ∫ x, hessianSandwichThirdTerm R φ x ∂potentialMeasure φ :=
    integral_mono hei hri (fun x => hessianSandwichEnergy_le_thirdTerm (contDiff_infty.mp hφ 3) R hR x (hH x))
  have hp0 : 0 ≤ ∫ x, hessianSandwichVTerm R φ V x ∂potentialMeasure φ := by
    apply integral_nonneg
    intro x
    exact (hessianSandwich_remainders_nonneg (contDiff_infty.mp hφ 2) (hH x).posSemidef
      hU hVc hV (hKU (hgrad x)) R hR).1
  obtain ⟨Rg, hRg⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn)
  have hgb : ∀ x i, |coordinateGradient φ x i| ≤ Rg := by
    intro x i
    have h : |coordinateGradient φ x i| ≤ ‖coordinateGradient φ x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (coordinateGradient φ x) i
    exact h.trans (hRg _ (hgrad x))
  have hBL := hessian_sandwich_variance_le_energy hφ hH Rg S hgb hHb hiso R hei
  have hfinal : (∫ x, hessianSandwichSquare R φ x ∂potentialMeasure φ) ≤ 2 * hsSquare (R * R) := by
    linarith
  calc
    _ = ∫ x, hessianSandwichSquare R φ x ∂potentialMeasure φ := by
      apply integral_congr_ae
      filter_upwards with x
      unfold hessianSandwichSquare
      rw [hsSquare_conjugate_eq_trace R _ hR (coordinateHessian_isSymm (contDiff_infty.mp hφ 2) x), hRR]
    _ ≤ 2 * hsSquare (R * R) := hfinal
    _ = _ := by rw [hRR, hsSquare_eq_trace_square B hBs]

lemma bounded_continuous_matrix_function {Ω κ : Type*} [Fintype κ]
    {H : Ω → Matrix κ κ ℝ} (S : ℝ) (hH : ∀ x i j, |H x i j| ≤ S)
    (f : Matrix κ κ ℝ → ℝ) (hf : Continuous f) : ∃ C : ℝ, ∀ x, |f (H x)| ≤ C := by
  let K : Set (κ × κ → ℝ) := Icc (fun _ => -|S|) (fun _ => |S|)
  let Q := fun z : κ × κ → ℝ => f (Matrix.of fun i j => z (i, j))
  have hreshape : Continuous (fun z : κ × κ → ℝ => Matrix.of fun i j => z (i, j)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_apply (i, j)
  have hQ : Continuous Q := hf.comp hreshape
  have hK : IsCompact K := isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hQ.continuousOn
  refine ⟨C, fun x => ?_⟩
  have hx : (fun p : κ × κ => H x p.1 p.2) ∈ K := by
    constructor
    · intro p; exact (abs_le.mp ((hH x p.1 p.2).trans (le_abs_self S))).1
    · intro p; exact (abs_le.mp ((hH x p.1 p.2).trans (le_abs_self S))).2
  have h := hC _ hx
  simpa only [Q, Matrix.of_apply, Real.norm_eq_abs] using h

lemma integrable_hessian_quadratic_trace {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => Matrix.trace (B * coordinateHessian φ x * B * coordinateHessian φ x)) (potentialMeasure φ) := by
  have hF : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => Matrix.trace (B * M * B * M)) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    fun_prop
  have hHm : Continuous (coordinateHessian φ) := continuous_pi fun i =>
    continuous_pi fun j => (smooth_coordinateHessian hφ i j).continuous
  obtain ⟨C, hC⟩ := bounded_continuous_matrix_function S hHb _ hF
  exact Integrable.of_bound (hF.comp hHm).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)

/-- Letwin theorem 2.5 for every symmetric test matrix, including indefinite
and singular matrices. The absolute-value reduction is proved spectrally. -/
theorem regular_mongeAmpere_trace_bound {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hc : ConvexOn ℝ univ φ)
    (hH : ∀ x, (coordinateHessian φ x).PosDef)
    {K U : Set (CoordinateSpace n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (hV : ContDiffOn ℝ 2 V U) (hVc : ConvexOn ℝ U V)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (hiso : covarianceMatrix (potentialMeasure φ) (coordinateGradient φ) = 1)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    (∫ x, Matrix.trace (B * coordinateHessian φ x * B * coordinateHessian φ x) ∂potentialMeasure φ) ≤
      2 * Matrix.trace (B ^ 2) := by
  have hBh : B.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using hB
  calc
    _ ≤ ∫ x, Matrix.trace (spectralAbsolute hBh * coordinateHessian φ x *
        spectralAbsolute hBh * coordinateHessian φ x) ∂potentialMeasure φ :=
      integral_mono (integrable_hessian_quadratic_trace hφ S hHb B)
        (integrable_hessian_quadratic_trace hφ S hHb (spectralAbsolute hBh))
        (fun x => trace_quadratic_le_spectralAbsolute hBh _ (hH x).posSemidef)
    _ ≤ 2 * Matrix.trace ((spectralAbsolute hBh)^2) :=
      regular_mongeAmpere_trace_bound_posSemidef hφ hc hH hK hU hKU hgrad hV hVc hMA S hHb hiso
        (spectralAbsolute hBh) (spectralAbsolute_posSemidef hBh)
    _ = _ := by rw [spectralAbsolute_trace_square hBh]

end GaussianTilt.Letwin
