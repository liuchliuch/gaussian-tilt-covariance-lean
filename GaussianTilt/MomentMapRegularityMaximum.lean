import GaussianTilt.MomentMapRegularityMatrix
import GaussianTilt.LetwinConvexity

/-! # The actual second-derivative maximum principle

This file derives Hessian negativity from a local maximum, before applying
the log-determinant inequality to smooth Monge--Ampère solutions.
-/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity

lemma second_deriv_nonpos_of_isLocalMax {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a : ℝ} (ha : IsLocalMax f a) : deriv (deriv f) a ≤ 0 := by
  by_contra! hpos
  have hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have he : ∀ᶠ x in 𝓝 a, 0 < deriv (deriv f) x ∧ f x ≤ f a :=
    ((hd.continuous_deriv le_rfl).continuousAt.eventually (eventually_gt_nhds hpos)).and ha
  obtain ⟨ε, hε, heε⟩ := Metric.eventually_nhds_iff.mp he
  let b := a + ε / 2
  have hab : a < b := by dsimp [b]; linarith
  have hnear (x : ℝ) (hx : x ∈ Icc a b) : dist x a < ε := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
    dsimp [b] at hx
    linarith [hx.2]
  have hdm : StrictMonoOn (deriv f) (Icc a b) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hd.continuous.continuousOn
      (fun x hx => (heε (hnear x (interior_subset hx))).1)
  have hm : StrictMonoOn f (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hf.continuous.continuousOn
    intro x hx
    have hx' : x ∈ Ioo a b := by simpa [interior_Icc] using hx
    have hh := hdm ⟨le_rfl, hab.le⟩ ⟨hx'.1.le, hx'.2.le⟩ hx'.1
    rw [ha.deriv_eq_zero] at hh
    exact hh
  exact (not_lt_of_ge (heε (hnear b ⟨hab.le, le_rfl⟩)).2)
    (hm ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab)

open GaussianTilt.Letwin in
/-- A C² function has negative semidefinite Hessian at every local maximum.
The scalar second-derivative test is applied to each actual affine line. -/
theorem neg_hessian_posSemidef_of_isLocalMax {n : ℕ} {f : CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) {x : CoordinateSpace n} (hx : IsLocalMax f x) :
    (-coordinateHessian f x).PosSemidef := by
  constructor
  · have hs := coordinateHessian_isSymm hf x
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_eq_transpose_of_trivial] using congrArg Neg.neg hs.eq
  · intro v
    let F := fun t : ℝ => f (x + t • v)
    have hF : ContDiff ℝ 2 F := hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
    have hFx : IsLocalMax F 0 := by
      have hc : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
      have hx' : ∀ᶠ y in 𝓝 (x + (0 : ℝ) • v), f y ≤ f x := by simpa using hx
      change ∀ᶠ t in 𝓝 (0 : ℝ), F t ≤ F 0
      simpa [F] using hc.tendsto.eventually hx'
    have hh := second_deriv_nonpos_of_isLocalMax hF hFx
    change deriv (deriv (fun t : ℝ => f (x + t • v))) 0 ≤ 0 at hh
    rw [second_deriv_affine_line_comp hf, zero_smul, add_zero,
      secondFDeriv_eq_hessianQuadratic hf.contDiffAt] at hh
    simpa only [star_trivial, Matrix.neg_mulVec, dotProduct_neg,
      matrixQuadratic, neg_nonneg] using hh

open GaussianTilt.Letwin

def secondDifference {n : ℕ} (f : CoordinateSpace n → ℝ) (h x : CoordinateSpace n) : ℝ :=
  f (x + h) + f (x + -h) - 2 * f x

lemma contDiff_secondDifference {n : ℕ} {k : WithTop ℕ∞} {f : CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ k f) (h : CoordinateSpace n) : ContDiff ℝ k (secondDifference f h) :=
  ((hf.comp (contDiff_id.add contDiff_const)).add
    (hf.comp (contDiff_id.add contDiff_const))).sub (contDiff_const.mul hf)

lemma coordinateDerivative_secondDifference {n : ℕ} {f : CoordinateSpace n → ℝ}
    (hf : Differentiable ℝ f) (h x : CoordinateSpace n) (i : Fin n) :
    coordinateDerivative i (secondDifference f h) x = secondDifference (coordinateDerivative i f) h x := by
  have hp : DifferentiableAt ℝ (fun y => f (y + h)) x :=
    (hf (x + h)).comp x (differentiableAt_id.add_const h)
  have hm : DifferentiableAt ℝ (fun y => f (y + -h)) x :=
    (hf (x + -h)).comp x (differentiableAt_id.add_const (-h))
  unfold secondDifference coordinateDerivative
  rw [fderiv_fun_sub (hp.fun_add hm) ((hf x).const_mul 2), fderiv_fun_add hp hm,
    fderiv_const_mul (hf x) 2, fderiv_comp_add_right, fderiv_comp_add_right]
  rfl

lemma coordinateHessian_secondDifference {n : ℕ} {f : CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (h x : CoordinateSpace n) :
    coordinateHessian (secondDifference f h) x =
      coordinateHessian f (x + h) + coordinateHessian f (x + -h) - (2 : ℝ) • coordinateHessian f x := by
  have hd := hf.differentiable (by norm_num)
  ext i j
  change coordinateDerivative j (coordinateDerivative i (secondDifference f h)) x = _
  rw [show coordinateDerivative i (secondDifference f h) =
    secondDifference (coordinateDerivative i f) h from
      funext (fun y => coordinateDerivative_secondDifference hd h y i)]
  rw [coordinateDerivative_secondDifference
    ((contDiff_coordinateDerivative hf (m := 1) (by norm_num) i).differentiable le_rfl)]
  rfl

/-- The actual Monge--Ampère equation and a local maximum imply the
finite-difference target/source comparison used by Caffarelli and Klartag. -/
theorem mongeAmpere_secondDifference_at_max {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hH : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    {h x : CoordinateSpace n} (hmax : IsLocalMax (secondDifference φ h) x) :
    V (coordinateGradient φ (x + h)) + V (coordinateGradient φ (x + -h)) -
      2 * V (coordinateGradient φ x) ≤ secondDifference φ h x := by
  have hneg := neg_hessian_posSemidef_of_isLocalMax (contDiff_secondDifference hφ h) hmax
  rw [coordinateHessian_secondDifference hφ] at hneg
  have hm : ((2 : ℝ) • coordinateHessian φ x -
      (coordinateHessian φ (x + h) + coordinateHessian φ (x + -h))).PosSemidef := by
    convert hneg using 1
    abel
  have hh := log_det_second_difference_nonpos (hH x) (hH (x + h)) (hH (x + -h)) hm
  rw [hMA, hMA, hMA] at hh
  dsimp [secondDifference]
  linarith

lemma gradient_secondDifference_at_max {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : Differentiable ℝ φ) {h x : CoordinateSpace n}
    (hmax : IsLocalMax (secondDifference φ h) x) :
    coordinateGradient φ (x + h) + coordinateGradient φ (x + -h) =
      (2 : ℝ) • coordinateGradient φ x := by
  have hz := hmax.fderiv_eq_zero
  ext i
  have hi : coordinateDerivative i (secondDifference φ h) x = 0 := by
    simp [coordinateDerivative, hz]
  rw [coordinateDerivative_secondDifference hφ] at hi
  change coordinateDerivative i φ (x + h) + coordinateDerivative i φ (x + -h) =
    2 * coordinateDerivative i φ x
  dsimp [secondDifference] at hi
  linarith

lemma convex_fderiv_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {x : E}
    (hx : DifferentiableAt ℝ φ x) (y : E) : φ x + fderiv ℝ φ x (y - x) ≤ φ y := by
  let l : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hc' : ConvexOn ℝ univ (φ ∘ l) := by simpa using hc.comp_affineMap l
  have hd : HasDerivAt (φ ∘ l) (fderiv ℝ φ x (y - x)) 0 := by
    have hx' : HasFDerivAt φ (fderiv ℝ φ x) (l 0) := by simpa [l] using hx.hasFDerivAt
    exact hx'.comp_hasDerivAt 0 (by simpa [l] using
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ))))
  have hs := hc'.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) (by norm_num) hd
  have hs' : fderiv ℝ φ x (y - x) ≤ φ y - φ x := by
    simpa [l, slope_def_field] using hs
  linarith

lemma secondDifference_le_gradient_gap {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ) (h x : CoordinateSpace n) :
    secondDifference φ h x ≤
      ∑ i, (coordinateGradient φ (x + h) i - coordinateGradient φ (x + -h) i) * h i := by
  have hp := convex_fderiv_support hc (hd (x + h)) x
  have hm := convex_fderiv_support hc (hd (x + -h)) x
  rw [show x - (x + h) = -h by abel, map_neg, fderiv_apply_eq_sum_coordinates] at hp
  rw [show x - (x + -h) = h by abel, fderiv_apply_eq_sum_coordinates] at hm
  dsimp [secondDifference]
  have he : (∑ i, (coordinateGradient φ (x + h) i - coordinateGradient φ (x + -h) i) * h i) =
      (∑ i, h i * coordinateDerivative i φ (x + h)) -
      ∑ i, h i * coordinateDerivative i φ (x + -h) := by
    simp only [coordinateGradient, sub_mul, Finset.sum_sub_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  rw [he]
  linarith

lemma stronglyConvex_secondDifference {n : ℕ} {V : CoordinateSpace n → ℝ}
    {K : Set (CoordinateSpace n)} {κ : ℝ} (hc : StrongConvexOn K κ V)
    {p u : CoordinateSpace n} (hp : p + u ∈ K) (hm : p + -u ∈ K) :
    κ * ‖u‖ ^ 2 ≤ secondDifference V u p := by
  have h := hc.2 hp hm (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
  have havg : (1 / 2 : ℝ) • (p + u) + (1 / 2 : ℝ) • (p + -u) = p := by module
  have hdiff : p + u - (p + -u) = (2 : ℝ) • u := by module
  rw [havg, hdiff, norm_smul] at h
  norm_num at h
  dsimp [secondDifference]
  nlinarith

/-- A quantitative finite-difference maximum principle. No source Hessian
bound is assumed: it follows at every attained second-difference maximum
from the Monge--Ampère equation and strict target convexity. The factor n²
comes only from using the library's sup norm on raw coordinate vectors. -/
theorem secondDifference_bound_at_max {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : ConvexOn ℝ univ φ)
    (hH : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    {K : Set (CoordinateSpace n)} {κ : ℝ} (hκ : 0 < κ)
    (hVc : StrongConvexOn K κ V) (hg : ∀ x, coordinateGradient φ x ∈ K)
    {h x : CoordinateSpace n} (hmax : IsLocalMax (secondDifference φ h) x) :
    secondDifference φ h x ≤ 4 * (n : ℝ)^2 * ‖h‖^2 / κ := by
  let p := coordinateGradient φ x
  let u := coordinateGradient φ (x + h) - p
  have hplus : coordinateGradient φ (x + h) = p + u := by dsimp [u]; abel
  have hminus : coordinateGradient φ (x + -h) = p + -u := by
    have hh := gradient_secondDifference_at_max (hφ.differentiable (by norm_num)) hmax
    change coordinateGradient φ (x + h) + coordinateGradient φ (x + -h) = (2 : ℝ) • p at hh
    rw [hplus] at hh
    ext i
    have hi := congrFun hh i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    change coordinateGradient φ (x + -h) i = p i + -u i
    linarith
  have hlo : κ * ‖u‖^2 ≤ secondDifference φ h x := by
    have hv := stronglyConvex_secondDifference hVc (hplus ▸ hg (x + h)) (hminus ▸ hg (x + -h))
    have hm := mongeAmpere_secondDifference_at_max hφ hH hMA hmax
    rw [hplus, hminus] at hm
    exact hv.trans hm
  have hup : secondDifference φ h x ≤ 2 * (n : ℝ) * ‖u‖ * ‖h‖ := by
    apply (secondDifference_le_gradient_gap hc (hφ.differentiable (by norm_num)) h x).trans
    rw [hplus, hminus]
    calc
      (∑ i, ((p + u) i - (p + -u) i) * h i) = ∑ i, 2 * (u i * h i) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Pi.add_apply, Pi.neg_apply]
        ring
      _ ≤ ∑ _ : Fin n, 2 * (‖u‖ * ‖h‖) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc
          u i * h i ≤ |u i * h i| := le_abs_self _
          _ = |u i| * |h i| := abs_mul _ _
          _ ≤ ‖u‖ * ‖h‖ := mul_le_mul (by simpa using norm_le_pi_norm u i)
            (by simpa using norm_le_pi_norm h i) (abs_nonneg _) (norm_nonneg _)
      _ = _ := by simp; ring
  have hu : ‖u‖ ≤ (2 * (n : ℝ) * ‖h‖) / κ := by
    apply (le_div_iff₀ hκ).mpr
    by_cases hu : ‖u‖ = 0
    · rw [hu, zero_mul]; positivity
    · have hu' : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
      nlinarith
  apply hup.trans
  apply (le_div_iff₀ hκ).mpr
  have hn : 0 ≤ (2 : ℝ) * n * ‖h‖ := by positivity
  have hh := mul_le_mul_of_nonneg_left hu hn
  have hhk := (mul_le_mul_of_nonneg_right hh hκ.le)
  field_simp at hhk
  nlinarith

end GaussianTilt.MomentMapRegularity
