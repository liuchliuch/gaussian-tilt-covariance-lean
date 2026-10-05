import GaussianTilt.MomentMapRegularityMaximum

/-! # From decay at infinity to actual global Hessian bounds

Maximum attainment and the passage from second differences to second
derivatives are proved here. The remaining geometric infinity condition is
kept explicit; this file does not claim general moment-source regularity.
-/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin

lemma exists_max_of_nonneg_tendsto_zero {E : Type*} [TopologicalSpace E] [Nonempty E]
    {f : E → ℝ} (hf : Continuous f) (hn : ∀ x, 0 ≤ f x)
    (ht : Tendsto f (cocompact E) (𝓝 0)) : ∃ x, ∀ y, f y ≤ f x := by
  by_cases hz : ∀ x, f x = 0
  · exact ⟨Classical.arbitrary E, fun y => by rw [hz y, hz]⟩
  · push_neg at hz
    obtain ⟨x, hx⟩ := hz
    exact hf.exists_forall_ge' x (ht.eventually (eventually_le_nhds
      (lt_of_le_of_ne (hn x) (Ne.symm hx))))

lemma secondDifference_nonneg {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hc : ConvexOn ℝ univ φ) (h x : CoordinateSpace n) : 0 ≤ secondDifference φ h x := by
  have hh := hc.2 (mem_univ (x + h)) (mem_univ (x + -h))
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
  have hm : (1 / 2 : ℝ) • (x + h) + (1 / 2 : ℝ) • (x + -h) = x := by module
  rw [hm] at hh
  dsimp [secondDifference]
  simp only [smul_eq_mul] at hh
  linarith

/-- Decay of the actual second difference at infinity supplies a genuine
maximizer. Thus the local maximum principle gives the global estimate. -/
theorem secondDifference_bound_of_decay {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : ConvexOn ℝ univ φ)
    (hH : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    {K : Set (CoordinateSpace n)} {κ : ℝ} (hκ : 0 < κ)
    (hVc : StrongConvexOn K κ V) (hg : ∀ x, coordinateGradient φ x ∈ K)
    {h : CoordinateSpace n}
    (hdecay : Tendsto (secondDifference φ h) (cocompact (CoordinateSpace n)) (𝓝 0))
    (x : CoordinateSpace n) :
    secondDifference φ h x ≤ 4 * (n : ℝ)^2 * ‖h‖^2 / κ := by
  obtain ⟨z, hz⟩ := exists_max_of_nonneg_tendsto_zero
    (contDiff_secondDifference hφ h).continuous (secondDifference_nonneg hc h) hdecay
  exact (hz x).trans (secondDifference_bound_at_max hφ hc hH hMA hκ hVc hg
    (Filter.Eventually.of_forall hz))

/-- Passing from bounded second differences to the actual second derivative
uses the proved local maximum test, without an assumed difference quotient
limit or an assumed Hessian bound. -/
lemma second_deriv_le_of_secondDifference_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {C : ℝ} (hb : ∀ t, f t + f (-t) - 2 * f 0 ≤ C * t^2) : deriv (deriv f) 0 ≤ C := by
  let G := fun t => f t + f (-t) - 2 * f 0 - C * t^2
  have hG : ContDiff ℝ 2 G :=
    ((hf.add (hf.comp contDiff_neg)).sub contDiff_const).sub (contDiff_const.mul (contDiff_id.pow 2))
  have hm : IsLocalMax G 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have h := hb t
    dsimp [G]
    norm_num
    linarith
  have hd := hf.differentiable (by norm_num)
  have hd' := hf.differentiable_deriv_two
  have hD (t : ℝ) : HasDerivAt G (deriv f t - deriv f (-t) - 2 * C * t) t := by
    have hn := (hd (-t)).hasDerivAt.comp t (hasDerivAt_neg t)
    have h := (((hd t).hasDerivAt.add hn).sub_const (2 * f 0)).sub
      (((hasDerivAt_id t).pow 2).const_mul C)
    convert h using 1 <;> dsimp [G] <;> ring
  have hDD : HasDerivAt (fun t => deriv f t - deriv f (-t) - 2 * C * t)
      (2 * deriv (deriv f) 0 - 2 * C) 0 := by
    have hn := (hd' (-(0 : ℝ))).hasDerivAt.comp 0 (hasDerivAt_neg (0 : ℝ))
    have h := ((hd' 0).hasDerivAt.sub hn).sub ((hasDerivAt_id (0 : ℝ)).const_mul (2 * C))
    convert h using 1 <;> simp <;> ring
  have he : deriv G = (fun t => deriv f t - deriv f (-t) - 2 * C * t) := funext (fun t => (hD t).deriv)
  have hh := second_deriv_nonpos_of_isLocalMax hG hm
  rw [he, hDD.deriv] at hh
  linarith

lemma hessian_diagonal_le_of_secondDifference_bound {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) {C : ℝ}
    (hb : ∀ h x, secondDifference φ h x ≤ C * ‖h‖ ^ 2)
    (x : CoordinateSpace n) (i : Fin n) : coordinateHessian φ x i i ≤ C := by
  let e : CoordinateSpace n := Pi.single i 1
  let f := fun t : ℝ => φ (x + t • e)
  have hf : ContDiff ℝ 2 f := hφ.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have he : ‖e‖ = 1 := by simp [e, Pi.norm_single]
  have hb' : ∀ t, f t + f (-t) - 2 * f 0 ≤ C * t ^ 2 := by
    intro t
    have h := hb (t • e) x
    simpa [f, secondDifference, neg_smul, norm_smul, he, Real.norm_eq_abs, sq_abs] using h
  have hh := second_deriv_le_of_secondDifference_bound hf hb'
  change deriv (deriv (fun t : ℝ => φ (x + t • e))) 0 ≤ C at hh
  rw [second_deriv_affine_line_comp hφ, zero_smul, add_zero] at hh
  simpa only [coordinateHessian_eq_secondFDerivAt hφ.contDiffAt, e] using hh

lemma abs_entry_le_of_posSemidef_diagonal_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {C : ℝ} (hC : ∀ i, A i i ≤ C)
    (i j : ι) : |A i j| ≤ C := by
  have hs : A j i = A i j := by
    have h := congrFun (congrFun hA.isHermitian.eq i) j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have hp := hA.2 ((Pi.single i 1 : ι → ℝ) + Pi.single j 1)
  have hm := hA.2 ((Pi.single i 1 : ι → ℝ) - Pi.single j 1)
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_sub,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub,
    Matrix.mulVec_single, MulOpposite.op_one, one_smul, single_dotProduct, Matrix.col_apply, one_mul, mul_one, hs] at hp hm
  exact abs_le.mpr ⟨by linarith [hC i, hC j], by linarith [hC i, hC j]⟩

/-- The complete maximum-principle Hessian estimate after the geometric
infinity condition is supplied. Uniform boundedness of Hessian entries is a
conclusion, not an assumption. -/
theorem hessian_entries_bounded_of_secondDifference_decay {n : ℕ}
    {φ V : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : ConvexOn ℝ univ φ)
    (hH : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    {K : Set (CoordinateSpace n)} {κ : ℝ} (hκ : 0 < κ)
    (hVc : StrongConvexOn K κ V) (hg : ∀ x, coordinateGradient φ x ∈ K)
    (hdecay : ∀ h, Tendsto (secondDifference φ h) (cocompact (CoordinateSpace n)) (𝓝 0)) :
    ∀ x i j, |coordinateHessian φ x i j| ≤ 4 * (n : ℝ)^2 / κ := by
  have hb : ∀ h x, secondDifference φ h x ≤ (4 * (n : ℝ)^2 / κ) * ‖h‖^2 := by
    intro h x
    convert secondDifference_bound_of_decay hφ hc hH hMA hκ hVc hg (hdecay h) x using 1
    ring
  intro x i j
  exact abs_entry_le_of_posSemidef_diagonal_bound (hH x).posSemidef
    (hessian_diagonal_le_of_secondDifference_bound hφ hb x) i j

/-- Convexity turns flattening of endpoint gradients into decay of the
actual second difference. No mean-value point or uniform line selection is
assumed. -/
theorem secondDifference_decay_of_gradient_gap {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ) (h : CoordinateSpace n)
    (hgap : Tendsto (fun x => coordinateGradient φ (x + h) - coordinateGradient φ (x + -h))
      (cocompact (CoordinateSpace n)) (𝓝 0)) :
    Tendsto (secondDifference φ h) (cocompact (CoordinateSpace n)) (𝓝 0) := by
  have hf : Continuous (fun v : CoordinateSpace n => ∑ i, v i * h i) := by fun_prop
  have hl := hf.continuousAt.tendsto.comp hgap
  have hl' : Tendsto (fun x => ∑ i,
      (coordinateGradient φ (x + h) i - coordinateGradient φ (x + -h) i) * h i)
      (cocompact (CoordinateSpace n)) (𝓝 0) := by
    simpa [Function.comp_def] using hl
  exact squeeze_zero (secondDifference_nonneg hc h)
    (secondDifference_le_gradient_gap hc hd h) hl'

end GaussianTilt.MomentMapRegularity
