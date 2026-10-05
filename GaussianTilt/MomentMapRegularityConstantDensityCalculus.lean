import GaussianTilt.MomentMapRegularityMaximum

/-!
# Local calculus for constant-density interior estimates

The logarithmic test functions are smooth only inside the section. All
maximum tests in this file are therefore genuinely local, without a global
smoothness assumption on a logarithm that vanishes at the boundary.
-/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
set_option maxHeartbeats 400000
open GaussianTilt.Letwin

lemma contDiffAt_coordinateDerivative {n : ℕ} {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} {k m : WithTop ℕ∞} (hf : ContDiffAt ℝ k f x)
    (hm : m + 1 ≤ k) (i : Fin n) : ContDiffAt ℝ m (coordinateDerivative i f) x := by
  exact (hf.fderiv_right hm).clm_apply contDiffAt_const

lemma contDiffAt_scalar_deriv {f : ℝ → ℝ} {x : ℝ} {k m : WithTop ℕ∞}
    (hf : ContDiffAt ℝ k f x) (hm : m + 1 ≤ k) : ContDiffAt ℝ m (deriv f) x := by
  exact (hf.fderiv_right hm).clm_apply contDiffAt_const

/-- The scalar second derivative test needs smoothness only near the maximum. -/
lemma second_deriv_nonpos_of_isLocalMax_at {f : ℝ → ℝ} {a : ℝ}
    (hf : ContDiffAt ℝ 2 f a) (ha : IsLocalMax f a) : deriv (deriv f) a ≤ 0 := by
  by_contra! hpos
  have hd : ContDiffAt ℝ 1 (deriv f) a := contDiffAt_scalar_deriv hf (by norm_num)
  have hdd : ContinuousAt (deriv (deriv f)) a :=
    (contDiffAt_scalar_deriv hd (m := 0) (by norm_num)).continuousAt
  have he : ∀ᶠ x in 𝓝 a, 0 < deriv (deriv f) x ∧ f x ≤ f a ∧ ContDiffAt ℝ 2 f x := by
    filter_upwards [hdd.eventually (eventually_gt_nhds hpos), ha, hf.eventually (by simp)]
      with x hx hm hs
    exact ⟨hx, hm, hs⟩
  obtain ⟨ε, hε, heε⟩ := Metric.eventually_nhds_iff.mp he
  let b := a + ε / 2
  have hab : a < b := by dsimp [b]; linarith
  have hnear (x : ℝ) (hx : x ∈ Icc a b) : dist x a < ε := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
    dsimp [b] at hx
    linarith [hx.2]
  have hcont : ContinuousOn f (Icc a b) := fun x hx =>
    (heε (hnear x hx)).2.2.continuousAt.continuousWithinAt
  have hdcont : ContinuousOn (deriv f) (Icc a b) := fun x hx =>
    (contDiffAt_scalar_deriv (heε (hnear x hx)).2.2 (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  have hdm : StrictMonoOn (deriv f) (Icc a b) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hdcont
      (fun x hx => (heε (hnear x (interior_subset hx))).1)
  have hm : StrictMonoOn f (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
    intro x hx
    have hx' : x ∈ Ioo a b := by simpa [interior_Icc] using hx
    have hh := hdm ⟨le_rfl, hab.le⟩ ⟨hx'.1.le, hx'.2.le⟩ hx'.1
    rw [ha.deriv_eq_zero] at hh
    exact hh
  exact (not_lt_of_ge (heε (hnear b ⟨hab.le, le_rfl⟩)).2.1)
    (hm ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab)

/-- Actual second differentiation along an affine line, with local C² data. -/
lemma second_deriv_affine_line_comp_at {n : ℕ} {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : ContDiffAt ℝ 2 f x) (v : CoordinateSpace n) :
    deriv (deriv (fun t : ℝ => f (x + t • v))) 0 =
      fderiv ℝ (fderiv ℝ f) x v v := by
  have hl (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using (hasDerivAt_const t x).fun_add ((hasDerivAt_id t).smul_const v)
  have hline : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    simpa using (hl 0).continuousAt.tendsto
  have heq : deriv (fun t : ℝ => f (x + t • v)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => fderiv ℝ f (x + t • v) v) := by
    filter_upwards [hline.eventually (hf.eventually (by simp))] with t ht
    exact (ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hl t) |>.deriv
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  have hdf' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x)
      (x + (0 : ℝ) • v) := by simpa using hdf.hasFDerivAt
  have hB : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • v))
      (fderiv ℝ (fderiv ℝ f) x v) 0 := hdf'.comp_hasDerivAt 0 (hl 0)
  have hh' : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • v) v)
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    simpa using hB.clm_apply (hasDerivAt_const (0 : ℝ) v)
  exact (hh'.congr_of_eventuallyEq heq).deriv

/-- The actual local Hessian at a C² maximum is negative semidefinite. -/
theorem neg_hessian_posSemidef_of_isLocalMax_at {n : ℕ} {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : ContDiffAt ℝ 2 f x) (hx : IsLocalMax f x) :
    (-coordinateHessian f x).PosSemidef := by
  constructor
  · have hs := coordinateHessian_isSymm_at hf
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_eq_transpose_of_trivial] using congrArg Neg.neg hs.eq
  · intro v
    let F := fun t : ℝ => f (x + t • v)
    have hF : ContDiffAt ℝ 2 F 0 := by
      apply ContDiffAt.comp (f := fun t : ℝ => x + t • v)
      · simpa using hf
      · exact contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    have hFx : IsLocalMax F 0 := by
      have hc : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
      have hx' : ∀ᶠ y in 𝓝 (x + (0 : ℝ) • v), f y ≤ f x := by simpa using hx
      change ∀ᶠ t in 𝓝 (0 : ℝ), F t ≤ F 0
      simpa [F] using hc.tendsto.eventually hx'
    have hh := second_deriv_nonpos_of_isLocalMax_at hF hFx
    change deriv (deriv (fun t : ℝ => f (x + t • v))) 0 ≤ 0 at hh
    rw [second_deriv_affine_line_comp_at hf, secondFDeriv_eq_hessianQuadratic hf] at hh
    simpa only [star_trivial, Matrix.neg_mulVec, dotProduct_neg,
      matrixQuadratic, neg_nonneg] using hh

lemma coordinateDerivative_congr_nhds {n : ℕ} {f g : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (he : f =ᶠ[𝓝 x] g) (i : Fin n) :
    coordinateDerivative i f x = coordinateDerivative i g x := by
  unfold coordinateDerivative
  rw [he.fderiv_eq]

lemma coordinateDerivative_mul_at {n : ℕ} {f g : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (i : Fin n) :
    coordinateDerivative i (fun y => f y * g y) x =
      coordinateDerivative i f x * g x + f x * coordinateDerivative i g x := by
  unfold coordinateDerivative
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma coordinateDerivative_add_at {n : ℕ} {f g : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (i : Fin n) :
    coordinateDerivative i (fun y => f y + g y) x =
      coordinateDerivative i f x + coordinateDerivative i g x := by
  unfold coordinateDerivative
  rw [fderiv_fun_add hf hg]
  rfl

lemma coordinateDerivative_inv_at {n : ℕ} {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0)
    (i : Fin n) :
    coordinateDerivative i (fun y => (f y)⁻¹) x =
      -((f x)⁻¹ ^ 2) * coordinateDerivative i f x := by
  unfold coordinateDerivative
  have hd := ((hasDerivAt_inv hx).comp_hasFDerivAt x hf.hasFDerivAt).fderiv
  simp only [Function.comp_def] at hd
  rw [hd]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma coordinateDerivative_log_at {n : ℕ} {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0)
    (i : Fin n) :
    coordinateDerivative i (fun y => Real.log (f y)) x =
      (f x)⁻¹ * coordinateDerivative i f x := by
  unfold coordinateDerivative
  rw [hf.hasFDerivAt.log hx |>.fderiv]
  rfl

/-- The actual local Hessian chain rule for logarithms, including negative
arguments (real logarithms mean log absolute value). -/
lemma coordinateHessian_log_at {n : ℕ} {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : ContDiffAt ℝ 2 f x) (hx : f x ≠ 0)
    (i j : Fin n) :
    coordinateHessian (fun y => Real.log (f y)) x i j =
      coordinateHessian f x i j / f x -
        coordinateDerivative i f x * coordinateDerivative j f x / (f x) ^ 2 := by
  have he : coordinateDerivative i (fun y => Real.log (f y)) =ᶠ[𝓝 x]
      (fun y => (f y)⁻¹ * coordinateDerivative i f y) := by
    filter_upwards [hf.eventually (by simp), hf.continuousAt.eventually_ne hx] with y hy hfy
    exact coordinateDerivative_log_at (hy.differentiableAt (by norm_num)) hfy i
  change coordinateDerivative j (coordinateDerivative i (fun y => Real.log (f y))) x = _
  rw [coordinateDerivative_congr_nhds he j]
  rw [coordinateDerivative_mul_at (f := fun y => (f y)⁻¹)
    ((hf.differentiableAt (by norm_num)).inv hx)
    ((contDiffAt_coordinateDerivative hf (m := 1) (by norm_num) i).differentiableAt le_rfl)]
  rw [coordinateDerivative_inv_at (hf.differentiableAt (by norm_num)) hx]
  change -((f x)⁻¹ ^ 2) * coordinateDerivative j f x * coordinateDerivative i f x +
    (f x)⁻¹ * coordinateHessian f x i j = _
  ring

lemma coordinateHessian_add_at {n : ℕ} {f g : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    coordinateHessian (fun y => f y + g y) x = coordinateHessian f x + coordinateHessian g x := by
  ext i j
  have he : coordinateDerivative i (fun y => f y + g y) =ᶠ[𝓝 x]
      (fun y => coordinateDerivative i f y + coordinateDerivative i g y) := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hyf hyg
    exact coordinateDerivative_add_at (hyf.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) i
  change coordinateDerivative j (coordinateDerivative i (fun y => f y + g y)) x = _
  rw [coordinateDerivative_congr_nhds he j,
    coordinateDerivative_add_at
      ((contDiffAt_coordinateDerivative hf (m := 1) (by norm_num) i).differentiableAt le_rfl)
      ((contDiffAt_coordinateDerivative hg (m := 1) (by norm_num) i).differentiableAt le_rfl)]
  rfl

lemma coordinateDerivative_half_sq_at {n : ℕ} {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : DifferentiableAt ℝ f x) (i : Fin n) :
    coordinateDerivative i (fun y => (f y)^2 / 2) x =
      f x * coordinateDerivative i f x := by
  have hd : HasFDerivAt (fun y => (f y)^2 / 2) (f x • fderiv ℝ f x) x := by
    convert (hf.hasFDerivAt.pow 2).const_mul (1 / 2 : ℝ) using 1
    · ext y; ring
    · ext y
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, pow_one]
      ring
  unfold coordinateDerivative
  rw [hd.fderiv]
  rfl

lemma coordinateHessian_half_sq_at {n : ℕ} {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : ContDiffAt ℝ 2 f x) (i j : Fin n) :
    coordinateHessian (fun y => (f y)^2 / 2) x i j =
      f x * coordinateHessian f x i j + coordinateDerivative i f x * coordinateDerivative j f x := by
  have he : coordinateDerivative i (fun y => (f y)^2 / 2) =ᶠ[𝓝 x]
      (fun y => f y * coordinateDerivative i f y) := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact coordinateDerivative_half_sq_at (hy.differentiableAt (by norm_num)) i
  change coordinateDerivative j (coordinateDerivative i (fun y => (f y)^2 / 2)) x = _
  rw [coordinateDerivative_congr_nhds he j,
    coordinateDerivative_mul_at (hf.differentiableAt (by norm_num))
      ((contDiffAt_coordinateDerivative hf (m := 1) (by norm_num) i).differentiableAt le_rfl)]
  change coordinateDerivative j f x * coordinateDerivative i f x + f x * coordinateHessian f x i j = _
  ring

end GaussianTilt.MomentMapRegularity
