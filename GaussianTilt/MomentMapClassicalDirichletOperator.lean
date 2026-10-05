import GaussianTilt.MomentMapRegularityConstantDensityEquation
import GaussianTilt.MomentMapSchauderLinearization

/-!
# Actual linearized Dirichlet operators and maximum principles

The coefficients are actual positive definite matrices and the operator is
the trace of their product with the true Hessian. Local C² regularity is
sufficient for every maximum test. These are linear a priori estimates;
linear or nonlinear Dirichlet solvability is not assumed or asserted here.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateDerivative_const_mul_at {f : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : Fin n) :
    coordinateDerivative i (fun y => c * f y) x = c * coordinateDerivative i f x := by
  unfold coordinateDerivative
  rw [(hf.hasFDerivAt.const_mul c).fderiv]
  rfl

lemma coordinateHessian_const_mul_at {f : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : ContDiffAt ℝ 2 f x) (c : ℝ) :
    coordinateHessian (fun y => c * f y) x = c • coordinateHessian f x := by
  ext i j
  have he : coordinateDerivative i (fun y => c * f y) =ᶠ[𝓝 x]
      (fun y => c * coordinateDerivative i f y) := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact coordinateDerivative_const_mul_at (hy.differentiableAt (by norm_num)) c i
  change coordinateDerivative j (coordinateDerivative i (fun y => c * f y)) x = _
  rw [coordinateDerivative_congr_nhds he,
    coordinateDerivative_const_mul_at
      ((contDiffAt_coordinateDerivative hf (m := 1) (by norm_num) i).differentiableAt le_rfl)]
  rfl

lemma linearizedMA_const_mul_at (A : Matrix (Fin n) (Fin n) ℝ)
    {f : CoordinateSpace n → ℝ} {x : CoordinateSpace n} (hf : ContDiffAt ℝ 2 f x) (c : ℝ) :
    linearizedMA A (fun y => c * f y) x = c * linearizedMA A f x := by
  simp only [linearizedMA, coordinateHessian_const_mul_at hf c,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

lemma linearizedMA_const (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : CoordinateSpace n) :
    linearizedMA A (fun _ => c) x = 0 := by
  have hH : coordinateHessian (fun _ : CoordinateSpace n => c) x = 0 := by
    ext i j
    change coordinateDerivative j (coordinateDerivative i (fun _ : CoordinateSpace n => c)) x = 0
    have he : coordinateDerivative i (fun _ : CoordinateSpace n => c) = fun _ => 0 := by
      funext y
      simp [coordinateDerivative]
    rw [he]
    simp [coordinateDerivative]
  simp [linearizedMA, hH]

lemma coordinateDerivative_coordinate (i j : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => y j) x = if i = j then 1 else 0 := by
  unfold coordinateDerivative
  rw [(hasFDerivAt_apply j x).fderiv]
  simp [Pi.single_apply, eq_comm]

lemma coordinateHessian_coordinate (i : Fin n) (x : CoordinateSpace n) :
    coordinateHessian (fun y => y i) x = 0 := by
  ext a b
  change coordinateDerivative b (coordinateDerivative a (fun y => y i)) x = 0
  have he : coordinateDerivative a (fun y : CoordinateSpace n => y i) =
      fun _ => if a = i then 1 else 0 := funext (fun y => coordinateDerivative_coordinate a i y)
  rw [he]
  simp [coordinateDerivative]

lemma coordinateGradient_coordinate (i : Fin n) (x : CoordinateSpace n) :
    coordinateGradient (fun y => y i) x = Pi.single i 1 := by
  ext j
  simp [coordinateGradient, coordinateDerivative_coordinate, Pi.single_apply, eq_comm]

lemma linearizedMA_coordinate_half_sq (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (x : CoordinateSpace n) :
    linearizedMA A (fun y => (y i) ^ 2 / 2) x = A i i := by
  rw [linearizedMA_half_sq_at A (by fun_prop : ContDiffAt ℝ 2 (fun y : CoordinateSpace n => y i) x)]
  simp [linearizedMA, coordinateHessian_coordinate, coordinateGradient_coordinate,
    dotProduct, Matrix.mulVec, Pi.single_apply]

/-- Strictly positive linearized forcing prevents a positive interior
maximum. Coefficients need only be pointwise positive semidefinite. -/
theorem classical_dirichlet_strict_maximum_principle
    {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    {f : CoordinateSpace n → ℝ} (hfc : ContinuousOn f S)
    (hf : ∀ x ∈ interior S, ContDiffAt ℝ 2 f x)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ x ∈ interior S, (A x).PosSemidef)
    (hLf : ∀ x ∈ interior S, 0 < linearizedMA (A x) f x)
    (hb : ∀ x ∈ frontier S, f x ≤ 0) : ∀ x ∈ S, f x ≤ 0 := by
  intro x hx
  obtain ⟨y, hy, hmax⟩ := hS.exists_isMaxOn ⟨x, hx⟩ hfc
  apply (hmax hx).trans
  by_cases hyi : y ∈ interior S
  · have hm : IsLocalMax f y := hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hyi)
    exact False.elim ((hLf y hyi).not_ge (linearizedMA_nonpos_at_max (hA y hyi) (hf y hyi) hm))
  · exact hb y ⟨subset_closure hy, hyi⟩

/-- The actual non-strict maximum principle for a pointwise positive
elliptic Dirichlet operator. A small quadratic perturbation supplies strict
forcing; uniform ellipticity and coefficient regularity are not assumed. -/
theorem classical_dirichlet_maximum_principle [NeZero n]
    {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    {f : CoordinateSpace n → ℝ} (hfc : ContinuousOn f S)
    (hf : ∀ x ∈ interior S, ContDiffAt ℝ 2 f x)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ x ∈ interior S, (A x).PosDef)
    (hLf : ∀ x ∈ interior S, 0 ≤ linearizedMA (A x) f x)
    (hb : ∀ x ∈ frontier S, f x ≤ 0) : ∀ x ∈ S, f x ≤ 0 := by
  classical
  let i : Fin n := Classical.arbitrary (Fin n)
  let q : CoordinateSpace n → ℝ := fun y => (y i) ^ 2 / 2
  have hq : ContDiff ℝ 2 q := by fun_prop
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hq.continuous.continuousOn
  have hqB (x : CoordinateSpace n) (hx : x ∈ S) : q x ≤ B :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB x hx)
  intro x hx
  by_contra hnot
  have hpos : 0 < f x := lt_of_not_ge hnot
  have hc : ContinuousAt (fun ε : ℝ => f x + ε * (q x - B)) 0 := by fun_prop
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, 0 < f x + ε * (q x - B) :=
    hc.eventually (eventually_gt_nhds (by simpa using hpos))
  obtain ⟨ε, hε, hex⟩ := ((show ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin).and
    (nhdsWithin_le_nhds hev)).exists
  let g : CoordinateSpace n → ℝ := fun y => f y + ε * (q y - B)
  have hgc : ContinuousOn g S := hfc.add (continuous_const.mul (hq.continuous.sub continuous_const)).continuousOn
  have hgd (y : CoordinateSpace n) (hy : y ∈ interior S) : ContDiffAt ℝ 2 g y :=
    (hf y hy).add (contDiffAt_const.mul (hq.contDiffAt.sub contDiffAt_const))
  have hLb (y : CoordinateSpace n) (hy : y ∈ interior S) : 0 < linearizedMA (A y) g y := by
    rw [linearizedMA_add_at (A y) (hf y hy)
      (contDiffAt_const.mul (hq.contDiffAt.sub contDiffAt_const)),
      linearizedMA_const_mul_at (A y) (hq.contDiffAt.sub contDiffAt_const)]
    have hshift : linearizedMA (A y) (fun z => q z - B) y = A y i i := by
      rw [show (fun z => q z - B) = (fun z => q z + (-B)) from by ext z; ring,
        linearizedMA_add_at (A y) hq.contDiffAt contDiffAt_const, linearizedMA_const, add_zero]
      exact linearizedMA_coordinate_half_sq _ _ _
    rw [hshift]
    have hdiag : 0 < A y i i := by
      have h := (hA y hy).2 (Pi.single i (1 : ℝ)) (by simp)
      simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using h
    exact add_pos_of_nonneg_of_pos (hLf y hy) (mul_pos hε hdiag)
  have hgb (y : CoordinateSpace n) (hy : y ∈ frontier S) : g y ≤ 0 := by
    have hbound := hqB y (hS.isClosed.frontier_subset hy)
    have hboundary := hb y hy
    dsimp [g]
    nlinarith
  have hresult := classical_dirichlet_strict_maximum_principle hS hgc hgd
    (fun y hy => (hA y hy).posSemidef) hLb hgb x hx
  exact hex.not_ge hresult

/-- A genuine positive elliptic barrier controls the solution's sup norm.
This is the C⁰ inverse estimate used in linear Dirichlet continuation. -/
theorem classical_dirichlet_barrier_bound [NeZero n]
    {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    {f w : CoordinateSpace n → ℝ} (hfc : ContinuousOn f S) (hwc : ContinuousOn w S)
    (hf : ∀ x ∈ interior S, ContDiffAt ℝ 2 f x)
    (hw : ∀ x ∈ interior S, ContDiffAt ℝ 2 w x)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ x ∈ interior S, (A x).PosDef)
    {M : ℝ} (hM : 0 ≤ M)
    (hLf : ∀ x ∈ interior S, |linearizedMA (A x) f x| ≤ M)
    (hLw : ∀ x ∈ interior S, 1 ≤ linearizedMA (A x) w x)
    (hfb : ∀ x ∈ frontier S, f x = 0) (hwb : ∀ x ∈ frontier S, w x ≤ 0) :
    ∀ x ∈ S, |f x| ≤ -M * w x := by
  have hbound (s : ℝ) (hs : |s| ≤ 1) :
      ∀ x ∈ S, s * f x + M * w x ≤ 0 := by
    apply classical_dirichlet_maximum_principle hS
      ((continuousOn_const.mul hfc).add (continuousOn_const.mul hwc))
      (fun x hx => (contDiffAt_const.mul (hf x hx)).add (contDiffAt_const.mul (hw x hx))) hA
    · intro x hx
      rw [linearizedMA_add_at _ (contDiffAt_const.mul (hf x hx)) (contDiffAt_const.mul (hw x hx)),
        linearizedMA_const_mul_at _ (hf x hx), linearizedMA_const_mul_at _ (hw x hx)]
      have hp : |s * linearizedMA (A x) f x| ≤ M := by
        rw [abs_mul]
        calc
          |s| * |linearizedMA (A x) f x| ≤ 1 * M :=
            mul_le_mul hs (hLf x hx) (abs_nonneg _) zero_le_one
          _ = M := one_mul _
      nlinarith [neg_abs_le (s * linearizedMA (A x) f x), hLw x hx]
    · intro x hx
      rw [hfb x hx, mul_zero, zero_add]
      exact mul_nonpos_of_nonneg_of_nonpos hM (hwb x hx)
  intro x hx
  have hplus := hbound 1 (by norm_num) x hx
  have hminus := hbound (-1) (by norm_num) x hx
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The actual homogeneous linear Dirichlet problem is injective. This is
one part of a later solvability theorem, not a surjectivity assumption. -/
theorem classical_dirichlet_linear_unique [NeZero n]
    {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    {f : CoordinateSpace n → ℝ} (hfc : ContinuousOn f S)
    (hf : ∀ x ∈ interior S, ContDiffAt ℝ 2 f x)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ x ∈ interior S, (A x).PosDef)
    (hLf : ∀ x ∈ interior S, linearizedMA (A x) f x = 0)
    (hb : ∀ x ∈ frontier S, f x = 0) : ∀ x ∈ S, f x = 0 := by
  have hplus := classical_dirichlet_maximum_principle hS hfc hf hA
    (fun x hx => (hLf x hx).ge) (fun x hx => (hb x hx).le)
  have hminus := classical_dirichlet_maximum_principle (f := fun x => (-1 : ℝ) * f x) hS (continuousOn_const.mul hfc)
    (fun x hx => contDiffAt_const.mul (hf x hx)) hA
    (fun x hx => by rw [linearizedMA_const_mul_at _ (hf x hx), hLf x hx, mul_zero])
    (fun x hx => by simp [hb x hx])
  intro x hx
  have hm : (-1 : ℝ) * f x ≤ 0 := hminus x hx
  linarith [hplus x hx]

lemma coordinateHessian_sub_at {f g : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    coordinateHessian (fun y => f y - g y) x = coordinateHessian f x - coordinateHessian g x := by
  rw [show (fun y => f y - g y) = (fun y => f y + (-1) * g y) from by ext y; ring,
    coordinateHessian_add_at hf (contDiffAt_const.mul hg), coordinateHessian_const_mul_at hg]
  simp only [neg_one_smul, sub_eq_add_neg]

/-- Classical Monge--Ampère comparison is deduced from the true log-det
tangent inequality and the proved elliptic maximum principle. -/
theorem classical_dirichlet_mongeAmpere_comparison [NeZero n]
    {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    {u v : CoordinateSpace n → ℝ} (huc : ContinuousOn u S) (hvc : ContinuousOn v S)
    (hu : ∀ x ∈ interior S, ContDiffAt ℝ 2 u x)
    (hv : ∀ x ∈ interior S, ContDiffAt ℝ 2 v x)
    (huH : ∀ x ∈ interior S, (coordinateHessian u x).PosDef)
    (hvH : ∀ x ∈ interior S, (coordinateHessian v x).PosDef)
    (hdet : ∀ x ∈ interior S, (coordinateHessian v x).det ≤ (coordinateHessian u x).det)
    (hb : ∀ x ∈ frontier S, u x ≤ v x) : ∀ x ∈ S, u x ≤ v x := by
  have hLf (x : CoordinateSpace n) (hx : x ∈ interior S) :
      0 ≤ linearizedMA (coordinateHessian v x)⁻¹ (fun y => u y - v y) x := by
    have ht := log_det_tangent (hvH x hx) (huH x hx)
    have hlog := Real.log_le_log (hvH x hx).det_pos (hdet x hx)
    unfold linearizedMA
    rw [coordinateHessian_sub_at (hu x hx) (hv x hx), Matrix.mul_sub, Matrix.trace_sub,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hvH x hx).det_pos.ne'), Matrix.trace_one]
    simpa only [Fintype.card_fin] using (show
      0 ≤ ((coordinateHessian v x)⁻¹ * coordinateHessian u x).trace - Fintype.card (Fin n) by linarith)
  have hm := classical_dirichlet_maximum_principle hS (huc.sub hvc)
    (fun x hx => (hu x hx).sub (hv x hx)) (fun x hx => (hvH x hx).inv) hLf
    (fun x hx => sub_nonpos.mpr (hb x hx))
  exact fun x hx => sub_nonpos.mp (hm x hx)

end GaussianTilt.MomentMapRegularity
