import GaussianTilt.MomentMapSchauderEllipticity

/-!
# Uniform ellipticity derived on compact subsets

Positive definite continuous matrix fields are uniformly elliptic on every
compact subset. The lower bound is the attained positive minimum over the
Euclidean unit sphere, and the upper bound follows from compactness.
-/
noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix quadratic form evaluated in the Euclidean normed model. -/
def euclideanQuadratic (A : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) : ℝ :=
  v.ofLp ⬝ᵥ (A *ᵥ v.ofLp)

lemma euclideanQuadratic_smul (A : Matrix ι ι ℝ) (c : ℝ) (v : EuclideanSpace ℝ ι) :
    euclideanQuadratic A (c • v) = c ^ 2 * euclideanQuadratic A v := by
  change (c • v.ofLp) ⬝ᵥ (A *ᵥ (c • v.ofLp)) = _
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  change c * (c * euclideanQuadratic A v) = _
  ring

@[simp] lemma euclideanQuadratic_zero (A : Matrix ι ι ℝ) : euclideanQuadratic A 0 = 0 := by
  simp [euclideanQuadratic]

lemma euclideanQuadratic_pos {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {v : EuclideanSpace ℝ ι} (hv : v ≠ 0) : 0 < euclideanQuadratic A v := by
  have hv' : v.ofLp ≠ 0 := by simpa only [WithLp.ofLp_eq_zero] using hv
  simpa only [euclideanQuadratic, star_trivial] using hA.2 v.ofLp hv'

lemma continuous_euclideanQuadratic :
    Continuous (fun p : Matrix ι ι ℝ × EuclideanSpace ℝ ι => euclideanQuadratic p.1 p.2) := by
  have hv : Continuous (fun p : Matrix ι ι ℝ × EuclideanSpace ℝ ι => p.2.ofLp) :=
    (PiLp.continuous_ofLp 2 (fun _ : ι => ℝ)).comp continuous_snd
  exact hv.dotProduct (continuous_fst.matrix_mulVec hv)

/-- Uniform two-sided Euclidean quadratic-form bounds are derived from
compactness and pointwise positive definiteness. No quantitative ellipticity
is assumed. The statement includes empty sets and zero-dimensional spaces. -/
theorem exists_uniform_ellipticity_on_compact {X : Type*} [TopologicalSpace X]
    {H : X → Matrix ι ι ℝ} {S : Set X}
    (hS : IsCompact S) (hH : ContinuousOn H S) (hpos : ∀ x ∈ S, (H x).PosDef) :
    ∃ lam Λ : ℝ, 0 < lam ∧ 0 < Λ ∧ ∀ x ∈ S, ∀ v : EuclideanSpace ℝ ι,
      lam * ‖v‖ ^ 2 ≤ euclideanQuadratic (H x) v ∧
        euclideanQuadratic (H x) v ≤ Λ * ‖v‖ ^ 2 := by
  let T : Set (X × EuclideanSpace ℝ ι) := S ×ˢ Metric.sphere 0 1
  have hT : IsCompact T := hS.prod (isCompact_sphere _ _)
  let q : X × EuclideanSpace ℝ ι → ℝ := fun p => euclideanQuadratic (H p.1) p.2
  have hq : ContinuousOn q T := by
    have hp : ContinuousOn (fun p : X × EuclideanSpace ℝ ι => (H p.1, p.2)) T :=
      (hH.comp continuous_fst.continuousOn (fun _ hp => hp.1)).prodMk
        continuous_snd.continuousOn
    exact continuous_euclideanQuadratic.comp_continuousOn hp
  have hqp : ∀ p ∈ T, 0 < q p := by
    intro p hp
    apply euclideanQuadratic_pos (hpos p.1 hp.1)
    intro hz
    have hs := hp.2
    simp [hz] at hs
  obtain ⟨lam, hlam, hlower⟩ : ∃ lam : ℝ, 0 < lam ∧ ∀ p ∈ T, lam ≤ q p := by
    by_cases hne : T.Nonempty
    · obtain ⟨p, hp, hmin⟩ := hT.exists_isMinOn hne hq
      exact ⟨q p, hqp p hp, fun y hy => hmin hy⟩
    · refine ⟨1, by norm_num, ?_⟩
      intro p hp
      exact (hne ⟨p, hp⟩).elim
  obtain ⟨M, hM⟩ := hT.exists_bound_of_continuousOn hq
  let Λ : ℝ := max M 1
  have hΛ : 0 < Λ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨lam, Λ, hlam, hΛ, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · simp [hv]
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : EuclideanSpace ℝ ι := ‖v‖⁻¹ • v
  have hw : w ∈ Metric.sphere (0 : EuclideanSpace ℝ ι) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvnorm), inv_mul_cancel₀ hvnorm.ne']
  have hvw : ‖v‖ • w = v := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ hvnorm.ne', one_smul]
  have hquad : euclideanQuadratic (H x) v = ‖v‖ ^ 2 * q (x, w) := by
    conv_lhs => rw [← hvw]
    exact euclideanQuadratic_smul (H x) ‖v‖ w
  have hlo := hlower (x, w) ⟨hx, hw⟩
  have hhi : q (x, w) ≤ Λ := by
    exact (le_abs_self _).trans ((hM (x, w) ⟨hx, hw⟩).trans (le_max_left _ _))
  rw [hquad]
  constructor
  · nlinarith [sq_nonneg ‖v‖]
  · nlinarith [sq_nonneg ‖v‖]

/-- The same ellipticity constants control all genuine averaged inverse
coefficients whose two Hessian endpoints lie in one compact source set.
In particular the constants are independent of a sufficiently small
finite-difference step. -/
theorem exists_uniform_ellipticity_averagedInverse_on_compact
    {X : Type*} [TopologicalSpace X] {H : X → Matrix ι ι ℝ} {S : Set X}
    (hS : IsCompact S) (hH : ContinuousOn H S) (hpos : ∀ x ∈ S, (H x).PosDef) :
    ∃ lam Λ : ℝ, 0 < lam ∧ 0 < Λ ∧ ∀ x ∈ S, ∀ y ∈ S,
      ∀ v : EuclideanSpace ℝ ι,
        lam * ‖v‖ ^ 2 ≤ euclideanQuadratic (averagedInverse (H x) (H y)) v ∧
          euclideanQuadratic (averagedInverse (H x) (H y)) v ≤ Λ * ‖v‖ ^ 2 := by
  let T : Set (X × X × ℝ) := S ×ˢ (S ×ˢ Icc (0 : ℝ) 1)
  have hT : IsCompact T := hS.prod (hS.prod isCompact_Icc)
  let F : X × X × ℝ → Matrix ι ι ℝ := fun p => matrixSegment (H p.1) (H p.2.1) p.2.2
  have hF : ContinuousOn F T := by
    have hx : ContinuousOn (fun p : X × X × ℝ => H p.1) T :=
      hH.comp continuous_fst.continuousOn (fun _ hp => hp.1)
    have hy : ContinuousOn (fun p : X × X × ℝ => H p.2.1) T :=
      hH.comp (continuous_fst.comp continuous_snd).continuousOn (fun _ hp => hp.2.1)
    exact (continuousOn_const.sub (continuous_snd.comp continuous_snd).continuousOn).smul hx |>.add
      ((continuous_snd.comp continuous_snd).continuousOn.smul hy)
  have hi : ContinuousOn (fun p => (F p)⁻¹) T := by
    intro p hp
    apply ContinuousAt.comp_continuousWithinAt _ (hF p hp)
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀
      (matrixSegment_posDef (hpos p.1 hp.1) (hpos p.2.1 hp.2.1) hp.2.2).det_pos.ne'
  obtain ⟨lam, Λ, hlam, hΛ, hbound⟩ := exists_uniform_ellipticity_on_compact hT hi
    (fun p hp => (matrixSegment_posDef (hpos p.1 hp.1) (hpos p.2.1 hp.2.1) hp.2.2).inv)
  refine ⟨lam, Λ, hlam, hΛ, ?_⟩
  intro x hx y hy v
  have hc : ContinuousOn
      (fun t => euclideanQuadratic ((matrixSegment (H x) (H y) t)⁻¹) v) (Icc (0 : ℝ) 1) := by
    have hp : ContinuousOn
        (fun t => ((matrixSegment (H x) (H y) t)⁻¹, v)) (Icc (0 : ℝ) 1) :=
      (continuousOn_inv_matrixSegment (hpos x hx) (hpos y hy)).prodMk continuousOn_const
    exact continuous_euclideanQuadratic.comp_continuousOn hp
  have hint := hc.intervalIntegrable_of_Icc (μ := volume) (show (0 : ℝ) ≤ 1 by norm_num)
  have hlow := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => lam * ‖v‖ ^ 2) volume 0 1)
    hint (fun t ht => (hbound (x, y, t) ⟨hx, hy, ht⟩ v).1)
  have hhigh := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num) hint
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Λ * ‖v‖ ^ 2) volume 0 1)
    (fun t ht => (hbound (x, y, t) ⟨hx, hy, ht⟩ v).2)
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hlow hhigh
  have he : euclideanQuadratic (averagedInverse (H x) (H y)) v =
      ∫ t in (0 : ℝ)..1, euclideanQuadratic ((matrixSegment (H x) (H y) t)⁻¹) v :=
    quadraticForm_averagedInverse_eq_integral (hpos x hx) (hpos y hy) v.ofLp
  rw [he]
  exact ⟨hlow, hhigh⟩

end GaussianTilt.MomentMapSchauder
