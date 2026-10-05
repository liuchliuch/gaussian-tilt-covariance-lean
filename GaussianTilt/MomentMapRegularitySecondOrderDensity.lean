import GaussianTilt.MomentMapRegularityLocalizationDensity
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.MetricSpace.Holder

/-!
# The Hölder right-hand side for second-order Alexandrov regularity

The literal Alexandrov density is `exp (V (gradient φ x) - φ x)`.  Local
Hölder continuity of the gradient and local `C¹` regularity of the target
potential imply a local Hölder modulus for this density, with positive
upper and lower bounds.  These are prerequisites for the second-order
perturbation theorem; no second derivative or ellipticity is assumed here.

This file does not assert the Caffarelli second-order perturbation theorem
or a Schauder estimate.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- The exponential is Lipschitz on a half-line bounded above. -/
lemma abs_exp_sub_exp_le {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  let C : ℝ≥0 := ⟨Real.exp M, (Real.exp_pos M).le⟩
  have h : LipschitzOnWith C Real.exp (Iic M) :=
    (convex_Iic M).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (fun x hx => by
        change ‖Real.exp x‖ ≤ Real.exp M
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
        exact Real.exp_le_exp.mpr hx)
  simpa only [Real.dist_eq, C] using h.dist_le_mul a ha b hb

/-- A Lipschitz function has the same Hölder exponent as the gradient on
sets of diameter at most one. -/
lemma logDensity_holder_bound {φ V : E n → ℝ} {L B : ℝ≥0}
    (hφ : LipschitzWith L φ) {S T : Set (E n)}
    (hV : LipschitzOnWith B V T) (hgT : MapsTo (gradient φ) S T)
    {C α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hg : ∀ y ∈ S, ∀ z ∈ S,
      ‖gradient φ y - gradient φ z‖ ≤ C * ‖y - z‖ ^ α)
    {y z : E n} (hy : y ∈ S) (hz : z ∈ S) (hyz : ‖y - z‖ ≤ 1) :
    |(V (gradient φ y) - φ y) - (V (gradient φ z) - φ z)| ≤
      ((B : ℝ) * C + L) * ‖y - z‖ ^ α := by
  have hpow : ‖y - z‖ ≤ ‖y - z‖ ^ α := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (y - z)) hyz hα hα1
  have ht : |V (gradient φ y) - V (gradient φ z)| ≤
      (B : ℝ) * ‖gradient φ y - gradient φ z‖ := by
    simpa only [Real.dist_eq, dist_eq_norm] using hV.dist_le_mul _ (hgT hy) _ (hgT hz)
  have hs : |φ y - φ z| ≤ (L : ℝ) * ‖y - z‖ := by
    simpa only [Real.norm_eq_abs] using hφ.norm_sub_le y z
  calc
    _ = |(V (gradient φ y) - V (gradient φ z)) - (φ y - φ z)| := by congr 1; ring
    _ ≤ |V (gradient φ y) - V (gradient φ z)| + |φ y - φ z| := abs_sub _ _
    _ ≤ (B : ℝ) * (C * ‖y - z‖ ^ α) + (L : ℝ) * ‖y - z‖ ^ α :=
      add_le_add (ht.trans (mul_le_mul_of_nonneg_left (hg y hy z hz) B.coe_nonneg))
        (hs.trans (mul_le_mul_of_nonneg_left hpow L.coe_nonneg))
    _ = _ := by ring

/-- A quantitative Hölder estimate for the actual positive Monge--Ampère
density; all assumptions involve first-order data only. -/
lemma density_holder_bound {φ V : E n → ℝ} {L B : ℝ≥0}
    (hφ : LipschitzWith L φ) {S T : Set (E n)}
    (hV : LipschitzOnWith B V T) (hgT : MapsTo (gradient φ) S T)
    {C α M : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hg : ∀ y ∈ S, ∀ z ∈ S,
      ‖gradient φ y - gradient φ z‖ ≤ C * ‖y - z‖ ^ α)
    (hM : ∀ y ∈ S, V (gradient φ y) - φ y ≤ M)
    {y z : E n} (hy : y ∈ S) (hz : z ∈ S) (hyz : ‖y - z‖ ≤ 1) :
    |Real.exp (V (gradient φ y) - φ y) - Real.exp (V (gradient φ z) - φ z)| ≤
      (Real.exp M * ((B : ℝ) * C + L)) * ‖y - z‖ ^ α := by
  exact (abs_exp_sub_exp_le (hM y hy) (hM z hz)).trans
    (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (logDensity_holder_bound hφ hV hgT hα hα1 hg hy hz hyz) (Real.exp_pos M).le)

/-- The logarithm of the actual density is continuous when the source is
`C¹` and the target potential is continuous at all its actual gradients. -/
lemma continuous_logDensity {φ V : E n → ℝ} (hφ : Continuous φ)
    (hg : Continuous (gradient φ))
    (hV : ∀ x, ContinuousAt V (gradient φ x)) :
    Continuous (fun x => V (gradient φ x) - φ x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ((hV x).comp hg.continuousAt).sub hφ.continuousAt

/-- Compact source sets have positive two-sided pointwise bounds for the
literal density, without assuming bounds on the entire target boundary. -/
theorem density_bounds_on_compact {φ V : E n → ℝ} (hφ : Continuous φ)
    (hg : Continuous (gradient φ))
    (hV : ∀ x, ContinuousAt V (gradient φ x)) {S : Set (E n)} (hS : IsCompact S) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ S,
      c ≤ Real.exp (V (gradient φ x) - φ x) ∧
      Real.exp (V (gradient φ x) - φ x) ≤ C := by
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn
    (continuous_logDensity hφ hg hV).continuousOn
  refine ⟨Real.exp (-M), Real.exp M, Real.exp_pos _, Real.exp_pos _, ?_⟩
  intro x hx
  have hb : |V (gradient φ x) - φ x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x hx
  constructor <;> apply Real.exp_le_exp.mpr
  · linarith [neg_abs_le (V (gradient φ x) - φ x)]
  · exact (le_abs_self _).trans hb

/-- Local `C¹,α` source data give the locally positive Hölder density needed
by the second-order Alexandrov perturbation step.  The exponent is preserved.
Only local `C¹` regularity of `V` along the gradient image is used. -/
theorem local_holder_density_of_local_holder_gradient {φ V : E n → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (hg : Continuous (gradient φ))
    (hV : ∀ x, ContDiffAt ℝ 1 V (gradient φ x))
    (hgrad : ∀ x : E n, ∃ ε C α : ℝ, 0 < ε ∧ 0 < C ∧ 0 < α ∧ α ≤ 1 ∧
      ∀ y ∈ Metric.ball x ε, ∀ z ∈ Metric.ball x ε,
        ‖gradient φ y - gradient φ z‖ ≤ C * ‖y - z‖ ^ α) :
    ∀ x : E n, ∃ r c D H α : ℝ, 0 < r ∧ 0 < c ∧ 0 < D ∧ 0 < H ∧
      0 < α ∧ α ≤ 1 ∧
      (∀ y ∈ Metric.ball x r, c ≤ Real.exp (V (gradient φ y) - φ y) ∧
        Real.exp (V (gradient φ y) - φ y) ≤ D) ∧
      (∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball x r,
        |Real.exp (V (gradient φ y) - φ y) - Real.exp (V (gradient φ z) - φ z)| ≤
          H * ‖y - z‖ ^ α) := by
  intro x
  obtain ⟨ε, C, α, hε, hC, hα, hα1, hgrad⟩ := hgrad x
  obtain ⟨B, T, hT, hVT⟩ := (hV x).exists_lipschitzOnWith
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hg.continuousAt.preimage_mem_nhds hT)
  let r : ℝ := min ε (min δ (1 / 2))
  have hr : 0 < r := lt_min hε (lt_min hδ (by norm_num))
  have hrε : r ≤ ε := min_le_left _ _
  have hrδ : r ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hrhalf : r ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsubε : Metric.ball x r ⊆ Metric.ball x ε := Metric.ball_subset_ball hrε
  have hsubT : MapsTo (gradient φ) (Metric.ball x r) T :=
    fun _ hy => hδT (Metric.ball_subset_ball hrδ hy)
  have hlog := continuous_logDensity hφ.continuous hg (fun y => (hV y).continuousAt)
  obtain ⟨M, hM⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hlog.continuousOn
  have hMb (y : E n) (hy : y ∈ Metric.ball x r) : |V (gradient φ y) - φ y| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM y (Metric.ball_subset_closedBall hy)
  let H : ℝ := Real.exp M * ((B : ℝ) * C + L + 1)
  refine ⟨r, Real.exp (-M), Real.exp M, H, α, hr, Real.exp_pos _, Real.exp_pos _,
    ?_, hα, hα1, ?_, ?_⟩
  · dsimp [H]
    positivity
  · intro y hy
    constructor <;> apply Real.exp_le_exp.mpr
    · linarith [neg_abs_le (V (gradient φ y) - φ y), hMb y hy]
    · exact (le_abs_self _).trans (hMb y hy)
  · intro y hy z hz
    have hdist : ‖y - z‖ ≤ 1 := by
      have hy' := Metric.mem_ball.mp hy
      have hz' := Metric.mem_ball.mp hz
      have ht := dist_triangle y x z
      rw [dist_comm x z] at ht
      rw [dist_eq_norm] at ht
      linarith
    have hh := density_holder_bound hφ hVT hsubT hα.le hα1
      (fun y hy z hz => hgrad y (hsubε hy) z (hsubε hz))
      (fun y hy => (le_abs_self _).trans (hMb y hy)) hy hz hdist
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
    dsimp [H]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos M).le

/-- Pointwise bounds on the actual density give compact-set bounds for the
literal subgradient image.  The Monge--Ampère premise is the genuine
Alexandrov identity, rather than a classical determinant equation. -/
theorem subgradientImage_volume_bounds_of_density_bounds {φ V : E n → ℝ}
    (hid : ∀ A : Set (E n), IsCompact A →
      volume (subgradientImage φ A) =
        (volume.withDensity (fun x => ENNReal.ofReal
          (Real.exp (V (gradient φ x) - φ x)))) A)
    {A : Set (E n)} (hA : IsCompact A) {c C : ℝ}
    (hb : ∀ x ∈ A, c ≤ Real.exp (V (gradient φ x) - φ x) ∧
      Real.exp (V (gradient φ x) - φ x) ≤ C) :
    ENNReal.ofReal c * volume A ≤ volume (subgradientImage φ A) ∧
      volume (subgradientImage φ A) ≤ ENNReal.ofReal C * volume A := by
  rw [hid A hA]
  constructor
  · apply const_mul_le_withDensity_of_ae hA.measurableSet
    filter_upwards [ae_restrict_mem hA.measurableSet] with x hx
    exact ENNReal.ofReal_le_ofReal (hb x hx).1
  · apply withDensity_le_const_mul_of_ae hA.measurableSet
    filter_upwards [ae_restrict_mem hA.measurableSet] with x hx
    exact ENNReal.ofReal_le_ofReal (hb x hx).2

/-- On sufficiently small source balls, the actual Alexandrov measure is
an arbitrarily small relative perturbation of its frozen positive density.
This is obtained directly from the literal transport law, before any
classical Hessian or ellipticity has been established. -/
theorem local_alexandrov_frozen_density_bounds_of_transport {φ V : E n → ℝ}
    {L : ℝ≥0} (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hKc : Convex ℝ K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x)))
    (hg : Continuous (gradient φ)) (hgK : ∀ x, gradient φ x ∈ K)
    (x : E n) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ r : ℝ, 0 < r ∧
      0 < (1 - η) * Real.exp (V (gradient φ x) - φ x) ∧
      ∀ A : Set (E n), IsCompact A → A ⊆ Metric.ball x r →
        ENNReal.ofReal ((1 - η) * Real.exp (V (gradient φ x) - φ x)) * volume A ≤
          volume (subgradientImage φ A) ∧
        volume (subgradientImage φ A) ≤
          ENNReal.ofReal ((1 + η) * Real.exp (V (gradient φ x) - φ x)) * volume A := by
  let f : E n → ℝ := fun y => Real.exp (V (gradient φ y) - φ y)
  have hf : Continuous f := Real.continuous_exp.comp
    (continuous_logDensity hL.continuous hg
      (fun y => hV.continuousAt (hK.mem_nhds (hgK y))))
  have hfx : 0 < f x := Real.exp_pos _
  obtain ⟨r, hr, hrbound⟩ := Metric.continuousAt_iff.mp hf.continuousAt
    (η * f x) (mul_pos hη hfx)
  refine ⟨r, hr, mul_pos (sub_pos.mpr hη1) hfx, ?_⟩
  intro A hA hAr
  apply subgradientImage_volume_bounds_of_density_bounds
    (fun S hS => volume_subgradientImage_eq_mongeAmpere_density hL hc hK hKc hV hmap hS) hA
  intro y hy
  have hb : |f y - f x| < η * f x := by
    simpa only [Real.dist_eq] using hrbound (Metric.mem_ball.mp (hAr hy))
  change (1 - η) * f x ≤ f y ∧ f y ≤ (1 + η) * f x
  constructor <;> nlinarith [le_abs_self (f y - f x), neg_abs_le (f y - f x)]

end GaussianTilt.MomentMapRegularity
