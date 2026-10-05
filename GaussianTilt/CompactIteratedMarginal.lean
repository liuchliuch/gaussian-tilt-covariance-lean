import GaussianTilt.CompactStrongMarginal
import GaussianTilt.IteratedMarginal

/-!
# Arbitrary-dimensional compact nonsmooth Brascamp–Lieb

The density can vanish, so extended-valued convex potentials and hard convex
support boundaries are included. The proof integrates coordinates successively,
with measurability, support bounds, all moments, and Fubini justified internally.
-/
noncomputable section
open MeasureTheory Set Filter
open GaussianTilt.LogConcaveMarginal
namespace GaussianTilt.IteratedMarginal

lemma convexOn_energy : ∀ n : ℕ, ConvexOn ℝ univ (@energy n)
  | 0 => even_two.convexOn_pow
  | n + 1 => by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ α β hα hβ hαβ
    have h₁ := (convexOn_energy n).2 (mem_univ x.1) (mem_univ y.1) hα hβ hαβ
    have h₂ := (even_two.convexOn_pow (𝕜 := ℝ)).2 (mem_univ x.2) (mem_univ y.2) hα hβ hαβ
    change energy (α • x.1 + β • y.1) + (α * x.2 + β * y.2) ^ 2 ≤
      α * (energy x.1 + x.2 ^ 2) + β * (energy y.1 + y.2 ^ 2)
    simp only [smul_eq_mul] at h₁ h₂
    linarith

lemma bounded_slice_support {n : ℕ} {f : Space (n + 1) → ℝ} {R : ℝ}
    (hs : ∀ p, R < ‖p‖ → f p = 0) (x : Space n) :
    ∀ u ∉ Icc (-R) R, f (x, u) = 0 := by
  intro u hu
  have hr : R < ‖u‖ := by
    rw [Real.norm_eq_abs]
    exact lt_of_not_ge (fun h ↦ hu (abs_le.mp h))
  exact hs (x, u) (hr.trans_le (by exact le_max_right _ _))

lemma bounded_marginal_support {n : ℕ} {f : Space (n + 1) → ℝ} {R : ℝ}
    (hs : ∀ p, R < ‖p‖ → f p = 0) :
    ∀ x : Space n, R < ‖x‖ → (∫ u : ℝ, f (x, u)) = 0 := by
  intro x hx
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall (fun u ↦ hs (x, u) (hx.trans_le (by exact le_max_left _ _)))

lemma measurable_marginal {n : ℕ} {f : Space (n + 1) → ℝ} (hm : Measurable f) :
    Measurable (fun x : Space n ↦ ∫ u : ℝ, f (x, u)) :=
  (hm.stronglyMeasurable.integral_prod_right (f := fun x u ↦ f (x, u))).measurable

lemma strong_marginal {n : ℕ} {f : Space (n + 1) → ℝ} {κ R : ℝ}
    (hκ : 0 ≤ κ) (hf : IsStronglyLogConcave energy κ f) (hm : Measurable f)
    (hs : ∀ p, R < ‖p‖ → f p = 0) :
    IsStronglyLogConcave energy κ (fun x : Space n ↦ ∫ u : ℝ, f (x, u)) :=
  strong_marginal_of_compact_slices hκ hf (fun x ↦ hm.comp measurable_prod_mk_left)
    (fun x ↦ ⟨-R, R, bounded_slice_support hs x⟩)

/-- Measurability, compact support and curvature all survive the complete
marginalization, including densities with hard zero sets. -/
theorem compact_marginal_properties : ∀ {n : ℕ} {f : Space n → ℝ} {κ R : ℝ},
    0 ≤ κ → IsStronglyLogConcave energy κ f → Measurable f →
    (∀ p, R < ‖p‖ → f p = 0) →
    Measurable (integrateOut f) ∧ IsStronglyLogConcave (fun x : ℝ ↦ x ^ 2) κ (integrateOut f) ∧
      ∀ x : ℝ, R < ‖x‖ → integrateOut f x = 0
  | 0, f, κ, R, hκ, hf, hm, hs => ⟨hm, hf, hs⟩
  | n + 1, f, κ, R, hκ, hf, hm, hs =>
    compact_marginal_properties (n := n) hκ (strong_marginal hκ hf hm hs)
      (measurable_marginal hm) (bounded_marginal_support hs)

/-- Integrability of every coordinate power for a compact strongly
logconcave density. No smoothness or positivity on full space is required. -/
theorem integrable_coordinate_pow_compact : ∀ {n : ℕ} {f : Space n → ℝ} {κ R : ℝ},
    0 ≤ κ → IsStronglyLogConcave energy κ f → Measurable f →
    (∀ p, R < ‖p‖ → f p = 0) → ∀ k : ℕ, Integrable (fun x ↦ coordinate x ^ k * f x)
  | 0, f, κ, R, hκ, hf, hm, hs, k => by
    have hs' : ∀ x ∉ Icc (-R) R, f x = 0 := by
      intro x hx
      exact hs x (by rw [Real.norm_eq_abs]; exact lt_of_not_ge (fun h ↦ hx (abs_le.mp h)))
    have hi := integrable_of_compact_support (hf.logconcave_scalar hκ) hm ⟨-R, R, hs'⟩
    exact BrascampLieb.integrable_pow_mul_compact_density hi hs' k
  | n + 1, f, κ, R, hκ, hf, hm, hs, k => by
    have hM := strong_marginal hκ hf hm hs
    have hi := integrable_coordinate_pow_compact (n := n) hκ hM (measurable_marginal hm)
      (bounded_marginal_support hs) k
    have hfn : ∀ p, 0 ≤ f p := hf.nonneg
    have hlc := hf.logconcave hκ (convexOn_energy (n + 1))
    have hsi : ∀ x : Space n, Integrable (fun u : ℝ ↦ f (x, u)) := fun x ↦
      integrable_of_compact_support (logconcave_slice hlc x) (hm.comp measurable_prod_mk_left)
        ⟨-R, R, bounded_slice_support hs x⟩
    change Integrable (fun x : Space n × ℝ ↦ coordinate x.1 ^ k * f x)
      ((volume : Measure (Space n)).prod (volume : Measure ℝ))
    apply (integrable_prod_iff (((continuous_coordinate n).measurable.comp measurable_fst).pow_const k |>.mul hm |>.aestronglyMeasurable)).mpr
    constructor
    · exact Filter.Eventually.of_forall (fun x ↦ (hsi x).const_mul (coordinate x ^ k))
    · convert hi.norm using 1
      funext x
      have hMN : 0 ≤ ∫ u : ℝ, f (x, u) := MeasureTheory.integral_nonneg (fun u ↦ hfn (x, u))
      simp only [Function.comp_apply, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hfn _), integral_const_mul,
        abs_of_nonneg hMN]

/-- Fubini identifies the actual original moments with the iterated scalar
marginal, for compact nonsmooth strongly logconcave densities. -/
theorem integral_coordinate_pow_compact : ∀ {n : ℕ} {f : Space n → ℝ} {κ R : ℝ},
    0 ≤ κ → IsStronglyLogConcave energy κ f → Measurable f →
    (∀ p, R < ‖p‖ → f p = 0) → ∀ k : ℕ,
    (∫ x : Space n, coordinate x ^ k * f x) = ∫ t : ℝ, t ^ k * integrateOut f t
  | 0, f, κ, R, hκ, hf, hm, hs, k => rfl
  | n + 1, f, κ, R, hκ, hf, hm, hs, k => by
    have hM := strong_marginal hκ hf hm hs
    have hprod := integral_prod (fun x : Space n × ℝ ↦ coordinate x.1 ^ k * f x)
      (by simpa only [coordinate] using integrable_coordinate_pow_compact hκ hf hm hs k)
    change (∫ x : Space n × ℝ, coordinate x.1 ^ k * f x
      ∂((volume : Measure (Space n)).prod (volume : Measure ℝ))) = _
    rw [hprod]
    simp_rw [integral_const_mul]
    exact integral_coordinate_pow_compact (n := n) hκ hM (measurable_marginal hm)
      (bounded_marginal_support hs) k

/-- The compact nonsmooth arbitrary-dimensional coordinate covariance bound.
The density, including its zero set, is used unchanged in every integral. -/
theorem compact_product_coordinate_variance_le_inv {n : ℕ} {f : Space n → ℝ} {κ R : ℝ}
    (hκ : 0 < κ) (hf : IsStronglyLogConcave energy κ f) (hm : Measurable f)
    (hs : ∀ p, R < ‖p‖ → f p = 0) (hZ : 0 < ∫ x : Space n, f x) :
    (∫ x : Space n, coordinate x ^ 2 * f x) / (∫ x : Space n, f x) -
      ((∫ x : Space n, coordinate x * f x) / (∫ x : Space n, f x)) ^ 2 ≤ κ⁻¹ := by
  obtain ⟨hmm, hmf, hms⟩ := compact_marginal_properties hκ.le hf hm hs
  have h₀ := integral_coordinate_pow_compact hκ.le hf hm hs 0
  have h₁ := integral_coordinate_pow_compact hκ.le hf hm hs 1
  have h₂ := integral_coordinate_pow_compact hκ.le hf hm hs 2
  simp only [pow_zero, one_mul] at h₀
  simp only [pow_one] at h₁
  rw [h₀] at hZ
  rw [h₀, h₁, h₂]
  apply compact_strong_density_variance_le_inv hκ hmf hmm ?_ hZ
  refine ⟨-R, R, ?_⟩
  intro x hx
  exact hms x (by rw [Real.norm_eq_abs]; exact lt_of_not_ge (fun h ↦ hx (abs_le.mp h)))

end GaussianTilt.IteratedMarginal
