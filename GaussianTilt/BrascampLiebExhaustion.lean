import GaussianTilt.CompactIteratedMarginal

/-!
# Moment control for exhaustion by compact strongly logconcave densities

A fixed positive-mass inner truncation controls the means of all larger
truncations. The proved covariance bound then gives a uniform second-moment
bound. Fatou's lemma supplies actual moment existence in the unbounded limit.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.BrascampLieb

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma weighted_center_integrable {p X : Ω → ℝ}
    (h₀ : Integrable p μ) (h₁ : Integrable (fun x ↦ X x * p x) μ)
    (h₂ : Integrable (fun x ↦ X x ^ 2 * p x) μ) (m : ℝ) :
    Integrable (fun x ↦ (X x - m) ^ 2 * p x) μ := by
  convert (h₂.sub (h₁.const_mul (2 * m))).add (h₀.const_mul (m ^ 2)) using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

lemma weighted_center_integral {p X : Ω → ℝ}
    (h₀ : Integrable p μ) (h₁ : Integrable (fun x ↦ X x * p x) μ)
    (h₂ : Integrable (fun x ↦ X x ^ 2 * p x) μ) (m : ℝ) :
    (∫ x, (X x - m) ^ 2 * p x ∂μ) =
      (∫ x, X x ^ 2 * p x ∂μ) - 2 * m * (∫ x, X x * p x ∂μ) + m ^ 2 * (∫ x, p x ∂μ) := by
  have he : (fun x ↦ (X x - m) ^ 2 * p x) =
      (fun x ↦ X x ^ 2 * p x - (2 * m) * (X x * p x) + m ^ 2 * p x) := by funext x; ring
  rw [he, integral_add
    (show Integrable (fun x ↦ X x ^ 2 * p x - (2 * m) * (X x * p x)) μ from h₂.sub (h₁.const_mul _))
    (h₀.const_mul _), integral_sub h₂ (h₁.const_mul _), integral_const_mul, integral_const_mul]

/-- A common nonzero inner density prevents the means from escaping to
infinity. Consequently a variance bound gives uniform unnormalized second
moments, without assuming moments of the final unbounded law. -/
theorem second_moment_bound_of_inner_density {p q X : Ω → ℝ} {K Z : ℝ}
    (hp₀ : Integrable p μ) (hp₁ : Integrable (fun x ↦ X x * p x) μ)
    (hp₂ : Integrable (fun x ↦ X x ^ 2 * p x) μ)
    (hq₀ : Integrable q μ) (hq₁ : Integrable (fun x ↦ X x * q x) μ)
    (hq₂ : Integrable (fun x ↦ X x ^ 2 * q x) μ)
    (hqn : ∀ x, 0 ≤ q x) (hqp : ∀ x, q x ≤ p x) (hqmass : 0 < ∫ x, q x ∂μ)
    (hK : 0 ≤ K) (hZ : (∫ x, p x ∂μ) ≤ Z)
    (hvar : (∫ x, X x ^ 2 * p x ∂μ) / (∫ x, p x ∂μ) -
      ((∫ x, X x * p x ∂μ) / (∫ x, p x ∂μ)) ^ 2 ≤ K) :
    (∫ x, X x ^ 2 * p x ∂μ) ≤
      (K + 2 * (K * Z + ∫ x, X x ^ 2 * q x ∂μ) / (∫ x, q x ∂μ)) * Z := by
  let A := ∫ x, p x ∂μ
  let B := ∫ x, X x * p x ∂μ
  let C := ∫ x, X x ^ 2 * p x ∂μ
  let a := ∫ x, q x ∂μ
  let c := ∫ x, X x ^ 2 * q x ∂μ
  let m := B / A
  have ha : 0 < a := hqmass
  have haA : a ≤ A := integral_mono hq₀ hp₀ hqp
  have hA : 0 < A := ha.trans_le haA
  have hAZ : A ≤ Z := hZ
  have hZp : 0 ≤ Z := hA.le.trans hAZ
  have hmA : m * A = B := div_mul_cancel₀ _ hA.ne'
  have hcenter : (∫ x, (X x - m) ^ 2 * p x ∂μ) ≤ K * A := by
    rw [weighted_center_integral hp₀ hp₁ hp₂]
    have hv : C / A - m ^ 2 ≤ K := hvar
    have hv' := (div_le_iff₀ hA).mp (show C / A ≤ K + m ^ 2 by linarith)
    change C - 2 * m * B + m ^ 2 * A ≤ K * A
    rw [← hmA]
    nlinarith
  have hcenter_mono : (∫ x, (X x - m) ^ 2 * q x ∂μ) ≤ ∫ x, (X x - m) ^ 2 * p x ∂μ :=
    integral_mono (weighted_center_integrable hq₀ hq₁ hq₂ m)
      (weighted_center_integrable hp₀ hp₁ hp₂ m)
      (fun x ↦ mul_le_mul_of_nonneg_left (hqp x) (sq_nonneg _))
  have hlower : m ^ 2 / 2 * a ≤ (∫ x, (X x - m) ^ 2 * q x ∂μ) + c := by
    have hi := integral_mono (hq₀.const_mul (m ^ 2 / 2))
      ((weighted_center_integrable hq₀ hq₁ hq₂ m).add hq₂)
      (fun x ↦ by
        have hh := mul_le_mul_of_nonneg_right (show m ^ 2 / 2 ≤ (X x - m) ^ 2 + X x ^ 2 by nlinarith [sq_nonneg (2 * X x - m)]) (hqn x)
        simpa only [add_mul, Pi.add_apply] using hh)
    simp only [Pi.add_apply] at hi
    rw [integral_add (weighted_center_integrable hq₀ hq₁ hq₂ m) hq₂, integral_const_mul] at hi
    exact hi
  have hmBound : m ^ 2 ≤ 2 * (K * Z + c) / a := by
    apply (le_div_iff₀ ha).mpr
    have hKAZ := mul_le_mul_of_nonneg_left hAZ hK
    linarith [hcenter_mono, hcenter, hlower]
  have hC : C ≤ (K + m ^ 2) * A := by
    apply (div_le_iff₀ hA).mp
    change C / A ≤ K + m ^ 2
    linarith [hvar]
  change C ≤ (K + 2 * (K * Z + c) / a) * Z
  calc
    C ≤ (K + m ^ 2) * A := hC
    _ ≤ (K + m ^ 2) * Z := mul_le_mul_of_nonneg_left hAZ (add_nonneg hK (sq_nonneg _))
    _ ≤ (K + 2 * (K * Z + c) / a) * Z := mul_le_mul_of_nonneg_right (add_le_add_left hmBound K) hZp

/-- Fatou's lemma converts uniformly bounded actual nonnegative integrals
into integrability of the pointwise limit. -/
lemma integrable_of_nonneg_limit_bounded {F : ℕ → Ω → ℝ} {f : Ω → ℝ} {C : ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hFn : ∀ n x, 0 ≤ F n x)
    (hf : AEStronglyMeasurable f μ) (hfn : ∀ x, 0 ≤ f x)
    (hlim : ∀ x, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x)))
    (hb : ∀ᶠ n in atTop, (∫ x, F n x ∂μ) ≤ C) : Integrable f μ := by
  refine ⟨hf, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hfn)).mpr ?_⟩
  have hFatou := lintegral_liminf_le' (fun n ↦ (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have he : (fun x ↦ liminf (fun n ↦ ENNReal.ofReal (F n x)) atTop) = fun x ↦ ENNReal.ofReal (f x) := by
    funext x
    exact (ENNReal.tendsto_ofReal (hlim x)).liminf_eq
  rw [he] at hFatou
  have hbound : liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop ≤ ENNReal.ofReal C := by
    apply liminf_le_of_frequently_le (hu := ⟨0, Filter.Eventually.of_forall (fun n ↦ bot_le)⟩)
    apply Filter.Eventually.frequently
    filter_upwards [hb] with n hn
    rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Filter.Eventually.of_forall (hFn n))]
    exact ENNReal.ofReal_le_ofReal hn
  exact (hFatou.trans hbound).trans_lt ENNReal.ofReal_lt_top

end GaussianTilt.BrascampLieb
