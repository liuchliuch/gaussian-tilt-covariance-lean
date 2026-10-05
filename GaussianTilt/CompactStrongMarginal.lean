import GaussianTilt.LogConcaveMarginal

/-!
# Strong logconcavity and compact measurable marginals

The density formulation permits zero values and thus extended-valued
potentials. The one-coordinate preservation theorem derives all slice
integrability from the preceding compact Prékopa theorem.
-/
noncomputable section
open MeasureTheory Set
namespace GaussianTilt.LogConcaveMarginal

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

lemma IsLogConcave.mul {f g : E → ℝ} (hf : IsLogConcave f) (hg : IsLogConcave g) :
    IsLogConcave (fun x ↦ f x * g x) := by
  refine ⟨fun x ↦ mul_nonneg (hf.1 x) (hg.1 x), ?_⟩
  intro x y α β hα hβ hαβ
  rw [Real.mul_rpow (hf.1 x) (hg.1 x), Real.mul_rpow (hf.1 y) (hg.1 y)]
  calc
    (f x ^ α * g x ^ α) * (f y ^ β * g y ^ β) = (f x ^ α * f y ^ β) * (g x ^ α * g y ^ β) := by ring
    _ ≤ f (α • x + β • y) * g (α • x + β • y) :=
      mul_le_mul (hf.2 x y α β hα hβ hαβ) (hg.2 x y α β hα hβ hαβ)
        (mul_nonneg (Real.rpow_nonneg (hg.1 x) _) (Real.rpow_nonneg (hg.1 y) _)) (hf.1 _)

lemma gaussian_logconcave {κ : ℝ} (hκ : 0 ≤ κ) :
    IsLogConcave (fun u : ℝ ↦ Real.exp (-(κ / 2) * u ^ 2)) := by
  refine ⟨fun u ↦ (Real.exp_pos _).le, ?_⟩
  intro u v α β hα hβ hαβ
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := (even_two.convexOn_pow (𝕜 := ℝ)).2 (mem_univ u) (mem_univ v) hα hβ hαβ
  simp only [smul_eq_mul] at hs ⊢
  have h := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ κ / 2)
  nlinarith

/-- Strong logconcavity formulated directly on a density, allowing zeros. -/
def IsStronglyLogConcave (q : E → ℝ) (κ : ℝ) (f : E → ℝ) : Prop :=
  IsLogConcave (fun x ↦ f x * Real.exp (κ / 2 * q x))

lemma IsStronglyLogConcave.nonneg {q : E → ℝ} {κ : ℝ} {f : E → ℝ}
    (hf : IsStronglyLogConcave q κ f) (x : E) : 0 ≤ f x :=
  (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp (hf.1 x)

lemma IsStronglyLogConcave.logconcave_scalar {κ : ℝ} {f : ℝ → ℝ}
    (hf : IsStronglyLogConcave (fun x ↦ x ^ 2) κ f) (hκ : 0 ≤ κ) : IsLogConcave f := by
  have h := IsLogConcave.mul hf (gaussian_logconcave hκ)
  have he : (fun x ↦ (f x * Real.exp (κ / 2 * x ^ 2)) * Real.exp (-(κ / 2) * x ^ 2)) = f := by
    funext x
    rw [mul_assoc, ← Real.exp_add]
    simp
  rwa [he] at h

/-- The exact curvature is preserved when integrating a compact measurable
coordinate, even when the potential is extended-valued on its support boundary. -/
theorem strong_marginal_of_compact_slices {q : E → ℝ} {κ : ℝ} {f : E × ℝ → ℝ}
    (hκ : 0 ≤ κ) (hf : IsStronglyLogConcave (fun p ↦ q p.1 + p.2 ^ 2) κ f)
    (hm : ∀ x, Measurable (fun u : ℝ ↦ f (x, u)))
    (hs : ∀ x, ∃ A B : ℝ, ∀ u ∉ Icc A B, f (x, u) = 0) :
    IsStronglyLogConcave q κ (fun x ↦ ∫ u : ℝ, f (x, u)) := by
  have hg : IsLogConcave (fun p : E × ℝ ↦ Real.exp (-(κ / 2) * p.2 ^ 2)) := by
    refine ⟨fun p ↦ (Real.exp_pos _).le, ?_⟩
    intro x y α β hα hβ hαβ
    exact (gaussian_logconcave hκ).2 x.2 y.2 α β hα hβ hαβ
  have hprod := IsLogConcave.mul hf hg
  have he : (fun p : E × ℝ ↦ (f p * Real.exp (κ / 2 * (q p.1 + p.2 ^ 2))) *
      Real.exp (-(κ / 2) * p.2 ^ 2)) = (fun p ↦ f p * Real.exp (κ / 2 * q p.1)) := by
    funext p
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he] at hprod
  have hh := marginal_logconcave_of_measurable_compact_slices hprod
    (fun x ↦ by exact (hm x).mul (show Measurable (fun _ : ℝ ↦ Real.exp (κ / 2 * q x)) from measurable_const)) ?_
  · simpa only [integral_mul_const] using hh
  · intro x
    obtain ⟨A, B, hAB⟩ := hs x
    exact ⟨A, B, fun u hu ↦ by rw [hAB u hu, zero_mul]⟩

/-- Compact scalar Brascamp–Lieb in its measurable density formulation.
All analytic hypotheses other than measurability and strong logconcavity are
derived; the nonzero mass is the normalization condition. -/
theorem compact_strong_density_variance_le_inv {κ : ℝ} {f : ℝ → ℝ} (hκ : 0 < κ)
    (hf : IsStronglyLogConcave (fun x ↦ x ^ 2) κ f) (hm : Measurable f)
    (hs : ∃ A B : ℝ, ∀ x ∉ Icc A B, f x = 0) (hZ : 0 < ∫ x, f x) :
    (∫ x, x ^ 2 * f x) / (∫ x, f x) - ((∫ x, x * f x) / (∫ x, f x)) ^ 2 ≤ κ⁻¹ := by
  have hlc := hf.logconcave_scalar hκ.le
  have hi := integrable_of_compact_support hlc hm hs
  obtain ⟨a, b, hab, hp, hs', _⟩ := interval_support_of_integral_pos hlc hi hZ hs
  have hc := convexOn_neg_log hf (convex_Ioo a b)
    (fun x hx ↦ mul_pos (hp x hx) (Real.exp_pos _))
  have he : Set.EqOn (fun x ↦ -Real.log (f x * Real.exp (κ / 2 * x ^ 2)))
      (fun x ↦ -Real.log (f x) - κ / 2 * x ^ 2) (Ioo a b) := by
    intro x hx
    change -Real.log (f x * Real.exp (κ / 2 * x ^ 2)) = -Real.log (f x) - κ / 2 * x ^ 2
    rw [Real.log_mul (hp x hx).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  exact BrascampLieb.compact_density_variance_le_inv hab hκ hi (hf.nonneg) hp hs' (hc.congr he)


lemma gaussian_energy_logconcave {q : E → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hq : ConvexOn ℝ univ q) : IsLogConcave (fun x ↦ Real.exp (-(κ / 2) * q x)) := by
  refine ⟨fun x ↦ (Real.exp_pos _).le, ?_⟩
  intro x y α β hα hβ hαβ
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (hq.2 (mem_univ x) (mem_univ y) hα hβ hαβ)
    (by positivity : 0 ≤ κ / 2)
  simp only [smul_eq_mul] at h
  nlinarith

lemma IsStronglyLogConcave.logconcave {q : E → ℝ} {κ : ℝ} {f : E → ℝ}
    (hf : IsStronglyLogConcave q κ f) (hκ : 0 ≤ κ) (hq : ConvexOn ℝ univ q) : IsLogConcave f := by
  have h := IsLogConcave.mul hf (gaussian_energy_logconcave hκ hq)
  have he : (fun x ↦ (f x * Real.exp (κ / 2 * q x)) * Real.exp (-(κ / 2) * q x)) = f := by
    funext x
    rw [mul_assoc, ← Real.exp_add]
    simp
  rwa [he] at h

end GaussianTilt.LogConcaveMarginal
