import GaussianTilt.Prekopa

/-!
# Strong convexity survives one-coordinate marginalization

The integral marginal theorem here is derived from the proved one-dimensional
Prékopa–Leindler theorem. Every slice integral and its strict positivity are
proved from the original strong convexity, using Gaussian domination.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace GaussianTilt.StrongMarginal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The potential of the actual unnormalized one-coordinate integral. -/
def potential (W : E × ℝ → ℝ) (x : E) : ℝ :=
  -Real.log (∫ u : ℝ, Real.exp (-W (x, u)))

lemma convexOn_slice {W : E × ℝ → ℝ} {κ : ℝ} {q : E → ℝ}
    (hc : ConvexOn ℝ univ (fun p ↦ W p - κ / 2 * (q p.1 + p.2 ^ 2))) (x : E) :
    ConvexOn ℝ univ (fun u : ℝ ↦ W (x, u) - κ / 2 * u ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ α β hα hβ hαβ
  have hx : α • x + β • x = x := by rw [← add_smul, hαβ, one_smul]
  have h := hc.2 (mem_univ (x, u)) (mem_univ (x, v)) hα hβ hαβ
  simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.fst, Prod.snd, smul_eq_mul, hx] at h ⊢
  linear_combination h - (κ / 2 * q x) * hαβ

lemma integrable_slice {W : E × ℝ → ℝ} {κ : ℝ} {q : E → ℝ} (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun p ↦ W p - κ / 2 * (q p.1 + p.2 ^ 2))) (x : E) :
    Integrable (fun u : ℝ ↦ Real.exp (-W (x, u))) := by
  simpa only [pow_zero, one_mul, BrascampLieb.weight] using
    BrascampLieb.integrable_pow_mul_weight hκ (convexOn_slice hc x) 0

lemma integral_slice_pos {W : E × ℝ → ℝ} {κ : ℝ} {q : E → ℝ} (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun p ↦ W p - κ / 2 * (q p.1 + p.2 ^ 2))) (x : E) :
    0 < ∫ u : ℝ, Real.exp (-W (x, u)) := integral_exp_pos (integrable_slice hκ hc x)

lemma residual_density_logconcave {W : E × ℝ → ℝ} {κ : ℝ} {q : E → ℝ} (hκ : 0 ≤ κ)
    (hc : ConvexOn ℝ univ (fun p ↦ W p - κ / 2 * (q p.1 + p.2 ^ 2))) :
    ∀ x y : E, ∀ u v α β : ℝ, 0 ≤ α → 0 ≤ β → α + β = 1 →
      Real.exp (-W (x, u) + κ / 2 * q x) ^ α *
          Real.exp (-W (y, v) + κ / 2 * q y) ^ β ≤
        Real.exp (-W (α • x + β • y, α * u + β * v) + κ / 2 * q (α • x + β • y)) := by
  intro x y u v α β hα hβ hαβ
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := hc.2 (mem_univ (x, u)) (mem_univ (y, v)) hα hβ hαβ
  simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.fst, Prod.snd, smul_eq_mul] at h
  have hsq : (α * u + β * v) ^ 2 ≤ α * u ^ 2 + β * v ^ 2 :=
    (even_two.convexOn_pow (𝕜 := ℝ)).2 (mem_univ u) (mem_univ v) hα hβ hαβ
  have hsq' := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ κ / 2)
  nlinarith

lemma convexOn_neg_log_of_logconcave {f : E → ℝ} (hp : ∀ x, 0 < f x)
    (hc : ∀ x y : E, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → α + β = 1 →
      f x ^ α * f y ^ β ≤ f (α • x + β • y)) :
    ConvexOn ℝ univ (fun x ↦ -Real.log (f x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ α β hα hβ hαβ
  have h := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos (hp x) α)
    (Real.rpow_pos_of_pos (hp y) β)) (hc x y α β hα hβ hαβ)
  rw [Real.log_mul (Real.rpow_pos_of_pos (hp x) α).ne' (Real.rpow_pos_of_pos (hp y) β).ne',
    Real.log_rpow (hp x), Real.log_rpow (hp y)] at h
  simp only [smul_eq_mul]
  linarith

/-- A genuine strongly convex marginal-potential theorem for finite continuous
potentials. The same curvature constant survives integration of one variable. -/
theorem convexOn_marginal_residual {W : E × ℝ → ℝ} {κ : ℝ} {q : E → ℝ} (hκ : 0 < κ)
    (hW : Continuous W) (hq : Continuous q)
    (hc : ConvexOn ℝ univ (fun p ↦ W p - κ / 2 * (q p.1 + p.2 ^ 2))) :
    ConvexOn ℝ univ (fun x ↦ potential W x - κ / 2 * q x) := by
  let f : E × ℝ → ℝ := fun p ↦ Real.exp (-W p + κ / 2 * q p.1)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfp : ∀ p, 0 < f p := fun p ↦ Real.exp_pos _
  have he : ∀ x, (fun u ↦ f (x, u)) =
      (fun u ↦ Real.exp (κ / 2 * q x) * Real.exp (-W (x, u))) := by
    intro x
    funext u
    dsimp [f]
    rw [Real.exp_add, mul_comm]
  have hfi : ∀ x, Integrable (fun u ↦ f (x, u)) := by
    intro x
    rw [he x]
    exact (integrable_slice hκ hc x).const_mul _
  have hfm : ∀ x, 0 < ∫ u, f (x, u) := by
    intro x
    rw [he x, integral_const_mul]
    exact mul_pos (Real.exp_pos _) (integral_slice_pos hκ hc x)
  have hlc := Prekopa.marginal_logconcave hf hfp hfi (residual_density_logconcave hκ.le hc)
  have hconv := convexOn_neg_log_of_logconcave hfm hlc
  apply hconv.congr
  intro x _
  change -Real.log (∫ u, f (x, u)) = potential W x - κ / 2 * q x
  rw [he x, integral_const_mul, Real.log_mul (Real.exp_pos _).ne' (integral_slice_pos hκ hc x).ne',
    Real.log_exp]
  dsimp [potential]
  ring

end GaussianTilt.StrongMarginal
