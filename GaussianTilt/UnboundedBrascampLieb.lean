import GaussianTilt.BrascampLiebExhaustion

/-!
# Unbounded-support nonsmooth Brascamp–Lieb by convex exhaustion

The theorem permits arbitrary zero sets, hence extended-valued convex
potentials, and imposes no bounded-support or pre-existing moment hypotheses.
Compact convex cutoffs, a fixed inner mass, and Fatou's lemma derive the
moments required to pass the covariance inequality to the original density.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace GaussianTilt.LogConcaveMarginal

lemma IsLogConcave.indicator {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {f : E → ℝ} (hf : IsLogConcave f) {S : Set E} (hS : Convex ℝ S) :
    IsLogConcave (S.indicator f) := by
  classical
  have hn : ∀ x, 0 ≤ S.indicator f x := by intro x; by_cases hx : x ∈ S <;> simp [hx, hf.1 x]
  refine ⟨hn, ?_⟩
  intro x y α β hα hβ hαβ
  by_cases hα0 : α = 0
  · have hβ1 : β = 1 := by linarith
    simp [hα0, hβ1]
  by_cases hβ0 : β = 0
  · have hα1 : α = 1 := by linarith
    simp [hβ0, hα1]
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · simpa only [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem (hS hx hy hα hβ hαβ)] using hf.2 x y α β hα hβ hαβ
    · simpa only [indicator_of_notMem hy, Real.zero_rpow hβ0, mul_zero] using hn (α • x + β • y)
  · simpa only [indicator_of_notMem hx, Real.zero_rpow hα0, zero_mul] using hn (α • x + β • y)

lemma IsStronglyLogConcave.indicator {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {f q : E → ℝ} {κ : ℝ} (hf : IsStronglyLogConcave q κ f) {S : Set E} (hS : Convex ℝ S) :
    IsStronglyLogConcave q κ (S.indicator f) := by
  have h := IsLogConcave.indicator hf hS
  have he : S.indicator (fun x ↦ f x * Real.exp (κ / 2 * q x)) =
      (fun x ↦ S.indicator f x * Real.exp (κ / 2 * q x)) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  rwa [he] at h

end GaussianTilt.LogConcaveMarginal
namespace GaussianTilt.BrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- Concrete compact convex cutoffs. -/
def truncate (f : E → ℝ) (n : ℕ) : E → ℝ := (Metric.closedBall 0 (n : ℝ)).indicator f

lemma truncate_nonneg {f : E → ℝ} (hf : ∀ x, 0 ≤ f x) (n : ℕ) (x : E) : 0 ≤ truncate f n x := by
  classical
  by_cases hx : x ∈ Metric.closedBall 0 (n : ℝ) <;> simp [truncate, hx, hf x]

lemma truncate_le {f : E → ℝ} (hf : ∀ x, 0 ≤ f x) (n : ℕ) (x : E) : truncate f n x ≤ f x := by
  classical
  by_cases hx : x ∈ Metric.closedBall 0 (n : ℝ) <;> simp [truncate, hx, hf x]

lemma truncate_mono {f : E → ℝ} (hf : ∀ x, 0 ≤ f x) {m n : ℕ} (hmn : m ≤ n) (x : E) :
    truncate f m x ≤ truncate f n x := by
  classical
  have hsub : Metric.closedBall (0 : E) (m : ℝ) ⊆ Metric.closedBall 0 (n : ℝ) :=
    Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
  by_cases hx : x ∈ Metric.closedBall 0 (m : ℝ)
  · simp [truncate, hx, hsub hx]
  · simp only [truncate, indicator_of_notMem hx]
    exact truncate_nonneg hf n x

lemma truncate_eventually_eq (f : E → ℝ) (x : E) : ∀ᶠ n : ℕ in atTop, truncate f n x = f x := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have hx : x ∈ Metric.closedBall 0 (n : ℝ) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hN.le.trans (by exact_mod_cast hn)
  exact indicator_of_mem hx f

lemma truncate_tendsto (f : E → ℝ) (x : E) : Tendsto (fun n ↦ truncate f n x) atTop (𝓝 (f x)) := by
  have he : (fun n ↦ truncate f n x) =ᶠ[atTop] (fun _ ↦ f x) := truncate_eventually_eq f x
  exact tendsto_const_nhds.congr' he.symm

lemma integral_truncate_tendsto {f : E → ℝ} (hi : Integrable f μ) :
    Tendsto (fun n ↦ ∫ x, truncate f n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
    (fun n ↦ hi.aestronglyMeasurable.indicator Metric.isClosed_closedBall.measurableSet) hi.norm
  · intro n
    exact Filter.Eventually.of_forall (fun x ↦ by
      by_cases hx : x ∈ Metric.closedBall 0 (n : ℝ) <;> simp [truncate, hx])
  · exact Filter.Eventually.of_forall (truncate_tendsto f)

lemma mul_truncate (X f : E → ℝ) (n : ℕ) :
    (fun x ↦ X x * truncate f n x) = truncate (fun x ↦ X x * f x) n := by
  funext x
  by_cases hx : x ∈ Metric.closedBall 0 (n : ℝ) <;> simp [truncate, hx]

end GaussianTilt.BrascampLieb
namespace GaussianTilt.IteratedMarginal
open GaussianTilt.LogConcaveMarginal GaussianTilt.BrascampLieb

lemma strong_truncate {n : ℕ} {f : Space n → ℝ} {κ : ℝ}
    (hf : IsStronglyLogConcave energy κ f) (m : ℕ) :
    IsStronglyLogConcave energy κ (truncate f m) :=
  hf.indicator (convex_closedBall _ _)

lemma truncate_support {n : ℕ} (f : Space n → ℝ) (m : ℕ) :
    ∀ x, (m : ℝ) < ‖x‖ → truncate f m x = 0 := by
  intro x hx
  simp [truncate, Metric.mem_closedBall, dist_zero_right, not_le_of_gt hx]

lemma truncate_moment_integrable {n : ℕ} {f : Space n → ℝ} {κ : ℝ}
    (hκ : 0 ≤ κ) (hf : IsStronglyLogConcave energy κ f) (hm : Measurable f) (m k : ℕ) :
    Integrable (fun x ↦ coordinate x ^ k * truncate f m x) :=
  integrable_coordinate_pow_compact hκ (strong_truncate hf m)
    (hm.indicator Metric.isClosed_closedBall.measurableSet) (truncate_support f m) k

/-- The arbitrary-dimensional nonsmooth coordinate Brascamp–Lieb theorem
for unbounded-support densities. The sole integrability assumption is the
finite positive normalizing mass; first and second moments are conclusions. -/
theorem coordinate_variance_le_inv_of_integrable_density {n : ℕ} {f : Space n → ℝ} {κ : ℝ}
    (hκ : 0 < κ) (hf : IsStronglyLogConcave energy κ f) (hm : Measurable f)
    (hi : Integrable f) (hZ : 0 < ∫ x : Space n, f x) :
    Integrable (fun x ↦ coordinate x * f x) ∧ Integrable (fun x ↦ coordinate x ^ 2 * f x) ∧
    (∫ x : Space n, coordinate x ^ 2 * f x) / (∫ x : Space n, f x) -
      ((∫ x : Space n, coordinate x * f x) / (∫ x : Space n, f x)) ^ 2 ≤ κ⁻¹ := by
  have hfn : ∀ x, 0 ≤ f x := hf.nonneg
  have hi₀ : ∀ m, Integrable (truncate f m) := by
    intro m
    simpa only [pow_zero, one_mul] using truncate_moment_integrable hκ.le hf hm m 0
  have hi₁ : ∀ m, Integrable (fun x ↦ coordinate x * truncate f m x) := by
    intro m
    simpa only [pow_one] using truncate_moment_integrable hκ.le hf hm m 1
  have hi₂ : ∀ m, Integrable (fun x ↦ coordinate x ^ 2 * truncate f m x) :=
    fun m ↦ truncate_moment_integrable hκ.le hf hm m 2
  have hZlim := integral_truncate_tendsto hi
  have hZev : ∀ᶠ m : ℕ in atTop, 0 < ∫ x : Space n, truncate f m x :=
    hZlim.eventually (eventually_gt_nhds hZ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hZev
  have hNpos := hN N le_rfl
  have hv : ∀ m ≥ N,
      (∫ x, coordinate x ^ 2 * truncate f m x) / (∫ x, truncate f m x) -
        ((∫ x, coordinate x * truncate f m x) / (∫ x, truncate f m x)) ^ 2 ≤ κ⁻¹ := by
    intro m hmN
    exact compact_product_coordinate_variance_le_inv hκ (strong_truncate hf m)
      (hm.indicator Metric.isClosed_closedBall.measurableSet) (truncate_support f m) (hN m hmN)
  let C := (κ⁻¹ + 2 * (κ⁻¹ * (∫ x : Space n, f x) +
      ∫ x : Space n, coordinate x ^ 2 * truncate f N x) / (∫ x : Space n, truncate f N x)) * (∫ x : Space n, f x)
  have hC : ∀ᶠ m : ℕ in atTop, (∫ x : Space n, coordinate x ^ 2 * truncate f m x) ≤ C := by
    filter_upwards [eventually_ge_atTop N] with m hmN
    exact second_moment_bound_of_inner_density (hi₀ m) (hi₁ m) (hi₂ m) (hi₀ N) (hi₁ N) (hi₂ N)
      (truncate_nonneg hfn N) (truncate_mono hfn hmN) hNpos (inv_pos.mpr hκ).le
      (integral_mono (hi₀ m) hi (truncate_le hfn m)) (hv m hmN)
  have hi₂full : Integrable (fun x : Space n ↦ coordinate x ^ 2 * f x) := by
    apply integrable_of_nonneg_limit_bounded hi₂
      (fun m x ↦ mul_nonneg (sq_nonneg _) (truncate_nonneg hfn m x))
      (((continuous_coordinate n).measurable.pow_const 2).mul hm).aestronglyMeasurable
      (fun x ↦ mul_nonneg (sq_nonneg _) (hfn x)) ?_ hC
    intro x
    exact tendsto_const_nhds.mul (truncate_tendsto f x)
  have hi₁full : Integrable (fun x : Space n ↦ coordinate x * f x) := by
    apply (hi.add hi₂full).mono' (((continuous_coordinate n).measurable.mul hm).aestronglyMeasurable)
    filter_upwards [] with x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hfn x)]
    have hco : |coordinate x| ≤ 1 + coordinate x ^ 2 := by
      nlinarith [sq_nonneg (|coordinate x| - 1), sq_abs (coordinate x)]
    have h := mul_le_mul_of_nonneg_right hco (hfn x)
    simpa only [add_mul, one_mul, Pi.add_apply] using h
  have h₁lim := integral_truncate_tendsto hi₁full
  have h₂lim := integral_truncate_tendsto hi₂full
  simp only [← mul_truncate] at h₁lim h₂lim
  refine ⟨hi₁full, hi₂full, ?_⟩
  apply le_of_tendsto ((h₂lim.div hZlim hZ.ne').sub ((h₁lim.div hZlim hZ.ne').pow 2))
  filter_upwards [eventually_ge_atTop N] with m hmN
  exact hv m hmN

end GaussianTilt.IteratedMarginal
