import GaussianTilt.StrongMarginal

/-!
# Iterated strongly convex marginals in arbitrary finite dimension

`Space n` is a concrete product of `n + 1` copies of ℝ. The density in the
conclusion is obtained by actual successive Lebesgue integrations. The
curvature and moment bounds are proved by induction, with no marginal law
or functional inequality supplied as a hypothesis.
-/
noncomputable section
open MeasureTheory Set
namespace GaussianTilt.IteratedMarginal

/-- A distinguished coordinate and `n` coordinates to integrate out. -/
abbrev Space : ℕ → Type
  | 0 => ℝ
  | n + 1 => Space n × ℝ

instance spaceNormedAddCommGroup : (n : ℕ) → NormedAddCommGroup (Space n)
  | 0 => inferInstanceAs (NormedAddCommGroup ℝ)
  | n + 1 => by
    letI := spaceNormedAddCommGroup n
    exact inferInstanceAs (NormedAddCommGroup (Space n × ℝ))

instance spaceNormedSpace : (n : ℕ) → NormedSpace ℝ (Space n)
  | 0 => inferInstanceAs (NormedSpace ℝ ℝ)
  | n + 1 => by
    letI := spaceNormedSpace n
    exact inferInstanceAs (NormedSpace ℝ (Space n × ℝ))

instance spaceFiniteDimensional : (n : ℕ) → FiniteDimensional ℝ (Space n)
  | 0 => inferInstanceAs (FiniteDimensional ℝ ℝ)
  | n + 1 => by
    letI := spaceFiniteDimensional n
    exact inferInstanceAs (FiniteDimensional ℝ (Space n × ℝ))

instance spaceMeasureSpace : (n : ℕ) → MeasureSpace (Space n)
  | 0 => inferInstanceAs (MeasureSpace ℝ)
  | n + 1 => by
    letI := spaceMeasureSpace n
    exact inferInstanceAs (MeasureSpace (Space n × ℝ))

instance spaceBorelSpace : (n : ℕ) → BorelSpace (Space n)
  | 0 => inferInstanceAs (BorelSpace ℝ)
  | n + 1 => by
    letI := spaceBorelSpace n
    exact inferInstanceAs (BorelSpace (Space n × ℝ))

instance spaceSigmaFinite : (n : ℕ) → SigmaFinite (volume : Measure (Space n))
  | 0 => inferInstanceAs (SigmaFinite (volume : Measure ℝ))
  | n + 1 => by
    letI := spaceSigmaFinite n
    exact inferInstanceAs (SigmaFinite ((volume : Measure (Space n)).prod (volume : Measure ℝ)))

/-- Sum of coordinate squares, independent of the product's max norm. -/
def energy : {n : ℕ} → Space n → ℝ
  | 0, x => x ^ 2
  | n + 1, x => energy x.1 + x.2 ^ 2

lemma continuous_energy : ∀ n : ℕ, Continuous (@energy n)
  | 0 => by
    change Continuous (fun x : ℝ ↦ x ^ 2)
    exact continuous_id.pow 2
  | n + 1 => by
    change Continuous (fun x : Space n × ℝ ↦ energy x.1 + x.2 ^ 2)
    exact (continuous_energy n).comp continuous_fst |>.add (continuous_snd.pow 2)

/-- Repeated Lebesgue integration of every coordinate after the first. -/
def integrateOut : {n : ℕ} → (Space n → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => integrateOut (fun x : Space n ↦ ∫ u : ℝ, f (x, u))

/-- The corresponding recursive negative log-density. -/
def marginalPotential : {n : ℕ} → (Space n → ℝ) → ℝ → ℝ
  | 0, W => W
  | n + 1, W => marginalPotential (StrongMarginal.potential W)

lemma continuous_of_convex_residual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {W q : E → ℝ} {κ : ℝ} (hq : Continuous q)
    (hc : ConvexOn ℝ univ (fun x ↦ W x - κ / 2 * q x)) : Continuous W := by
  have hR := continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hc)
  convert hR.add (show Continuous (fun x : E ↦ κ / 2 * q x) from continuous_const.mul hq) using 1
  funext x
  ring

/-- Every marginal potential keeps the original curvature constant. -/
theorem convexOn_marginalPotential : ∀ {n : ℕ} {W : Space n → ℝ} {κ : ℝ}, 0 < κ →
    ConvexOn ℝ univ (fun x ↦ W x - κ / 2 * energy x) →
    ConvexOn ℝ univ (fun x ↦ marginalPotential W x - κ / 2 * x ^ 2)
  | 0, W, κ, hκ, hc => hc
  | n + 1, W, κ, hκ, hc => by
    have hW := continuous_of_convex_residual (continuous_energy (n + 1)) hc
    have hm := StrongMarginal.convexOn_marginal_residual hκ hW (continuous_energy n) hc
    exact convexOn_marginalPotential (n := n) hκ hm

/-- The negative-log construction agrees with the actual iterated integral. -/
theorem exp_marginalPotential : ∀ {n : ℕ} {W : Space n → ℝ} {κ : ℝ}, 0 < κ →
    ConvexOn ℝ univ (fun x ↦ W x - κ / 2 * energy x) →
    (fun x ↦ Real.exp (-marginalPotential W x)) =
      integrateOut (fun p ↦ Real.exp (-W p))
  | 0, W, κ, hκ, hc => rfl
  | n + 1, W, κ, hκ, hc => by
    have hW := continuous_of_convex_residual (continuous_energy (n + 1)) hc
    have hm := StrongMarginal.convexOn_marginal_residual hκ hW (continuous_energy n) hc
    change (fun x ↦ Real.exp (-marginalPotential (StrongMarginal.potential W) x)) = _
    rw [exp_marginalPotential (n := n) hκ hm]
    change integrateOut (fun x : Space n ↦ Real.exp (-StrongMarginal.potential W x)) = _
    congr 1
    funext x
    dsimp [StrongMarginal.potential]
    rw [neg_neg, Real.exp_log (StrongMarginal.integral_slice_pos hκ hc x)]

/-- The distinguished coordinate obeys the Brascamp–Lieb covariance bound
under the genuine iterated marginal of an arbitrary-dimensional finite
strongly convex potential. -/
theorem coordinate_variance_le_inv {n : ℕ} {W : Space n → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x ↦ W x - κ / 2 * energy x)) :
    let p := integrateOut (fun x ↦ Real.exp (-W x))
    (∫ x : ℝ, x ^ 2 * p x) / (∫ x : ℝ, p x) -
      ((∫ x : ℝ, x * p x) / (∫ x : ℝ, p x)) ^ 2 ≤ κ⁻¹ := by
  have h := BrascampLieb.fullVariance_le_inv hκ (convexOn_marginalPotential hκ hc)
  have he := congrFun (exp_marginalPotential hκ hc)
  simpa only [BrascampLieb.fullVariance, BrascampLieb.weight, he] using h


/-- The distinguished first coordinate. -/
def coordinate : {n : ℕ} → Space n → ℝ
  | 0, x => x
  | n + 1, x => coordinate x.1

lemma continuous_coordinate : ∀ n : ℕ, Continuous (@coordinate n)
  | 0 => continuous_id
  | n + 1 => (continuous_coordinate n).comp continuous_fst

/-- All powers of the distinguished coordinate are integrable under the
original product-Lebesgue density; Fubini is justified, not postulated. -/
theorem integrable_coordinate_pow : ∀ {n : ℕ} {W : Space n → ℝ} {κ : ℝ}, 0 < κ →
    ConvexOn ℝ univ (fun x ↦ W x - κ / 2 * energy x) → ∀ k : ℕ,
    Integrable (fun x ↦ coordinate x ^ k * Real.exp (-W x))
  | 0, W, κ, hκ, hc, k => BrascampLieb.integrable_pow_mul_weight hκ hc k
  | n + 1, W, κ, hκ, hc, k => by
    have hW := continuous_of_convex_residual (continuous_energy (n + 1)) hc
    have hm := StrongMarginal.convexOn_marginal_residual hκ hW (continuous_energy n) hc
    have hi := integrable_coordinate_pow (n := n) hκ hm k
    have he : ∀ x : Space n, Real.exp (-StrongMarginal.potential W x) = ∫ u : ℝ, Real.exp (-W (x, u)) := by
      intro x
      simp only [StrongMarginal.potential, neg_neg,
        Real.exp_log (StrongMarginal.integral_slice_pos hκ hc x)]
    change Integrable (fun x : Space n × ℝ ↦ coordinate x.1 ^ k * Real.exp (-W x))
      ((volume : Measure (Space n)).prod (volume : Measure ℝ))
    apply (integrable_prod_iff (Continuous.aestronglyMeasurable
      ((((continuous_coordinate n).comp continuous_fst).pow k).mul (Real.continuous_exp.comp hW.neg)))).mpr
    constructor
    · exact Filter.Eventually.of_forall (fun x ↦ (StrongMarginal.integrable_slice hκ hc x).const_mul (coordinate x ^ k))
    · convert hi.norm using 1
      funext x
      simp only [Function.comp_apply, Prod.fst, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), integral_const_mul, he x,
        abs_of_pos (StrongMarginal.integral_slice_pos hκ hc x)]

/-- Actual product-space moments equal the moments of the constructed
one-dimensional marginal. -/
theorem integral_coordinate_pow : ∀ {n : ℕ} {W : Space n → ℝ} {κ : ℝ}, 0 < κ →
    ConvexOn ℝ univ (fun x ↦ W x - κ / 2 * energy x) → ∀ k : ℕ,
    (∫ x : Space n, coordinate x ^ k * Real.exp (-W x)) =
      ∫ t : ℝ, t ^ k * integrateOut (fun x ↦ Real.exp (-W x)) t
  | 0, W, κ, hκ, hc, k => rfl
  | n + 1, W, κ, hκ, hc, k => by
    have hW := continuous_of_convex_residual (continuous_energy (n + 1)) hc
    have hm := StrongMarginal.convexOn_marginal_residual hκ hW (continuous_energy n) hc
    have he : ∀ x : Space n, Real.exp (-StrongMarginal.potential W x) = ∫ u : ℝ, Real.exp (-W (x, u)) := by
      intro x
      simp only [StrongMarginal.potential, neg_neg,
        Real.exp_log (StrongMarginal.integral_slice_pos hκ hc x)]
    change (∫ x : Space n × ℝ, coordinate x.1 ^ k * Real.exp (-W x)
      ∂((volume : Measure (Space n)).prod (volume : Measure ℝ))) = _
    have hprod := integral_prod (fun x : Space n × ℝ ↦ coordinate x.1 ^ k * Real.exp (-W x))
      (by simpa only [coordinate] using integrable_coordinate_pow hκ hc k)
    rw [hprod]
    simp_rw [integral_const_mul, ← he]
    rw [integral_coordinate_pow (n := n) hκ hm k]
    congr 1
    funext t
    congr 1
    change integrateOut (fun x : Space n ↦ Real.exp (-StrongMarginal.potential W x)) t =
      integrateOut (fun x : Space n ↦ ∫ u : ℝ, Real.exp (-W (x, u))) t
    simp_rw [he]

/-- Brascamp–Lieb for a coordinate of the original arbitrary-dimensional
product-Lebesgue probability density. All normalization integrals are actual
integrals of that density. -/
theorem product_coordinate_variance_le_inv {n : ℕ} {W : Space n → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x ↦ W x - κ / 2 * energy x)) :
    (∫ x : Space n, coordinate x ^ 2 * Real.exp (-W x)) / (∫ x : Space n, Real.exp (-W x)) -
      ((∫ x : Space n, coordinate x * Real.exp (-W x)) / (∫ x : Space n, Real.exp (-W x))) ^ 2 ≤ κ⁻¹ := by
  have h₀ := integral_coordinate_pow hκ hc 0
  have h₁ := integral_coordinate_pow hκ hc 1
  have h₂ := integral_coordinate_pow hκ hc 2
  simp only [pow_zero, one_mul] at h₀
  simp only [pow_one] at h₁
  rw [h₀, h₁, h₂]
  exact coordinate_variance_le_inv hκ hc

end GaussianTilt.IteratedMarginal
