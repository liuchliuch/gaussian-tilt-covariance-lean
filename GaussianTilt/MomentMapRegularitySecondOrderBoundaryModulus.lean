import GaussianTilt.MomentMapRegularitySecondOrderLocalMaximum
import Mathlib.Analysis.Convex.Continuous

/-! # Uniform boundary control for bounded Alexandrov mass -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- A continuous convex function with zero boundary values on a compact
domain is nonpositive. No convex extension outside the domain is used. -/
theorem convexOn_nonpos_of_zero_boundary [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) {u : E n → ℝ} (hu : ConvexOn ℝ S u) (huc : ContinuousOn u S)
    (hb : ∀ x ∈ frontier S, u x = 0) : ∀ x ∈ S, u x ≤ 0 := by
  intro x hx
  obtain ⟨z, hz, hmax⟩ := hS.exists_isMaxOn ⟨x, hx⟩ huc
  apply (hmax hx).trans
  by_cases hzi : z ∈ interior S
  · obtain ⟨y, hy⟩ := nonempty_frontier_iff.mpr ⟨⟨x, hx⟩, hS.ne_univ⟩
    have hc : ContinuousAt (fun t : ℝ => z + t • (z - y)) 0 := by fun_prop
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, z + t • (z - y) ∈ S := by
      have h := hc.preimage_mem_nhds (show S ∈ 𝓝 (z + (0 : ℝ) • (z - y)) by
        simpa using mem_interior_iff_mem_nhds.mp hzi)
      exact h
    obtain ⟨t, ht, htz⟩ := ((show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin).and
      (nhdsWithin_le_nhds hnear)).exists
    have htp : 0 < 1 + t := by linarith
    have hab : t / (1 + t) + 1 / (1 + t) = 1 := by field_simp; ring
    have he : (t / (1 + t)) • y + (1 / (1 + t)) • (z + t • (z - y)) = z := by
      ext i
      change (t / (1 + t)) * y i + (1 / (1 + t)) * (z i + t * (z i - y i)) = z i
      field_simp
      ring
    have hcv := hu.2 (hS.isClosed.frontier_subset hy) htz
      (div_nonneg ht.le htp.le) (div_nonneg zero_le_one htp.le) hab
    rw [he, hb y hy] at hcv
    simp only [smul_eq_mul, mul_zero, zero_add] at hcv
    have hzbound : u (z + t • (z - y)) ≤ u z := hmax htz
    have hh := mul_le_mul_of_nonneg_left hcv htp.le
    field_simp at hh
    nlinarith
  · exact (hb z ⟨subset_closure hz, hzi⟩).le

/-- The local-domain maximum principle in real-valued form under a finite
mass bound. This is the uniform boundary modulus for atomic Dirichlet data. -/
theorem alexandrovOn_boundary_power_bound [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) {u : E n → ℝ} (hu : ConvexOn ℝ S u) (huc : ContinuousOn u S)
    (hb : ∀ x ∈ frontier S, u x = 0) {M : ℝ} (hM : 0 ≤ M)
    (hmass : volume (subgradientImageOn S u (interior S)) ≤ ENNReal.ofReal M) :
    ∀ x ∈ S, |u x| ^ n ≤
      (2 * ((n : ℝ) + 1) ^ (n - 1) * Metric.diam S ^ (n - 1) * M) *
        Metric.infDist x (frontier S) := by
  intro x hx
  have hn := convexOn_nonpos_of_zero_boundary hS hu huc hb x hx
  have hcoef : 0 ≤ (2 * ((n : ℝ) + 1) ^ (n - 1) * Metric.diam S ^ (n - 1) * M) *
      Metric.infDist x (frontier S) := by
    have hd := Metric.infDist_nonneg (x := x) (s := frontier S)
    positivity
  by_cases hxi : x ∈ interior S
  · by_cases hu0 : u x = 0
    · simpa [hu0, zero_pow (NeZero.ne n)] using hcoef
    have hneg : u x < 0 := lt_of_le_of_ne hn hu0
    have h := alexandrovOn_maximum_principle huc hS hu.1 hxi hneg (fun y hy => (hb y hy).ge)
    have hc : 0 ≤ 2 * ((n : ℝ) + 1) ^ (n - 1) * Metric.infDist x (frontier S) *
        Metric.diam S ^ (n - 1) := by
      have hd := Metric.infDist_nonneg (x := x) (s := frontier S)
      positivity
    have hh := h.trans (mul_le_mul_left' hmass _)
    rw [← ENNReal.ofReal_mul hc] at hh
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    rw [ENNReal.toReal_ofReal (pow_nonneg (by linarith : 0 ≤ 0 - u x) _),
      ENNReal.toReal_ofReal (mul_nonneg hc hM)] at hreal
    rw [abs_of_nonpos hn]
    simpa only [zero_sub, mul_assoc, mul_left_comm, mul_comm] using hreal
  · have hz := hb x ⟨subset_closure hx, hxi⟩
    simpa [hz, zero_pow (NeZero.ne n)] using hcoef

/-- A common finite mass controls the sup norm uniformly. The deliberately
coarse constant avoids dimension-dependent roots. -/
theorem alexandrovOn_uniform_abs_bound [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) {u : E n → ℝ} (hu : ConvexOn ℝ S u) (huc : ContinuousOn u S)
    (hb : ∀ x ∈ frontier S, u x = 0) {M : ℝ} (hM : 0 ≤ M)
    (hmass : volume (subgradientImageOn S u (interior S)) ≤ ENNReal.ofReal M) :
    ∀ x ∈ S, |u x| ≤ 2 * ((n : ℝ) + 1) ^ (n - 1) * Metric.diam S ^ n * M + 1 := by
  intro x hx
  have hbound := alexandrovOn_boundary_power_bound hS hu huc hb hM hmass x hx
  obtain ⟨y, hy⟩ := nonempty_frontier_iff.mpr ⟨⟨x, hx⟩, hS.ne_univ⟩
  have hdist : Metric.infDist x (frontier S) ≤ Metric.diam S :=
    (Metric.infDist_le_dist_of_mem hy).trans
      (Metric.dist_le_diam_of_mem hS.isBounded hx (hS.isClosed.frontier_subset hy))
  have hd : Metric.diam S ^ n = Metric.diam S ^ (n - 1) * Metric.diam S := by
    have he : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
    calc
      Metric.diam S ^ n = Metric.diam S ^ (n - 1 + 1) := congrArg (fun k : ℕ => Metric.diam S ^ k) he.symm
      _ = _ := pow_succ _ _
  have hp : |u x| ^ n ≤ 2 * ((n : ℝ) + 1) ^ (n - 1) * Metric.diam S ^ n * M := by
    rw [hd]
    nlinarith [mul_le_mul_of_nonneg_left hdist
      (show 0 ≤ 2 * ((n : ℝ) + 1) ^ (n - 1) * Metric.diam S ^ (n - 1) * M by positivity)]
  by_cases hab : |u x| ≤ 1
  · apply hab.trans
    have hnonneg : 0 ≤ 2 * ((n : ℝ) + 1) ^ (n - 1) * Metric.diam S ^ n * M := by positivity
    linarith
  · have hs := le_self_pow₀ (le_of_lt (lt_of_not_ge hab)) (NeZero.ne n)
    linarith

/-- A uniform small-distance-to-boundary modulus follows directly from
the true Alexandrov mass, independently of the atomic support or weights. -/
theorem alexandrovOn_uniform_boundary_modulus [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) {M : ℝ} (hM : 0 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : E n → ℝ,
      ConvexOn ℝ S u → ContinuousOn u S → (∀ z ∈ frontier S, u z = 0) →
      volume (subgradientImageOn S u (interior S)) ≤ ENNReal.ofReal M →
      ∀ y ∈ S, ∀ z ∈ frontier S, dist y z < δ → |u y| < ε := by
  let B := 2 * ((n : ℝ) + 1) ^ (n - 1) * Metric.diam S ^ (n - 1) * M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let δ := ε ^ n / (B + 1)
  have hδ : 0 < δ := div_pos (pow_pos hε _) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro u hu huc hb hm y hy z hz hyz
  have hpow := alexandrovOn_boundary_power_bound hS hu huc hb hM hm y hy
  change |u y| ^ n ≤ B * Metric.infDist y (frontier S) at hpow
  have hupper : |u y| ^ n < ε ^ n := by
    have hd := Metric.infDist_le_dist_of_mem hz (x := y)
    have hδeq : (B + 1) * δ = ε ^ n := by dsimp [δ]; field_simp
    have hbd := mul_le_mul_of_nonneg_left hd hB
    nlinarith
  by_contra hge
  have he := pow_le_pow_left₀ hε.le (le_of_not_gt hge) n
  exact hupper.not_ge he

end GaussianTilt.MomentMapRegularity
