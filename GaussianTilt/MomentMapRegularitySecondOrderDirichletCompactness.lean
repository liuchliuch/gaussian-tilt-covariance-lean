import GaussianTilt.MomentMapRegularitySecondOrderBoundaryModulus
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Genuine compactness of bounded-mass Dirichlet potentials

The local Aleksandrov boundary modulus and convex interior Lipschitz
estimate give equicontinuity on the whole compact domain. Arzelà--Ascoli
then supplies an actual uniformly convergent subsequence, preserving
convexity and zero boundary values.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Equicontinuity is derived from the actual common Alexandrov mass bound,
including at the boundary of the Dirichlet domain. -/
theorem equicontinuous_dirichlet_of_mass_bound [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) {u : ℕ → E n → ℝ}
    (hu : ∀ k, ConvexOn ℝ S (u k)) (huc : ∀ k, ContinuousOn (u k) S)
    (hb : ∀ k, ∀ x ∈ frontier S, u k x = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ k, volume (subgradientImageOn S (u k) (interior S)) ≤ ENNReal.ofReal M) :
    Equicontinuous (fun k => fun x : S => u k x) := by
  let B := 2 * ((n : ℝ) + 1) ^ (n - 1) * Metric.diam S ^ n * M + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hab (k : ℕ) (x : E n) (hx : x ∈ S) : |u k x| ≤ B :=
    alexandrovOn_uniform_abs_bound hS (hu k) (huc k) (hb k) hM (hmass k) x hx
  intro x
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  by_cases hxi : (x : E n) ∈ interior S
  · obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxi)
    let K : ℝ≥0 := (2 * B / (r / 2)).toNNReal
    have hlip (k : ℕ) : LipschitzOnWith K (u k) (Metric.ball (x : E n) (r / 2)) := by
      have h := ((hu k).subset hrs (convex_ball _ _)).lipschitzOnWith_of_abs_le
        (half_pos hr) (fun y hy => hab k y (hrs hy))
      simpa only [show r - r / 2 = r / 2 by ring] using h
    refine ⟨min (r / 2) (ε / (K + 1)), lt_min (half_pos hr) (div_pos hε (by positivity)), ?_⟩
    intro y hy k
    have hyx : dist (y : E n) (x : E n) < r / 2 := (lt_min_iff.mp hy).1
    have hyε : dist (y : E n) (x : E n) < ε / ((K : ℝ) + 1) := (lt_min_iff.mp hy).2
    have hxball : (x : E n) ∈ Metric.ball (x : E n) (r / 2) := Metric.mem_ball_self (half_pos hr)
    have hyball : (y : E n) ∈ Metric.ball (x : E n) (r / 2) := hyx
    have hbnd := (hlip k).dist_le_mul (x : E n) hxball (y : E n) hyball
    rw [dist_comm (x : E n) (y : E n)] at hbnd
    have hεb := (lt_div_iff₀ (by positivity : 0 < (K : ℝ) + 1)).mp hyε
    exact hbnd.trans_lt (by nlinarith [(show 0 ≤ dist (y : E n) (x : E n) from dist_nonneg)])
  · have hxf : (x : E n) ∈ frontier S := ⟨subset_closure x.property, hxi⟩
    obtain ⟨δ, hδ, hmod⟩ := alexandrovOn_uniform_boundary_modulus hS hM hε
    refine ⟨δ, hδ, ?_⟩
    intro y hy k
    have h := hmod (u k) (hu k) (huc k) (hb k) (hmass k) y y.property x hxf hy
    simpa [hb k x hxf, Real.dist_eq] using h

/-- Uniform limits on the actual domain preserve convexity. -/
lemma convexOn_of_uniform_limit_on {S : Set (E n)} {u : E n → ℝ} {v : ℕ → E n → ℝ}
    (hv : ∀ k, ConvexOn ℝ S (v k)) (hvu : TendstoUniformlyOn v u atTop S) :
    ConvexOn ℝ S u := by
  refine ⟨(hv 0).1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz := (hv 0).1 hx hy ha hb hab
  have hleft := hvu.tendsto_at hz
  have hright := ((hvu.tendsto_at hx).const_mul a).add ((hvu.tendsto_at hy).const_mul b)
  simp only [smul_eq_mul] at *
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall (fun k => (hv k).2 hx hy ha hb hab))

/-- The actual Arzelà--Ascoli extraction for convex zero-boundary potentials
with uniformly bounded literal Alexandrov mass on a fixed compact domain. -/
theorem exists_uniformly_convergent_dirichlet_subsequence [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) {v : ℕ → E n → ℝ}
    (hv : ∀ k, ConvexOn ℝ S (v k)) (hvc : ∀ k, ContinuousOn (v k) S)
    (hb : ∀ k, ∀ x ∈ frontier S, v k x = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ k, volume (subgradientImageOn S (v k) (interior S)) ≤ ENNReal.ofReal M) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ ∃ u : E n → ℝ,
      ContinuousOn u S ∧ ConvexOn ℝ S u ∧ (∀ x ∈ frontier S, u x = 0) ∧
      TendstoUniformlyOn (fun k => v (j k)) u atTop S := by
  classical
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let F : ℕ → BoundedContinuousFunction S ℝ := fun k =>
    BoundedContinuousFunction.mkOfCompact ⟨fun x => v k x, (hvc k).restrict⟩
  let B := 2 * ((n : ℝ) + 1) ^ (n - 1) * Metric.diam S ^ n * M + 1
  have hab (k : ℕ) (x : S) : |F k x| ≤ B :=
    alexandrovOn_uniform_abs_bound hS (hv k) (hvc k) (hb k) hM (hmass k) x x.property
  have heq : Equicontinuous (fun k => fun x : S => F k x) :=
    equicontinuous_dirichlet_of_mass_bound hS hv hvc hb hM hmass
  have hrange : Equicontinuous (fun f : Set.range F => fun x : S => f.val x) := by
    intro x
    apply Metric.equicontinuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδbound⟩ := Metric.equicontinuousAt_iff.mp (heq x) ε hε
    refine ⟨δ, hδ, ?_⟩
    intro y hy f
    obtain ⟨k, hk⟩ := f.property
    simpa only [← hk] using hδbound y hy k
  have hcompact : IsCompact (closure (Set.range F)) :=
    BoundedContinuousFunction.arzela_ascoli (Icc (-B) B) isCompact_Icc (Set.range F)
      (by rintro f x ⟨k, rfl⟩; exact abs_le.mp (hab k x)) hrange
  obtain ⟨f, _, j, hj, hlim⟩ := hcompact.tendsto_subseq
    (fun k => subset_closure (mem_range_self k))
  have huni : TendstoUniformly (fun k => fun x : S => F (j k) x) f atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  let u : E n → ℝ := fun x => if hx : x ∈ S then f ⟨x, hx⟩ else 0
  have huval (x : E n) (hx : x ∈ S) : u x = f ⟨x, hx⟩ := dif_pos hx
  have huc : ContinuousOn u S := by
    rw [continuousOn_iff_continuous_restrict]
    convert f.continuous using 1
    ext x
    exact huval x x.property
  have hunif : TendstoUniformlyOn (fun k => v (j k)) u atTop S := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp huni ε hε] with k hk
    intro x hx
    simpa only [huval x hx] using hk ⟨x, hx⟩
  refine ⟨j, hj, u, huc, convexOn_of_uniform_limit_on (fun k => hv (j k)) hunif, ?_, hunif⟩
  intro x hx
  have ht := hunif.tendsto_at (hS.isClosed.frontier_subset hx)
  have hzero : Tendsto (fun k => v (j k) x) atTop (𝓝 0) := by
    simp_rw [hb _ x hx]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique ht hzero

/-- Extending a zero-boundary Dirichlet potential by zero is genuinely
continuous. No convexity is claimed outside the domain. -/
lemma continuous_zero_extension {S : Set (E n)} (hS : IsClosed S)
    {u : E n → ℝ} (hu : ContinuousOn u S) (hb : ∀ x ∈ frontier S, u x = 0) :
    Continuous (S.indicator u) := by
  apply continuous_indicator hb
  rwa [hS.closure_eq]

/-- The zero extension leaves every literal bounded-domain supporting
plane and image unchanged on source subsets of the domain. -/
lemma subgradientImageOn_zero_extension {S A : Set (E n)} (hAS : A ⊆ S) (u : E n → ℝ) :
    subgradientImageOn S (S.indicator u) A = subgradientImageOn S u A := by
  classical
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    refine ⟨x, hx, ?_⟩
    intro y hy
    simpa only [Set.indicator_of_mem (hAS hx), Set.indicator_of_mem hy] using hp y hy
  · rintro ⟨x, hx, hp⟩
    refine ⟨x, hx, ?_⟩
    intro y hy
    simpa only [Set.indicator_of_mem (hAS hx), Set.indicator_of_mem hy] using hp y hy

/-- The compactness limit can be represented by an actual globally
continuous zero extension, convex only where the Dirichlet equation lives. -/
theorem exists_continuous_dirichlet_subsequence [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) {v : ℕ → E n → ℝ}
    (hv : ∀ k, ConvexOn ℝ S (v k)) (hvc : ∀ k, ContinuousOn (v k) S)
    (hb : ∀ k, ∀ x ∈ frontier S, v k x = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ k, volume (subgradientImageOn S (v k) (interior S)) ≤ ENNReal.ofReal M) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ ∃ u : E n → ℝ,
      Continuous u ∧ ConvexOn ℝ S u ∧ (∀ x ∈ frontier S, u x = 0) ∧
      TendstoUniformlyOn (fun k => v (j k)) u atTop S := by
  classical
  obtain ⟨j, hj, u, huc, hu, hub, hlim⟩ :=
    exists_uniformly_convergent_dirichlet_subsequence hS hv hvc hb hM hmass
  have heq : EqOn (S.indicator u) u S := fun x hx => Set.indicator_of_mem hx u
  have hconv : ConvexOn ℝ S (S.indicator u) := by
    refine ⟨hu.1, ?_⟩
    intro x hx y hy a b ha hb hab
    rw [heq hx, heq hy, heq (hu.1 hx hy ha hb hab)]
    exact hu.2 hx hy ha hb hab
  refine ⟨j, hj, S.indicator u, continuous_zero_extension hS.isClosed huc hub, hconv, ?_, ?_⟩
  · intro x hx
    rw [heq (hS.isClosed.frontier_subset hx), hub x hx]
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim ε hε] with k hk
    intro x hx
    rw [heq hx]
    exact hk x hx

end GaussianTilt.MomentMapRegularity
