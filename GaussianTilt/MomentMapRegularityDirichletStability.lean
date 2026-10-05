import GaussianTilt.MomentMapRegularityDirichlet

/-!
# Stability of literal bounded-domain Alexandrov lower mass bounds

Uniform convergence preserves supporting-plane inequalities along compact
source/slope sequences. The resulting upper semicontinuity of compact
subgradient images, combined with outer continuity of Lebesgue volume,
preserves lower Alexandrov mass bounds. No abstract Monge--Ampère convergence
theorem or classical differentiability is assumed.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Uniform convergence passes literal domain-support inequalities to the
limit when both the supporting points and slopes converge. -/
theorem supportsOn_of_uniform_limit {S : Set (E n)}
    {u : E n → ℝ} {v : ℕ → E n → ℝ}
    (hu : ContinuousOn u S) (hvu : TendstoUniformlyOn v u atTop S)
    {x p : E n} {xs ps : ℕ → E n} (hx : x ∈ S)
    (hxs : ∀ k, xs k ∈ S) (hxt : Tendsto xs atTop (𝓝 x))
    (hpt : Tendsto ps atTop (𝓝 p))
    (hs : ∀ k, SupportsOn S (v k) (ps k) (xs k)) : SupportsOn S u p x := by
  have hwithin : Tendsto xs atTop (𝓝[S] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxt, Eventually.of_forall hxs⟩
  have hvx : Tendsto (fun k => v k (xs k)) atTop (𝓝 (u x)) :=
    hvu.tendsto_comp (hu.continuousWithinAt hx) hwithin
  intro y hy
  have hinner : Tendsto (fun k => inner ℝ (ps k) (y - xs k)) atTop
      (𝓝 (inner ℝ p (y - x))) := hpt.inner (tendsto_const_nhds.sub hxt)
  exact le_of_tendsto_of_tendsto (hvx.add hinner) (hvu.tendsto_at hy)
    (Eventually.of_forall (fun k => hs k y hy))

/-- Compact interior subgradient images are eventually contained in every
open thickening of the limiting image. Only uniform boundedness and uniform
convergence on the domain are used; convexity of the approximants is not
needed for this support-graph statement. -/
theorem eventually_subgradientImageOn_subset_thickening_of_uniform_bound
    {S A : Set (E n)} {u : E n → ℝ} {v : ℕ → E n → ℝ}
    (hu : ContinuousOn u S) (hA : IsCompact A) (hAS : A ⊆ interior S)
    (hvu : TendstoUniformlyOn v u atTop S)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᶠ k in atTop, ∀ y ∈ S, |v k y| ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, subgradientImageOn S (v k) A ⊆
      Metric.thickening ε (subgradientImageOn S u A) := by
  classical
  obtain ⟨r, hr, hthick⟩ := hA.exists_cthickening_subset_open isOpen_interior hAS
  let B := 2 * M / r
  have hpbound {k : ℕ} {x p : E n} (hbk : ∀ y ∈ S, |v k y| ≤ M) (hx : x ∈ A)
      (hp : SupportsOn S (v k) p x) : ‖p‖ ≤ B := by
    exact supportsOn_norm_bound hp hr hM
      (((Metric.closedBall_subset_cthickening hx r).trans hthick).trans interior_subset)
      hbk
  by_contra hne
  have hfreq : ∃ᶠ k : ℕ in atTop, ¬ (subgradientImageOn S (v k) A ⊆
      Metric.thickening ε (subgradientImageOn S u A)) := not_eventually.mp hne
  obtain ⟨j, hj, hbad⟩ := extraction_of_frequently_atTop (hfreq.and_eventually hbound)
  have hex : ∀ k, ∃ p : E n, p ∈ subgradientImageOn S (v (j k)) A ∧
      p ∉ Metric.thickening ε (subgradientImageOn S u A) := by
    intro k
    exact Set.not_subset.mp (hbad k).1
  choose ps hps hnot using hex
  choose xs hxs hsupports using hps
  have hcompact : IsCompact (A ×ˢ Metric.closedBall (0 : E n) B) :=
    hA.prod (isCompact_closedBall 0 B)
  obtain ⟨z, hz, i, hi, hlim⟩ := hcompact.tendsto_subseq
    (show ∀ k, (xs k, ps k) ∈ A ×ˢ Metric.closedBall (0 : E n) B from fun k =>
      ⟨hxs k, by simpa using hpbound (hbad k).2 (hxs k) (hsupports k)⟩)
  have hxlim : Tendsto (fun k => xs (i k)) atTop (𝓝 z.1) :=
    (continuous_fst.tendsto z).comp hlim
  have hplim : Tendsto (fun k => ps (i k)) atTop (𝓝 z.2) :=
    (continuous_snd.tendsto z).comp hlim
  have hunif : TendstoUniformlyOn (fun k => v (j (i k))) u atTop S :=
    hvu.seq_tendstoUniformlyOn (fun k => j (i k)) (hj.tendsto_atTop.comp hi.tendsto_atTop)
  have hs : SupportsOn S u z.2 z.1 := supportsOn_of_uniform_limit hu hunif
    (interior_subset (hAS hz.1)) (fun k => interior_subset (hAS (hxs (i k))))
    hxlim hplim (fun k => hsupports (i k))
  have hzin : z.2 ∈ Metric.thickening ε (subgradientImageOn S u A) :=
    Metric.self_subset_thickening hε _ ⟨z.1, hz.1, hs⟩
  have hzout : z.2 ∈ (Metric.thickening ε (subgradientImageOn S u A))ᶜ :=
    Metric.isOpen_thickening.isClosed_compl.mem_of_tendsto hplim
      (Eventually.of_forall (fun k => hnot (i k)))
  exact hzout hzin

/-- On a compact domain, uniform convergence supplies the eventual uniform
bound required for compactness of all interior supporting slopes. -/
theorem eventually_subgradientImageOn_subset_thickening
    {S A : Set (E n)} {u : E n → ℝ} {v : ℕ → E n → ℝ}
    (hS : IsCompact S) (hu : ContinuousOn u S) (hA : IsCompact A)
    (hAS : A ⊆ interior S) (hvu : TendstoUniformlyOn v u atTop S)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, subgradientImageOn S (v k) A ⊆
      Metric.thickening ε (subgradientImageOn S u A) := by
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hu
  have hb : ∀ᶠ k in atTop, ∀ y ∈ S, |v k y| ≤ max M 0 + 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hvu 1 zero_lt_one] with k hk
    intro y hy
    have hdiff : |u y - v k y| < 1 := by simpa only [Real.dist_eq] using hk y hy
    have huy : |u y| ≤ M := by simpa only [Real.norm_eq_abs] using hM y hy
    have htri := abs_add_le (u y) (v k y - u y)
    rw [show u y + (v k y - u y) = v k y by ring, abs_sub_comm] at htri
    have hMM := le_max_left M 0
    linarith
  exact eventually_subgradientImageOn_subset_thickening_of_uniform_bound hu hA hAS hvu
    (by positivity : 0 ≤ max M 0 + 1) hb hε

/-- Compactness of interior local subgradient images only requires continuity
on the actual compact domain, not a continuous extension outside it. -/
theorem isCompact_subgradientImageOn_of_continuousOn
    {S A : Set (E n)} {u : E n → ℝ}
    (hS : IsCompact S) (hu : ContinuousOn u S) (hA : IsCompact A)
    (hAS : A ⊆ interior S) : IsCompact (subgradientImageOn S u A) := by
  classical
  obtain ⟨r, hr, hthick⟩ := hA.exists_cthickening_subset_open isOpen_interior hAS
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hu
  let B := 2 * max M 0 / r
  have hpbound {x p : E n} (hx : x ∈ A) (hp : SupportsOn S u p x) : ‖p‖ ≤ B := by
    apply supportsOn_norm_bound hp hr (le_max_right _ _)
      (((Metric.closedBall_subset_cthickening hx r).trans hthick).trans interior_subset)
    intro y hy
    exact (hM y hy).trans (le_max_left _ _)
  apply IsSeqCompact.isCompact
  intro ps hps
  choose xs hxs hsupports using hps
  have hcompact : IsCompact (A ×ˢ Metric.closedBall (0 : E n) B) :=
    hA.prod (isCompact_closedBall 0 B)
  obtain ⟨z, hz, i, hi, hlim⟩ := hcompact.tendsto_subseq
    (show ∀ k, (xs k, ps k) ∈ A ×ˢ Metric.closedBall (0 : E n) B from fun k =>
      ⟨hxs k, by simpa using hpbound (hxs k) (hsupports k)⟩)
  have hxlim : Tendsto (fun k => xs (i k)) atTop (𝓝 z.1) :=
    (continuous_fst.tendsto z).comp hlim
  have hplim : Tendsto (fun k => ps (i k)) atTop (𝓝 z.2) :=
    (continuous_snd.tendsto z).comp hlim
  have hunif : TendstoUniformlyOn (fun _ : ℕ => u) u atTop S := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall (fun _ _ _ => by simpa using hε)
  have hs : SupportsOn S u z.2 z.1 := supportsOn_of_uniform_limit hu hunif
    (interior_subset (hAS hz.1)) (fun k => interior_subset (hAS (hxs (i k))))
    hxlim hplim (fun k => hsupports (i k))
  exact ⟨z.2, ⟨z.1, hz.1, hs⟩, i, hi, hplim⟩

/-- Any common lower bound on the volumes of literal compact subgradient
images passes to a uniform limit. The proof uses outer continuity of volume
on the compact limiting image. -/
theorem subgradientImageOn_volume_lower_bound_of_uniform_limit_on
    {S A : Set (E n)} {u : E n → ℝ} {v : ℕ → E n → ℝ}
    (hS : IsCompact S) (hu : ContinuousOn u S) (hA : IsCompact A)
    (hAS : A ⊆ interior S) (hvu : TendstoUniformlyOn v u atTop S)
    {m : ℝ≥0∞} (hm : ∀ᶠ k in atTop, m ≤ volume (subgradientImageOn S (v k) A)) :
    m ≤ volume (subgradientImageOn S u A) := by
  have hcompact : IsCompact (subgradientImageOn S u A) :=
    isCompact_subgradientImageOn_of_continuousOn hS hu hA hAS
  have hbound (ε : ℝ) (hε : 0 < ε) :
      m ≤ volume (Metric.cthickening ε (subgradientImageOn S u A)) := by
    obtain ⟨k, hmk, hk⟩ := (hm.and
      (eventually_subgradientImageOn_subset_thickening hS hu hA hAS hvu hε)).exists
    exact hmk.trans (measure_mono (hk.trans (Metric.thickening_subset_cthickening _ _)))
  have hlim : Tendsto (fun ε : ℝ => volume (Metric.cthickening ε (subgradientImageOn S u A)))
      (𝓝[>] (0 : ℝ)) (𝓝 (volume (subgradientImageOn S u A))) :=
    (tendsto_measure_cthickening_of_isCompact hcompact).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε

/-- The lower Alexandrov density condition on every compact interior test
set is closed under uniform convergence. This is the Perron subsolution
stability statement for the literal bounded-domain supporting relation. -/
theorem alexandrovOn_lower_bound_stable_under_uniform_limit_on
    {S : Set (E n)} {u : E n → ℝ} {v : ℕ → E n → ℝ}
    (hS : IsCompact S) (hu : ContinuousOn u S) (hvu : TendstoUniformlyOn v u atTop S)
    {μ : Measure (E n)}
    (hm : ∀ k, ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      μ A ≤ volume (subgradientImageOn S (v k) A)) :
    ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      μ A ≤ volume (subgradientImageOn S u A) := by
  intro A hA hAS
  exact subgradientImageOn_volume_lower_bound_of_uniform_limit_on hS hu hA hAS hvu
    (Eventually.of_forall (fun k => hm k A hA hAS))

/-- Globally continuous specialization of compact image-volume stability. -/
theorem subgradientImageOn_volume_lower_bound_of_uniform_limit
    {S A : Set (E n)} {u : E n → ℝ} {v : ℕ → E n → ℝ}
    (hS : IsCompact S) (hu : Continuous u) (hA : IsCompact A)
    (hAS : A ⊆ interior S) (hvu : TendstoUniformlyOn v u atTop S)
    {m : ℝ≥0∞} (hm : ∀ᶠ k in atTop, m ≤ volume (subgradientImageOn S (v k) A)) :
    m ≤ volume (subgradientImageOn S u A) :=
  subgradientImageOn_volume_lower_bound_of_uniform_limit_on hS hu.continuousOn hA hAS hvu hm

/-- Globally continuous specialization of the Perron lower-mass stability theorem. -/
theorem alexandrovOn_lower_bound_stable_under_uniform_limit
    {S : Set (E n)} {u : E n → ℝ} {v : ℕ → E n → ℝ}
    (hS : IsCompact S) (hu : Continuous u) (hvu : TendstoUniformlyOn v u atTop S)
    {μ : Measure (E n)}
    (hm : ∀ k, ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      μ A ≤ volume (subgradientImageOn S (v k) A)) :
    ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      μ A ≤ volume (subgradientImageOn S u A) :=
  alexandrovOn_lower_bound_stable_under_uniform_limit_on hS hu.continuousOn hvu hm

end GaussianTilt.MomentMapRegularity
