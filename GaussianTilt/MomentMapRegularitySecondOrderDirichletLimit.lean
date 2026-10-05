import GaussianTilt.MomentMapRegularityDirichletStability
import GaussianTilt.MomentMapRegularityDirichletDual
import GaussianTilt.MomentMapRegularityDirichletComparison
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Local weak continuity of the genuine Alexandrov measure

Uniform convergence on a compact domain controls actual contact points.
Almost-everywhere uniqueness of the limiting contact and Fatou's lemma give
lower semicontinuity on open sets. Compact-image upper semicontinuity gives
the opposite inequality on compact interior sets. No abstract Monge--Ampère
continuity theorem is assumed.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- When every limiting contact lies in an open set, all approximating
contacts lie there eventually. The proof uses the actual compact support
graph and uniform convergence, rather than continuity of a chosen minimizer. -/
theorem eventually_supportsOn_mem_open_of_uniform_limit
    {S A : Set (E n)} (hS : IsCompact S) (hA : IsOpen A)
    {u : E n → ℝ} {v : ℕ → E n → ℝ}
    (hu : ContinuousOn u S) (hvu : TendstoUniformlyOn v u atTop S)
    (p : E n) (hp : ∀ x ∈ S, SupportsOn S u p x → x ∈ A) :
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ S, SupportsOn S (v k) p x → x ∈ A := by
  classical
  by_contra hne
  have hfreq : ∃ᶠ k : ℕ in atTop,
      ¬ (∀ x ∈ S, SupportsOn S (v k) p x → x ∈ A) := not_eventually.mp hne
  obtain ⟨j, hj, hbad⟩ := extraction_of_frequently_atTop hfreq
  have hex : ∀ k, ∃ x ∈ S, SupportsOn S (v (j k)) p x ∧ x ∉ A := by
    intro k
    push_neg at hbad
    exact hbad k
  choose xs hxs hsx hnot using hex
  obtain ⟨x, hx, i, hi, hlim⟩ := hS.tendsto_subseq hxs
  have hunif : TendstoUniformlyOn (fun k => v (j (i k))) u atTop S :=
    hvu.seq_tendstoUniformlyOn (fun k => j (i k)) (hj.tendsto_atTop.comp hi.tendsto_atTop)
  have hs : SupportsOn S u p x := supportsOn_of_uniform_limit hu hunif hx
    (fun k => hxs (i k)) hlim tendsto_const_nhds (fun k => hsx (i k))
  have hxin := hp x hx hs
  have hxout : x ∈ Aᶜ := hA.isClosed_compl.mem_of_tendsto hlim
    (Eventually.of_forall (fun k => hnot (i k)))
  exact hxout hxin

/-- The actual dual gradient is a measurable contact selector. -/
lemma measurable_domainConjugate_gradient (S : Set (E n)) (u : E n → ℝ) :
    Measurable (gradient (domainConjugate S u)) :=
  (InnerProductSpace.toDual ℝ (E n)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ (domainConjugate S u))

/-- Almost every limiting open-set contact remains an open-set contact for
all sufficiently large indices. -/
theorem ae_eventually_domainContact_mem_open
    {S A : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty) (hA : IsOpen A)
    {u : E n → ℝ} {v : ℕ → E n → ℝ}
    (hu : ContinuousOn u S) (hv : ∀ k, ContinuousOn (v k) S)
    (hvu : TendstoUniformlyOn v u atTop S) :
    ∀ᵐ p ∂volume, gradient (domainConjugate S u) p ∈ A →
      ∀ᶠ k : ℕ in atTop, gradient (domainConjugate S (v k)) p ∈ A := by
  have hall : ∀ᵐ p ∂volume, ∀ k : ℕ,
      gradient (domainConjugate S (v k)) p ∈ S ∧
        SupportsOn S (v k) p (gradient (domainConjugate S (v k)) p) := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [domainConjugate_ae_unique_contact hS hSn (hv k)] with p hp
    exact ⟨hp.1, hp.2.1⟩
  filter_upwards [domainConjugate_ae_unique_contact hS hSn hu, hall] with p hp hpk
  intro hpA
  have he := eventually_supportsOn_mem_open_of_uniform_limit hS hA hu hvu p
    (fun x hx hs => by rwa [hp.2.2 x hx hs])
  filter_upwards [he] with k hk
  exact hk _ (hpk k).1 (hpk k).2

/-- Open-set lower semicontinuity of the actual Alexandrov measure under
uniform convergence on the compact domain. -/
theorem alexandrovMeasureOn_open_le_liminf_of_uniform_limit
    {S A : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty) (hA : IsOpen A)
    {u : E n → ℝ} {v : ℕ → E n → ℝ}
    (hu : ContinuousOn u S) (hv : ∀ k, ContinuousOn (v k) S)
    (hvu : TendstoUniformlyOn v u atTop S) :
    alexandrovMeasureOn S u A ≤
      liminf (fun k => alexandrovMeasureOn S (v k) A) atTop := by
  classical
  let P : Set (E n) := gradient (domainConjugate S u) ⁻¹' A
  let Ps : ℕ → Set (E n) := fun k => gradient (domainConjugate S (v k)) ⁻¹' A
  have hPm : MeasurableSet P := (measurable_domainConjugate_gradient S u) hA.measurableSet
  have hPsm (k : ℕ) : MeasurableSet (Ps k) :=
    (measurable_domainConjugate_gradient S (v k)) hA.measurableSet
  have hpoint : ∀ᵐ p ∂volume, P.indicator (fun _ => (1 : ℝ≥0∞)) p ≤
      liminf (fun k => (Ps k).indicator (fun _ => (1 : ℝ≥0∞)) p) atTop := by
    filter_upwards [ae_eventually_domainContact_mem_open hS hSn hA hu hv hvu] with p hp
    by_cases hpP : p ∈ P
    · rw [Set.indicator_of_mem hpP]
      apply le_liminf_of_le (by isBoundedDefault)
      filter_upwards [hp hpP] with k hk
      rw [Set.indicator_of_mem (show p ∈ Ps k from hk)]
    · rw [Set.indicator_of_notMem hpP]
      exact zero_le _
  have hfatou := (lintegral_mono_ae hpoint).trans
    (lintegral_liminf_le (fun k => measurable_const.indicator (hPsm k)))
  have hvol : volume P ≤ liminf (fun k => volume (Ps k)) atTop := by
    simpa only [lintegral_indicator_const hPm, one_mul,
      lintegral_indicator_const (hPsm _)] using hfatou
  simpa only [alexandrovMeasureOn, Measure.map_apply (measurable_domainConjugate_gradient S u) hA.measurableSet,
    Measure.map_apply (measurable_domainConjugate_gradient S (v _)) hA.measurableSet, P, Ps] using hvol

/-- Compact interior sets satisfy the complementary limsup inequality. -/
theorem subgradientImageOn_compact_limsup_le_of_uniform_limit
    {S A : Set (E n)} (hS : IsCompact S) (hA : IsCompact A) (hAS : A ⊆ interior S)
    {u : E n → ℝ} {v : ℕ → E n → ℝ}
    (hu : ContinuousOn u S) (hvu : TendstoUniformlyOn v u atTop S) :
    limsup (fun k => volume (subgradientImageOn S (v k) A)) atTop ≤
      volume (subgradientImageOn S u A) := by
  have hcompact := isCompact_subgradientImageOn_of_continuousOn hS hu hA hAS
  have hbound (ε : ℝ) (hε : 0 < ε) :
      limsup (fun k => volume (subgradientImageOn S (v k) A)) atTop ≤
        volume (Metric.cthickening ε (subgradientImageOn S u A)) := by
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [eventually_subgradientImageOn_subset_thickening hS hu hA hAS hvu hε] with k hk
    exact measure_mono (hk.trans (Metric.thickening_subset_cthickening _ _))
  have hlim : Tendsto (fun ε : ℝ => volume (Metric.cthickening ε (subgradientImageOn S u A)))
      (𝓝[>] (0 : ℝ)) (𝓝 (volume (subgradientImageOn S u A))) :=
    (tendsto_measure_cthickening_of_isCompact hcompact).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε

theorem alexandrovMeasureOn_compact_limsup_le_of_uniform_limit
    {S A : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    (hA : IsCompact A) (hAS : A ⊆ interior S)
    {u : E n → ℝ} {v : ℕ → E n → ℝ}
    (hu : ContinuousOn u S) (hv : ∀ k, ContinuousOn (v k) S)
    (hvu : TendstoUniformlyOn v u atTop S) :
    limsup (fun k => alexandrovMeasureOn S (v k) A) atTop ≤ alexandrovMeasureOn S u A := by
  simp_rw [alexandrovMeasureOn_apply hS hSn (hv _) hA.measurableSet (hAS.trans interior_subset),
    alexandrovMeasureOn_apply hS hSn hu hA.measurableSet (hAS.trans interior_subset)]
  exact subgradientImageOn_compact_limsup_le_of_uniform_limit hS hA hAS hu hvu

/-- Local Portmanteau bounds determine the measure on every compact test
set. The proof shrinks genuine metric neighborhoods inside the open domain. -/
theorem measure_le_on_compact_of_local_portmanteau
    {μ ν : Measure (E n)} {ms : ℕ → Measure (E n)} {U : Set (E n)} (hU : IsOpen U)
    (hνfin : ∀ A : Set (E n), IsCompact A → A ⊆ U → ν A ≠ ⊤)
    (hclosed : ∀ A : Set (E n), IsCompact A → A ⊆ U →
      limsup (fun k => ms k A) atTop ≤ ν A)
    (hopen : ∀ A : Set (E n), IsOpen A → A ⊆ U →
      μ A ≤ liminf (fun k => ms k A) atTop)
    {A : Set (E n)} (hA : IsCompact A) (hAU : A ⊆ U) : μ A ≤ ν A := by
  obtain ⟨R, hR, hRU⟩ := hA.exists_cthickening_subset_open hU hAU
  have hfinite : ∃ R > 0, ν (Metric.cthickening R A) ≠ ⊤ :=
    ⟨R, hR, hνfin _ hA.cthickening hRU⟩
  have hlim : Tendsto (fun r : ℝ => ν (Metric.cthickening r A))
      (𝓝[>] (0 : ℝ)) (𝓝 (ν A)) :=
    (tendsto_measure_cthickening_of_isClosed hfinite hA.isClosed).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds hR)] with r hr hrR
  have hCU : Metric.cthickening r A ⊆ U := (Metric.cthickening_mono hrR.le A).trans hRU
  calc
    μ A ≤ μ (Metric.thickening r A) := measure_mono (Metric.self_subset_thickening hr A)
    _ ≤ liminf (fun k => ms k (Metric.thickening r A)) atTop :=
      hopen _ Metric.isOpen_thickening ((Metric.thickening_subset_cthickening _ _).trans hCU)
    _ ≤ limsup (fun k => ms k (Metric.cthickening r A)) atTop :=
      liminf_le_limsup_of_frequently_le (Eventually.of_forall
        (fun k => measure_mono (Metric.thickening_subset_cthickening r A))).frequently
    _ ≤ ν (Metric.cthickening r A) := hclosed _ hA.cthickening hCU

/-- The open-set Portmanteau bound for finite measures of fixed total mass.
Atomic approximations of a finite density can preserve this mass exactly. -/
theorem finiteMeasure_open_le_liminf_of_tendsto_of_mass_eq
    {μ : FiniteMeasure (E n)} {ms : ℕ → FiniteMeasure (E n)}
    (hweak : Tendsto ms atTop (𝓝 μ))
    (hmass : ∀ k, (ms k : Measure (E n)) univ = (μ : Measure (E n)) univ)
    {A : Set (E n)} (hA : IsOpen A) :
    (μ : Measure (E n)) A ≤ liminf (fun k => (ms k : Measure (E n)) A) atTop := by
  have hclosed := FiniteMeasure.limsup_measure_closed_le_of_tendsto hweak hA.isClosed_compl
  have hmu : (μ : Measure (E n)) A = (μ : Measure (E n)) univ - (μ : Measure (E n)) Aᶜ := by
    simpa using measure_compl hA.isClosed_compl.measurableSet (measure_lt_top (μ : Measure (E n)) Aᶜ).ne
  have hmk (k : ℕ) : (ms k : Measure (E n)) A =
      (μ : Measure (E n)) univ - (ms k : Measure (E n)) Aᶜ := by
    simpa only [compl_compl, hmass k] using measure_compl hA.isClosed_compl.measurableSet
      (measure_lt_top (ms k : Measure (E n)) Aᶜ).ne
  simp_rw [hmu, hmk]
  have hmap := (show Antitone (fun z : ℝ≥0∞ => (μ : Measure (E n)) univ - z) from
    antitone_const_tsub).map_limsup_of_continuousAt (F := atTop)
    (fun k => (ms k : Measure (E n)) Aᶜ)
    (ENNReal.continuous_sub_left (measure_lt_top (μ : Measure (E n)) univ).ne).continuousAt
  have hh : (μ : Measure (E n)) univ - (μ : Measure (E n)) Aᶜ ≤
      (μ : Measure (E n)) univ - limsup (fun k => (ms k : Measure (E n)) Aᶜ) atTop :=
    antitone_const_tsub hclosed
  exact hh.trans_eq hmap

/-- Weak limits of actual finite-density Alexandrov solutions retain the
literal compact-set equation. This applies in particular to finite atomic
Dirichlet approximations converging to a continuous positive density. -/
theorem alexandrovOn_identity_of_uniform_limit_of_weak_convergence
    {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {u : E n → ℝ} {v : ℕ → E n → ℝ}
    (hu : ContinuousOn u S) (hv : ∀ k, ContinuousOn (v k) S)
    (hvu : TendstoUniformlyOn v u atTop S)
    {μ : FiniteMeasure (E n)} {ms : ℕ → FiniteMeasure (E n)}
    (hweak : Tendsto ms atTop (𝓝 μ))
    (hmass : ∀ k, (ms k : Measure (E n)) univ = (μ : Measure (E n)) univ)
    (hsol : ∀ k, ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S (v k) A) = (ms k : Measure (E n)) A) :
    ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S u A) = (μ : Measure (E n)) A := by
  let ν : Measure (E n) := alexandrovMeasureOn S u
  have hνfin : ∀ A : Set (E n), IsCompact A → A ⊆ interior S → ν A ≠ ⊤ := by
    intro A hA hAS
    rw [show ν A = volume (subgradientImageOn S u A) from
      alexandrovMeasureOn_apply hS hSn hu hA.measurableSet (hAS.trans interior_subset)]
    exact (isCompact_subgradientImageOn_of_continuousOn hS hu hA hAS).measure_ne_top
  have hsolc (k : ℕ) (A : Set (E n)) (hA : IsCompact A) (hAS : A ⊆ interior S) :
      alexandrovMeasureOn S (v k) A = (ms k : Measure (E n)) A := by
    rw [alexandrovMeasureOn_apply hS hSn (hv k) hA.measurableSet (hAS.trans interior_subset)]
    exact hsol k A hA hAS
  have hsolo (k : ℕ) (A : Set (E n)) (hA : IsOpen A) (hAS : A ⊆ interior S) :
      alexandrovMeasureOn S (v k) A = (ms k : Measure (E n)) A := by
    rw [alexandrovMeasureOn_apply hS hSn (hv k) hA.measurableSet (hAS.trans interior_subset)]
    exact alexandrovOn_identity_on_open_of_on_compact hS (hsol k) hA hAS
  have hνclosed (A : Set (E n)) (hA : IsCompact A) (hAS : A ⊆ interior S) :
      limsup (fun k => (ms k : Measure (E n)) A) atTop ≤ ν A := by
    have h := alexandrovMeasureOn_compact_limsup_le_of_uniform_limit hS hSn hA hAS hu hv hvu
    simpa only [hsolc _ A hA hAS] using h
  have hνopen (A : Set (E n)) (hA : IsOpen A) (hAS : A ⊆ interior S) :
      ν A ≤ liminf (fun k => (ms k : Measure (E n)) A) atTop := by
    have h := alexandrovMeasureOn_open_le_liminf_of_uniform_limit hS hSn hA hu hv hvu
    simpa only [hsolo _ A hA hAS] using h
  intro A hA hAS
  rw [← alexandrovMeasureOn_apply hS hSn hu hA.measurableSet (hAS.trans interior_subset)]
  apply le_antisymm
  · exact measure_le_on_compact_of_local_portmanteau isOpen_interior
      (fun B _ _ => (measure_lt_top (μ : Measure (E n)) B).ne)
      (fun B hB _ => FiniteMeasure.limsup_measure_closed_le_of_tendsto hweak hB.isClosed)
      hνopen hA hAS
  · exact measure_le_on_compact_of_local_portmanteau isOpen_interior hνfin hνclosed
      (fun B hB _ => finiteMeasure_open_le_liminf_of_tendsto_of_mass_eq hweak hmass hB) hA hAS

end GaussianTilt.MomentMapRegularity
