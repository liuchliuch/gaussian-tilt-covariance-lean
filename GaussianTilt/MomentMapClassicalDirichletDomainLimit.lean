import GaussianTilt.MomentMapClassicalDirichletDomainComparison
import GaussianTilt.MomentMapClassicalDirichletGeometryExhaustion
import GaussianTilt.MomentMapRegularitySecondOrderDirichletExistence

/-! # Genuine varying-domain Dirichlet approximation

The actual continuous Alexandrov solution is approximated on the nested
constructed smooth domains. Comparison and the vanishing boundary modulus
prove uniform convergence of the zero extensions. Smooth classical
solvability is not claimed by this theorem.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma eventually_small_off_smooth_domain_exhaustion {S : Set (E n)} (hS : IsCompact S)
    {u : E n → ℝ} (hu : Continuous u) (hb : ∀ x ∈ frontier S, u x = 0)
    (d : ℕ → SmoothInnerDomain S ∅)
    (hex : ∀ A, IsCompact A → A ⊆ interior S → ∀ᶠ k in atTop, A ⊆ (d k).domain)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ S, x ∉ (d k).domain → |u x| < ε := by
  let B := S ∩ {x | ε ≤ |u x|}
  have hB : IsCompact B := hS.inter_right (isClosed_le continuous_const hu.abs)
  have hBS : B ⊆ interior S := by
    intro x hx
    by_contra hxi
    have hxb : x ∈ frontier S := ⟨subset_closure hx.1,hxi⟩
    have hh := hx.2
    change ε ≤ |u x| at hh
    rw [hb x hxb,abs_zero] at hh
    exact hε.not_ge hh
  filter_upwards [hex B hB hBS] with k hk
  intro x hx hxd
  by_contra hn
  exact hxd (hk ⟨hx,not_lt.mp hn⟩)

/-- Any actual unit-density Dirichlet solutions on the constructed inner
domains converge uniformly to the actual solution on the original body.
No convergence, boundary modulus or domain-restriction identity is assumed. -/
theorem unit_density_dirichlet_tendstoUniformlyOn_inner_domains [NeZero n]
    {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {u : E n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ S u)
    (hb : ∀ x ∈ frontier S, u x = 0)
    (huid : ∀ A, IsCompact A → A ⊆ interior S → volume (subgradientImageOn S u A) = volume A)
    (d : ℕ → SmoothInnerDomain S ∅)
    (hex : ∀ A, IsCompact A → A ⊆ interior S → ∀ᶠ k in atTop, A ⊆ (d k).domain)
    {v : ℕ → E n → ℝ} (hvc : ∀ k, ContinuousOn (v k) (d k).body)
    (hvb : ∀ k, ∀ x ∈ frontier (d k).body, v k x = 0)
    (hvid : ∀ k A, IsCompact A → A ⊆ interior (d k).body →
      volume (subgradientImageOn (d k).body (v k) A) = volume A) :
    TendstoUniformlyOn (fun k => (d k).body.indicator (v k)) u atTop S := by
  classical
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hsmall := eventually_small_off_smooth_domain_exhaustion hS hu hb d hex (half_pos hε)
  filter_upwards [hsmall] with k hk
  let V := (d k).body.indicator (v k)
  have hVc : Continuous V := continuous_zero_extension (d k).compact_sublevel.isClosed (hvc k) (hvb k)
  have hVid : ∀ A, IsCompact A → A ⊆ interior (d k).body →
      volume (subgradientImageOn (d k).body V A) = volume A := by
    intro A hA hAS
    rw [subgradientImageOn_zero_extension (hAS.trans interior_subset)]
    exact hvid k A hA hAS
  have huT : ∀ A, IsCompact A → A ⊆ interior (d k).body →
      volume (subgradientImageOn (d k).body u A) = volume A := by
    intro A hA hAT
    rw [subgradientImageOn_restrict_compact_interior (T := (d k).body) hS hSn hu.continuousOn hc
      (d k).compact_sublevel (d k).sublevel_inside hAT]
    exact huid A hA (hAT.trans (interior_subset.trans (d k).sublevel_inside))
  have hboundary : ∀ x ∈ frontier (d k).body, |V x-u x| ≤ ε/2 := by
    intro x hx
    have hxT : x ∈ (d k).body := (d k).compact_sublevel.isClosed.frontier_subset hx
    have hxS := interior_subset ((d k).sublevel_inside hxT)
    have hxd : x ∉ (d k).domain := by simpa only [← (d k).interior_body] using hx.2
    have hh := hk x hxS hxd
    simpa only [V,indicator_of_mem hxT,hvb k x hx,zero_sub,abs_neg] using hh.le
  have hcmp := unit_density_dirichlet_boundary_stability hu hVc (d k).compact_sublevel hboundary huT hVid
  intro x hx
  have habs : |V x-u x| < ε := by
    by_cases hxT : x ∈ (d k).body
    · exact (hcmp x hxT).trans_lt (half_lt_self hε)
    · have hxd : x ∉ (d k).domain := fun h => hxT (show (d k).defining x ≤ 0 from h.le)
      have hh := hk x hx hxd
      simpa only [V,indicator_of_notMem hxT,zero_sub,abs_neg] using hh.trans (half_lt_self hε)
  simpa only [Real.dist_eq,abs_sub_comm] using habs

/-- The approximants and their limit are genuinely constructed Alexandrov
solutions on genuinely constructed smooth domains. This closes the complete
variable-domain limit step before classical regularity is established. -/
theorem exists_smooth_domain_alexandrov_approximation [NeZero n]
    {S : Set (E n)} (hS : IsCompact S) (hSc : Convex ℝ S) (hSi : (interior S).Nonempty) :
    ∃ (u : E n → ℝ) (d : ℕ → SmoothInnerDomain S ∅) (v : ℕ → E n → ℝ),
      Continuous u ∧ ConvexOn ℝ S u ∧ (∀ x ∈ frontier S, u x = 0) ∧
      (∀ A, IsCompact A → A ⊆ interior S → volume (subgradientImageOn S u A) = volume A) ∧
      (∀ k, (d k).body ⊆ (d (k+1)).domain) ∧ (⋃ k, (d k).domain) = interior S ∧
      (∀ k, Continuous (v k) ∧ ConvexOn ℝ (d k).body (v k) ∧
        (∀ x ∈ frontier (d k).body, v k x = 0) ∧
        ∀ A, IsCompact A → A ⊆ interior (d k).body →
          volume (subgradientImageOn (d k).body (v k) A) = volume A) ∧
      TendstoUniformlyOn (fun k => (d k).body.indicator (v k)) u atTop S := by
  classical
  obtain ⟨u,hu,huc,hb,huid⟩ := exists_unit_density_alexandrov_dirichlet hS hSc hSi
  obtain ⟨d,hnest,hunion,hex⟩ := exists_smoothInnerDomain_exhaustion hS hSc hSi
  have hv (k : ℕ) : ∃ v : E n → ℝ, Continuous v ∧ ConvexOn ℝ (d k).body v ∧
      (∀ x ∈ frontier (d k).body, v x = 0) ∧
      ∀ A, IsCompact A → A ⊆ interior (d k).body →
        volume (subgradientImageOn (d k).body v A) = volume A := by
    apply exists_unit_density_alexandrov_dirichlet (S := (d k).body) (d k).compact_sublevel (d k).convex_body
    rw [(d k).interior_body]
    exact (d k).negative_nonempty
  choose v hv using hv
  refine ⟨u,d,v,hu,huc,hb,huid,hnest,hunion,hv,?_⟩
  exact unit_density_dirichlet_tendstoUniformlyOn_inner_domains hS (hSi.mono interior_subset)
    hu huc hb huid d hex (fun k => (hv k).1.continuousOn) (fun k => (hv k).2.2.1)
    (fun k => (hv k).2.2.2)

end GaussianTilt.MomentMapRegularity
