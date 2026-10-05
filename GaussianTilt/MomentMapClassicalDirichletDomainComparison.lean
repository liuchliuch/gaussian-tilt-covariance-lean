import GaussianTilt.MomentMapRegularityDirichletExtension
import GaussianTilt.MomentMapRegularitySecondOrderLocalPerturbation

/-! # Actual Dirichlet comparison when the underlying domain shrinks -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Restricting a convex potential to a compact interior subdomain does not
change its literal supporting slopes at interior points. The required local
convex extension is constructed, not assumed. -/
lemma subgradientImageOn_restrict_compact_interior {S T B : Set (E n)}
    (hS : IsCompact S) (hSn : S.Nonempty) {u : E n → ℝ}
    (hu : ContinuousOn u S) (hc : ConvexOn ℝ S u)
    (hT : IsCompact T) (hTS : T ⊆ interior S) (hBT : B ⊆ interior T) :
    subgradientImageOn T u B = subgradientImageOn S u B := by
  obtain ⟨V,L,hVL,hVc,hlocal,hle,himage⟩ :=
    exists_local_convex_lipschitz_extension hS hSn hu hc hT hTS
  rw [← himage B (hBT.trans interior_subset)]
  ext p
  constructor
  · rintro ⟨x,hx,hp⟩
    exact ⟨x,hx,(supportsOn_iff_supportsAt_of_local_extension hVc (hBT hx)
      (hlocal x (interior_subset (hBT hx))) (fun y hy => hle y (interior_subset (hTS hy)))).mp hp⟩
  · rintro ⟨x,hx,hp⟩
    exact ⟨x,hx,(supportsOn_iff_supportsAt_of_local_extension hVc (hBT hx)
      (hlocal x (interior_subset (hBT hx))) (fun y hy => hle y (interior_subset (hTS hy)))).mpr hp⟩

lemma subgradientImageOn_add_const (S : Set (E n)) (u : E n → ℝ) (c : ℝ) (A : Set (E n)) :
    subgradientImageOn S (fun x => u x+c) A = subgradientImageOn S u A := by
  ext p
  constructor <;> rintro ⟨x,hx,hp⟩ <;> refine ⟨x,hx,?_⟩
  · intro y hy
    have hh := hp y hy
    dsimp at hh
    linarith
  · intro y hy
    have hh := hp y hy
    dsimp
    linarith

lemma unit_density_alexandrovOn_comparison [NeZero n] {u v : E n → ℝ}
    (huc : Continuous u) (hvc : Continuous v) {S : Set (E n)} (hS : IsCompact S)
    (hb : ∀ y ∈ frontier S, v y ≤ u y)
    (huid : ∀ A, IsCompact A → A ⊆ interior S → volume (subgradientImageOn S u A) = volume A)
    (hvid : ∀ A, IsCompact A → A ⊆ interior S → volume (subgradientImageOn S v A) = volume A) :
    ∀ x ∈ S, v x ≤ u x := by
  apply alexandrovOn_comparison_of_density_le (f:=fun _ => 1) (g:=fun _ => 1)
    huc hvc hS hb measurable_const (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ _ => le_rfl)
  · simpa using hS.measure_ne_top (μ:=volume)
  · simpa using huid
  · simpa using hvid

/-- The actual boundary-value stability estimate for equal unit density. -/
theorem unit_density_dirichlet_boundary_stability [NeZero n] {u v : E n → ℝ}
    (huc : Continuous u) (hvc : Continuous v) {S : Set (E n)} (hS : IsCompact S)
    {ε : ℝ} (hb : ∀ y ∈ frontier S, |v y-u y| ≤ ε)
    (huid : ∀ A, IsCompact A → A ⊆ interior S → volume (subgradientImageOn S u A) = volume A)
    (hvid : ∀ A, IsCompact A → A ⊆ interior S → volume (subgradientImageOn S v A) = volume A) :
    ∀ x ∈ S, |v x-u x| ≤ ε := by
  have huplus : ∀ A, IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S (fun x => u x+ε) A) = volume A := by
    intro A hA hAS
    rw [subgradientImageOn_add_const]
    exact huid A hA hAS
  have hvplus : ∀ A, IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S (fun x => v x+ε) A) = volume A := by
    intro A hA hAS
    rw [subgradientImageOn_add_const]
    exact hvid A hA hAS
  have hupper := unit_density_alexandrovOn_comparison (huc.add continuous_const) hvc hS
    (fun y hy => by have hh := (abs_le.mp (hb y hy)).2; linarith) huplus hvid
  have hlower := unit_density_alexandrovOn_comparison (hvc.add continuous_const) huc hS
    (fun y hy => by have hh := (abs_le.mp (hb y hy)).1; linarith) hvplus huid
  intro x hx
  exact abs_le.mpr ⟨by linarith [hlower x hx], by linarith [hupper x hx]⟩

end GaussianTilt.MomentMapRegularity
