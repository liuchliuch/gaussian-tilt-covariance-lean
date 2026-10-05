import GaussianTilt.MomentMapRegularityReferenceSmoothLimit

/-! # Literal bounded-domain Alexandrov data under translation -/
noncomputable section
open Set MeasureTheory
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma supportsOn_translation_iff (S : Set (E n)) (u : E n → ℝ) (a p x : E n) :
    SupportsOn ((fun y=>y+a) ⁻¹' S) (fun y=>u (y+a)) p x ↔ SupportsOn S u p (x+a) := by
  constructor
  · intro h y hy
    have hh := h (y-a) (by simpa using hy)
    have he : y-a-x=y-(x+a) := by abel
    simpa only [sub_add_cancel,he] using hh
  · intro h y hy
    have hh := h (y+a) hy
    simpa only [add_sub_add_right_eq_sub] using hh

lemma subgradientImageOn_translation (S : Set (E n)) (u : E n → ℝ) (a : E n) (A : Set (E n)) :
    subgradientImageOn ((fun y=>y+a) ⁻¹' S) (fun y=>u (y+a)) A=
      subgradientImageOn S u ((fun y=>y+a) '' A) := by
  ext p
  constructor
  · rintro ⟨x,hx,hs⟩
    exact ⟨x+a,⟨x,hx,rfl⟩,(supportsOn_translation_iff S u a p x).mp hs⟩
  · rintro ⟨_,⟨x,hx,rfl⟩,hs⟩
    exact ⟨x,hx,(supportsOn_translation_iff S u a p x).mpr hs⟩

lemma convexOn_translation_preimage {S : Set (E n)} {u : E n → ℝ}
    (hu : ConvexOn ℝ S u) (a : E n) :
    ConvexOn ℝ ((fun y=>y+a) ⁻¹' S) (fun y=>u (y+a)) := by
  have he (x y : E n) (s t : ℝ) (hst : s+t=1) : s • x+t • y+a=s • (x+a)+t • (y+a) := by
    have hh : s • a+t • a=a := by rw [← add_smul,hst,one_smul]
    calc
      _ = s • x+t • y+(s • a+t • a) := congrArg (fun v:E n=>s • x+t • y+v) hh.symm
      _ = _ := by simp only [smul_add]; abel
  refine ⟨?_,?_⟩
  · intro x hx y hy s t hs ht hst
    change s • x+t • y+a∈S
    rw [he x y s t hst]
    exact hu.1 hx hy hs ht hst
  · intro x hx y hy s t hs ht hst
    change u (s • x+t • y+a)≤s • u (x+a)+t • u (y+a)
    rw [he x y s t hst]
    exact hu.2 hx hy hs ht hst

lemma unit_alexandrov_translation {S : Set (E n)} {u : E n → ℝ}
    (hu : ∀ A, IsCompact A → A⊆interior S → volume (subgradientImageOn S u A)=volume A)
    (a : E n) :
    ∀ A, IsCompact A → A⊆interior ((fun y=>y+a) ⁻¹' S) →
      volume (subgradientImageOn ((fun y=>y+a) ⁻¹' S) (fun y=>u (y+a)) A)=volume A := by
  intro A hA hAS
  rw [subgradientImageOn_translation]
  have hAi : (fun y=>y+a) '' A⊆interior S := by
    rintro _ ⟨y,hy,rfl⟩
    have hh := hAS hy
    have he := (Homeomorph.addRight a).preimage_interior S
    change (fun y:E n=>y+a) ⁻¹' interior S=interior ((fun y=>y+a) ⁻¹' S) at he
    rw [← he] at hh
    exact hh
  have himage : IsCompact ((fun y:E n=>y+a) '' A) := hA.image (continuous_id.add continuous_const)
  rw [hu _ himage hAi,
    ConvexIntegrability.volume_image_add_right]

end GaussianTilt.MomentMapRegularity
