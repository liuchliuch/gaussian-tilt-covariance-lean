import GaussianTilt.MomentMapClassicalDirichletBoundaryJets
import GaussianTilt.MomentMapClassicalDirichletContinuationAdmissibility

/-!
# Genuine boundary identities for intrinsic within-domain jets

The level-set curves stay inside the actual closed domain. Within-domain
chain rules therefore derive the first and second boundary jets without a
smooth extension across the boundary.
-/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

lemma firstJet_tangent_eq_zero_of_level_constant
    {S : Set X} {u w : X → ℝ} {x e v : X} {D : X →L[ℝ] ℝ}
    (hu : HasFDerivWithinAt u D S x) (hw : ContDiffAt ℝ 2 w x)
    (he : fderiv ℝ w x e = 1) (hv : fderiv ℝ w x v = 0)
    (hlevelS : ∀ᶠ y in 𝓝 x, w y = w x → y ∈ S)
    (hzero : ∀ᶠ y in 𝓝 x, w y = w x → u y = u x) : D v = 0 := by
  obtain ⟨γ,hγ0,hγc,hγd,hlevel⟩ := exists_curve_in_regular_level hw he hv
  have hnear : Tendsto γ (𝓝 0) (𝓝 x) := by simpa only [ContinuousAt,hγ0] using hγd.continuousAt
  have hγS : ∀ᶠ t in 𝓝 0, γ t ∈ S := by
    filter_upwards [hnear.eventually hlevelS,hlevel] with t ht hl
    exact ht hl
  have heq : (fun t => u (γ t)) =ᶠ[𝓝 0] fun _ => u x := by
    filter_upwards [hnear.eventually hzero,hlevel] with t ht hl
    exact ht hl
  have hud : HasFDerivWithinAt u D S (γ 0) := by simpa only [hγ0] using hu
  have hcomp := hud.comp_hasDerivAt 0 hγd hγS
  exact hcomp.unique ((hasDerivAt_const (0:ℝ) (u x)).congr_of_eventuallyEq heq)

/-- The intrinsic first boundary jet is normal, with the true transverse
multiplier. No ordinary derivative of the zero extension is used. -/
theorem firstJet_eq_smul_of_level_constant
    {S : Set X} {u w : X → ℝ} {x e : X} {D : X →L[ℝ] ℝ}
    (hu : HasFDerivWithinAt u D S x) (hw : ContDiffAt ℝ 2 w x)
    (he : fderiv ℝ w x e = 1)
    (hlevelS : ∀ᶠ y in 𝓝 x, w y = w x → y ∈ S)
    (hzero : ∀ᶠ y in 𝓝 x, w y = w x → u y = u x) : D = (D e) • fderiv ℝ w x := by
  ext v
  have hv : fderiv ℝ w x (v-(fderiv ℝ w x v) • e) = 0 := by
    simp only [map_sub,map_smul,smul_eq_mul,he,mul_one,sub_self]
  have ht := firstJet_tangent_eq_zero_of_level_constant hu hw he hv hlevelS hzero
  simp only [map_sub,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul] at ht ⊢
  linarith

/-- A second chain rule using actual within-domain derivative fields and a
curve whose local image lies in that domain. -/
lemma second_deriv_comp_curve_of_within_fields
    {S : Set X} {u : X → ℝ} {D : X → X →L[ℝ] ℝ} {H : X →L[ℝ] X →L[ℝ] ℝ}
    {γ : ℝ → X}
    (hu : ∀ y ∈ S, HasFDerivWithinAt u (D y) S y)
    (hD : HasFDerivWithinAt D H S (γ 0))
    (hγ : ContDiffAt ℝ 2 γ 0) (hγS : ∀ᶠ t in 𝓝 0, γ t ∈ S) :
    deriv (deriv (fun t => u (γ t))) 0 =
      H (deriv γ 0) (deriv γ 0) + D (γ 0) (deriv (deriv γ) 0) := by
  have hγd : DifferentiableAt ℝ γ 0 := hγ.differentiableAt (by norm_num)
  have hDγ : DifferentiableAt ℝ (deriv γ) 0 := by
    change DifferentiableAt ℝ (fun t => fderiv ℝ γ t 1) 0
    exact ((hγ.fderiv_right (m:=1) (by norm_num)).differentiableAt le_rfl).clm_apply
      (differentiableAt_const 1)
  have hcompose := hD.comp_hasDerivAt 0 hγd.hasDerivAt hγS
  have hproduct := hcompose.clm_apply hDγ.hasDerivAt
  have heq : deriv (fun t => u (γ t)) =ᶠ[𝓝 0] (fun t => D (γ t) (deriv γ t)) := by
    filter_upwards [hγ.eventually (by norm_num),hγS.eventually_nhds] with t hgt hst
    exact ((hu (γ t) hst.self_of_nhds).comp_hasDerivAt t
      (hgt.differentiableAt (by norm_num)).hasDerivAt hst).deriv
  exact (hproduct.congr_of_eventuallyEq heq).deriv

/-- The genuine tangential second-jet identity holds for intrinsic C²
fields on the closed domain, without a boundary extension assumption. -/
theorem secondJet_tangent_eq_of_level_constant
    {S : Set X} {u w : X → ℝ} {D : X → X →L[ℝ] ℝ}
    {H : X →L[ℝ] X →L[ℝ] ℝ} {x e v : X}
    (hu : ∀ y ∈ S, HasFDerivWithinAt u (D y) S y)
    (hD : HasFDerivWithinAt D H S x) (hx : x ∈ S)
    (hw : ContDiffAt ℝ 2 w x) (he : fderiv ℝ w x e = 1) (hv : fderiv ℝ w x v = 0)
    (hlevelS : ∀ᶠ y in 𝓝 x, w y = w x → y ∈ S)
    (hzero : ∀ᶠ y in 𝓝 x, w y = w x → u y = u x) :
    H v v = D x e * fderiv ℝ (fderiv ℝ w) x v v := by
  obtain ⟨γ,hγ0,hγc,hγd,hlevel⟩ := exists_curve_in_regular_level hw he hv
  have hnear : Tendsto γ (𝓝 0) (𝓝 x) := by simpa only [ContinuousAt,hγ0] using hγd.continuousAt
  have hγS : ∀ᶠ t in 𝓝 0, γ t ∈ S := by
    filter_upwards [hnear.eventually hlevelS,hlevel] with t ht hl
    exact ht hl
  have hueq : (fun t => u (γ t)) =ᶠ[𝓝 0] fun _ => u x := by
    filter_upwards [hnear.eventually hzero,hlevel] with t ht hl
    exact ht hl
  have hDc : HasFDerivWithinAt D H S (γ 0) := by simpa only [hγ0] using hD
  have hu2 := second_deriv_comp_curve_of_within_fields hu hDc hγc hγS
  have hw2 := second_deriv_comp_curve (by simpa only [hγ0] using hw) hγc
  have hu0 : deriv (deriv (fun t => u (γ t))) 0 = 0 := by
    have h1 := hueq.deriv
    simpa using h1.deriv_eq
  have hw0 : deriv (deriv (fun t => w (γ t))) 0 = 0 := by
    have hh : (fun t => w (γ t)) =ᶠ[𝓝 0] fun _ => w x := hlevel
    have h1 := hh.deriv
    simpa using h1.deriv_eq
  have hfirst := firstJet_eq_smul_of_level_constant (hu x hx) hw he hlevelS hzero
  rw [hu0,hγ0,hγd.deriv,hfirst] at hu2
  rw [hw0,hγ0,hγd.deriv] at hw2
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul] at hu2
  have hm := congrArg (fun z : ℝ => D x e*z) hw2
  nlinarith [hm]

/-- Polarization for genuine intrinsic boundary jets. Symmetry is stated
for the actual second field and is derived for the constructed Hölder jets. -/
theorem secondJet_tangent_bilinear_eq_of_level_constant
    {S : Set X} {u w : X → ℝ} {D : X → X →L[ℝ] ℝ}
    {H : X →L[ℝ] X →L[ℝ] ℝ} {x e v z : X}
    (hu : ∀ y ∈ S, HasFDerivWithinAt u (D y) S y)
    (hD : HasFDerivWithinAt D H S x) (hx : x ∈ S)
    (hw : ContDiffAt ℝ 2 w x) (he : fderiv ℝ w x e = 1)
    (hv : fderiv ℝ w x v = 0) (hz : fderiv ℝ w x z = 0)
    (hSymm : ∀ v z, H v z = H z v)
    (hlevelS : ∀ᶠ y in 𝓝 x, w y = w x → y ∈ S)
    (hzero : ∀ᶠ y in 𝓝 x, w y = w x → u y = u x) :
    H v z = D x e * fderiv ℝ (fderiv ℝ w) x v z := by
  have hvz : fderiv ℝ w x (v+z) = 0 := by simp [map_add,hv,hz]
  have h1 := secondJet_tangent_eq_of_level_constant hu hD hx hw he hv hlevelS hzero
  have h2 := secondJet_tangent_eq_of_level_constant hu hD hx hw he hz hlevelS hzero
  have h3 := secondJet_tangent_eq_of_level_constant hu hD hx hw he hvz hlevelS hzero
  simp only [map_add,ContinuousLinearMap.add_apply] at h3
  rw [hSymm z v,hw.isSymmSndFDerivAt (by norm_num) z v] at h3
  nlinarith

end GaussianTilt.MomentMapRegularity
