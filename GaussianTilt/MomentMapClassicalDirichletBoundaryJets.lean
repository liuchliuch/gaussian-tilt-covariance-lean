import GaussianTilt.MomentMapClassicalDirichletBoundaryGeometry

/-! # Zero-boundary first and second jets derived from actual curves -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Gradient
namespace GaussianTilt.MomentMapRegularity
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

lemma fderiv_tangent_eq_zero_of_level_constant {u w : X → ℝ} {x e v : X}
    (hu : DifferentiableAt ℝ u x) (hw : ContDiffAt ℝ 2 w x)
    (he : fderiv ℝ w x e = 1) (hv : fderiv ℝ w x v = 0)
    (hzero : ∀ᶠ y in 𝓝 x, w y = w x → u y = u x) : fderiv ℝ u x v = 0 := by
  obtain ⟨γ,hγ0,hγc,hγd,hlevel⟩ := exists_curve_in_regular_level hw he hv
  have hnear : Tendsto γ (𝓝 0) (𝓝 x) := by simpa only [ContinuousAt, hγ0] using hγd.continuousAt
  have heq : (fun t => u (γ t)) =ᶠ[𝓝 0] fun _ => u x := by
    filter_upwards [hnear.eventually hzero, hlevel] with t ht hl
    exact ht hl
  have hud : HasFDerivAt u (fderiv ℝ u x) (γ 0) := by simpa only [hγ0] using hu.hasFDerivAt
  have hcomp := hud.comp_hasDerivAt 0 hγd
  exact hcomp.unique ((hasDerivAt_const (0 : ℝ) (u x)).congr_of_eventuallyEq heq)

/-- The first jet is normal, with its multiplier computed from any actual
unit transverse direction. -/
theorem fderiv_eq_smul_of_level_constant {u w : X → ℝ} {x e : X}
    (hu : DifferentiableAt ℝ u x) (hw : ContDiffAt ℝ 2 w x)
    (he : fderiv ℝ w x e = 1)
    (hzero : ∀ᶠ y in 𝓝 x, w y = w x → u y = u x) :
    fderiv ℝ u x = (fderiv ℝ u x e) • fderiv ℝ w x := by
  ext v
  have htan : fderiv ℝ w x (v-(fderiv ℝ w x v) • e) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, he, mul_one, sub_self]
  have hh := fderiv_tangent_eq_zero_of_level_constant hu hw he htan hzero
  simp only [map_sub, map_smul, smul_eq_mul] at hh
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  linarith

/-- The actual second chain rule along a C² curve, using only pointwise C²
regularity and the genuine Fréchet derivatives. -/
lemma second_deriv_comp_curve {u : X → ℝ} {γ : ℝ → X}
    (hu : ContDiffAt ℝ 2 u (γ 0)) (hγ : ContDiffAt ℝ 2 γ 0) :
    deriv (deriv (fun t => u (γ t))) 0 =
      fderiv ℝ (fderiv ℝ u) (γ 0) (deriv γ 0) (deriv γ 0) +
        fderiv ℝ u (γ 0) (deriv (deriv γ) 0) := by
  have hγd : DifferentiableAt ℝ γ 0 := hγ.differentiableAt (by norm_num)
  have hDγ : DifferentiableAt ℝ (deriv γ) 0 := by
    change DifferentiableAt ℝ (fun t => fderiv ℝ γ t 1) 0
    exact ((hγ.fderiv_right (m:=1) (by norm_num)).differentiableAt le_rfl).clm_apply
      (differentiableAt_const 1)
  have hDu := ((hu.fderiv_right (m:=1) (by norm_num)).differentiableAt le_rfl).hasFDerivAt
  have hcompose := hDu.comp_hasDerivAt 0 hγd.hasDerivAt
  have hproduct := hcompose.clm_apply hDγ.hasDerivAt
  have heq : deriv (fun t => u (γ t)) =ᶠ[𝓝 0] (fun t => fderiv ℝ u (γ t) (deriv γ t)) := by
    filter_upwards [hγ.eventually (by norm_num),
      hγd.continuousAt.eventually (hu.eventually (by norm_num))] with t hgt hut
    exact ((hut.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (hgt.differentiableAt (by norm_num)).hasDerivAt).deriv
  exact (hproduct.congr_of_eventuallyEq heq).deriv

/-- Vanishing on the genuine regular level set forces the tangential second
jet identity. Both first and second boundary identities are derived. -/
theorem secondFDeriv_tangent_eq_of_level_constant {u w : X → ℝ} {x e v : X}
    (hu : ContDiffAt ℝ 2 u x) (hw : ContDiffAt ℝ 2 w x)
    (he : fderiv ℝ w x e = 1) (hv : fderiv ℝ w x v = 0)
    (hzero : ∀ᶠ y in 𝓝 x, w y = w x → u y = u x) :
    fderiv ℝ (fderiv ℝ u) x v v =
      (fderiv ℝ u x e) * fderiv ℝ (fderiv ℝ w) x v v := by
  obtain ⟨γ,hγ0,hγc,hγd,hlevel⟩ := exists_curve_in_regular_level hw he hv
  have hnear : Tendsto γ (𝓝 0) (𝓝 x) := by simpa only [ContinuousAt, hγ0] using hγd.continuousAt
  have hueq : (fun t => u (γ t)) =ᶠ[𝓝 0] fun _ => u x := by
    filter_upwards [hnear.eventually hzero, hlevel] with t ht hl
    exact ht hl
  have hw2 := second_deriv_comp_curve (by simpa only [hγ0] using hw) hγc
  have hu2 := second_deriv_comp_curve (by simpa only [hγ0] using hu) hγc
  have hw0 : deriv (deriv (fun t => w (γ t))) 0 = 0 := by
    have hh : (fun t => w (γ t)) =ᶠ[𝓝 0] fun _ => w x := hlevel
    have h1 := hh.deriv
    simpa using h1.deriv_eq
  have hu0 : deriv (deriv (fun t => u (γ t))) 0 = 0 := by
    have h1 := hueq.deriv
    simpa using h1.deriv_eq
  have hfirst := fderiv_eq_smul_of_level_constant (hu.differentiableAt (by norm_num)) hw he hzero
  rw [hw0,hγ0,hγd.deriv] at hw2
  rw [hu0,hγ0,hγd.deriv,hfirst] at hu2
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hu2
  have hm := congrArg (fun z : ℝ => (fderiv ℝ u x e)*z) hw2
  nlinarith [hm]

end GaussianTilt.MomentMapRegularity
