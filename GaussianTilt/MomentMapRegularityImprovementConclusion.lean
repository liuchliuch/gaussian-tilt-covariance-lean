import GaussianTilt.MomentMapRegularityImprovementCampanato

/-! # First C²,α regularity of the genuine weak Alexandrov source -/
noncomputable section
open Set Metric MeasureTheory
open scoped NNReal ENNReal ContDiff
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

theorem contDiffOn_two_holder_of_classical_references [NeZero n]
    {φ f : E n → ℝ} {Lip : ℝ≥0} (hLip : LipschitzWith Lip φ)
    (hc : StrictConvexOn ℝ univ φ) (hfc : Continuous f)
    (hMA : ∀ A, IsCompact A → volume (subgradientImage φ A)=
      (volume.withDensity (fun y=>ENNReal.ofReal (f y))) A)
    (href : ∀ S : Set (E n), IsCompact S → Convex ℝ S → (interior S).Nonempty →
      ∃ w : E n → ℝ, Continuous w ∧ ContDiffOn ℝ ∞ w (interior S) ∧ ConvexOn ℝ S w ∧
        (∀ y∈frontier S, w y=0) ∧
        ∀ A, IsCompact A → A⊆interior S → volume (subgradientImageOn S w A)=volume A)
    (x₀ : E n) {r m M F α : ℝ} (hr : 0 < r) (hm : 0 < m) (hM : 0 < M)
    (hF : 0≤F) (hα : 0 < α) (hα1 : α≤1)
    (hfrange : ∀ y∈closedBall x₀ r, m≤f y ∧ f y≤M)
    (hfHolder : ∀ y∈closedBall x₀ r, ∀ z∈closedBall x₀ r, |f y-f z|≤F*‖y-z‖^α) :
    ContDiffOn ℝ 2 φ (ball x₀ (r/2)) ∧
      ∃ R H : ℝ, 0 < R ∧ 0≤H ∧ closedBall x₀ (2*R)⊆ball x₀ (r/2) ∧
        ∀ x∈closedBall x₀ (2*R), ∀ y∈closedBall x₀ (2*R),
          ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖≤
            H*‖x-y‖^improvementRemainderExponent α := by
  obtain ⟨s₀,C₀,hs₀,hC₀,happrox⟩ := uniform_quadratic_approximations_of_classical_references
    hLip hc hfc hMA href x₀ hr hm hM hF hα hα1 hfrange hfHolder
  have hβ := (improvement_exponents hα hα1).2.1
  obtain ⟨hreg,H,hH,hHolder⟩ := contDiffOn_two_of_all_radius_quadratic_approximations
    isOpen_ball hs₀ hC₀ hβ (fun x hx=>happrox x (ball_subset_closedBall hx))
  let R := min (r/8) (s₀/8)
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hRr : R≤r/8 := min_le_left _ _
  have hRs : R≤s₀/8 := min_le_right _ _
  have hsub : closedBall x₀ (2*R)⊆ball x₀ (r/2) := closedBall_subset_ball (by linarith)
  refine ⟨hreg,R,H,hR,hH,hsub,?_⟩
  intro x hx y hy
  apply hHolder x (hsub hx) y (hsub hy)
  have hdist := dist_triangle x x₀ y
  have hxx : dist x x₀≤2*R := hx
  have hyy : dist x₀ y≤2*R := by simpa only [dist_comm] using (show dist y x₀≤2*R from hy)
  rw [dist_eq_norm] at hdist
  nlinarith

end GaussianTilt.MomentMapRegularity
