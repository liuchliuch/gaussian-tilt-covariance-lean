import GaussianTilt.MomentMapRegularityReferenceLimit
import GaussianTilt.MomentMapRegularityImprovementCampanato
import GaussianTilt.MomentMapSchauderLocalMongeAmpere

/-! # Genuine local smoothness of the weak reference after inner-domain approximation -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Gradient
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapSchauder
variable {n : ℕ}

theorem reference_contDiffOn_infty_of_classical_inner_references [NeZero n]
    {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {u : E n → ℝ} (huc : Continuous u) (hucv : ConvexOn ℝ S u)
    (hub : ∀ x ∈ frontier S, u x = 0)
    (huid : ∀ A, IsCompact A → A ⊆ interior S → volume (subgradientImageOn S u A) = volume A)
    (d : ℕ → SmoothInnerDomain S ∅)
    (hex : ∀ A, IsCompact A → A ⊆ interior S → ∀ᶠ m in atTop, A ⊆ (d m).domain)
    (v : ℕ → E n → ℝ) (hvc : ∀ m, Continuous (v m))
    (hvs : ∀ m, ContDiffOn ℝ ∞ (v m) (interior (d m).body))
    (hvv : ∀ m, ConvexOn ℝ (d m).body (v m))
    (hvb : ∀ m, ∀ x ∈ frontier (d m).body, v m x = 0)
    (hvH : ∀ m, ∀ x ∈ interior (d m).body,
      (coordinateHessian (coordinatePullback (v m)) (coordinateEquiv n x)).PosDef)
    (hvMA : ∀ m, ∀ x ∈ interior (d m).body,
      (coordinateHessian (coordinatePullback (v m)) (coordinateEquiv n x)).det = 1)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hSR : S ⊆ Metric.closedBall 0 R)
    (hrS : Metric.closedBall (0 : E n) r ⊆ interior S) :
    ContDiffOn ℝ ∞ u (Metric.ball (0:E n) (r/16)) := by
  obtain ⟨hC2,H,hH,hLip⟩ := reference_contDiffOn_two_of_classical_inner_references hS hSn huc hucv hub huid
    d hex v hvc hvs hvv hvb hvH hvMA hr hR hSR hrS
  have heq := (reference_C2_equation_of_classical_inner_references hS hSn huc hucv hub huid
    d hex v hvc hvs hvv hvb hvH hvMA hr hR hSR hrS).2
  have hsub : Metric.ball (0:E n) (r/16)⊆Metric.ball 0 (r/4) := Metric.ball_subset_ball (by linarith)
  let L := 36*campanatoLimitConstant (r/4) (1/2) (1/2) (referenceLimitConstant n r R)
  apply reference_contDiffOn_infty_of_C2_lipschitz_hessian Metric.isOpen_ball (hC2.mono hsub)
    (fun x hx=>(heq x (hsub hx)).1) (fun x hx=>(heq x (hsub hx)).2) (le_max_right L 0)
  intro x hx y hy
  rw [secondFrechet_difference_norm_of_gradient_derivatives (hH x (hsub hx)) (hH y (hsub hy))]
  have hdist : 2*‖x-y‖≤r/4 := by
    have hxn : ‖x‖<r/16 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hyn : ‖y‖<r/16 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    have hh := norm_sub_le x y
    linarith
  exact (hLip x (hsub hx) y (hsub hy) hdist).trans
    (mul_le_mul_of_nonneg_right (le_max_left L 0) (norm_nonneg _))

end GaussianTilt.MomentMapRegularity
