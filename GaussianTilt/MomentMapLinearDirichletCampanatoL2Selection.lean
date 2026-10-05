import GaussianTilt.MomentMapLinearDirichletCampanatoL2Holder

/-! # Constructing a uniformly Hölder coefficient field from actual L² errors -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Actual mean-square approximants construct a single Hölder field on any
small closed-half-space patch. No representative or continuity is assumed. -/
theorem exists_l2_campanato_holder_limit [NeZero n] {F : Type*}
    [NormedAddCommGroup F] [CompleteSpace F]
    (j : Fin n) (G : KernelSpace n → F) (p : KernelSpace n → ℕ → F)
    {S : Set (KernelSpace n)} {R C α : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hα : 0 < α)
    (hS : ∀ x ∈ S, 0 ≤ x j)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ R/2)
    (hI : ∀ x ∈ S, ∀ k, IntegrableOn (fun z => ‖G z-p x k‖^2)
      (upperCampanatoBall j x (R*(1/2 : ℝ)^k)))
    (hE : ∀ x ∈ S, ∀ k, (∫ z in upperCampanatoBall j x (R*(1/2 : ℝ)^k), ‖G z-p x k‖^2) ≤
      C*(R*(1/2 : ℝ)^k)^((n:ℝ)+2*α)) :
    ∃ L : KernelSpace n → F,
      (∀ x ∈ S, Tendsto (p x) atTop (𝓝 (L x))) ∧
      (∀ x ∈ S, ∀ k, ‖p x k-L x‖ ≤ campanatoL2StepConstant n C*
        (R*(1/2 : ℝ)^k)^α/(1-(1/2 : ℝ)^α)) ∧
      (∀ x ∈ S, ∀ y ∈ S, ‖L x-L y‖ ≤ campanatoL2HolderConstant n C α*‖x-y‖^α) := by
  classical
  have hex : ∀ x : S, ∃ q : F, Tendsto (p x) atTop (𝓝 q) ∧ ∀ k,
      ‖p x k-q‖ ≤ campanatoL2StepConstant n C*(R*(1/2 : ℝ)^k)^α/(1-(1/2 : ℝ)^α) := by
    intro x
    exact exists_l2_campanato_geometric_limit j x (hS x x.property) G (p x) hR
      (by norm_num) (by norm_num) hC hα (hI x x.property) (hE x x.property)
  choose q hq htail using hex
  let L : KernelSpace n → F := fun x => if hx : x ∈ S then q ⟨x,hx⟩ else 0
  have hL (x : KernelSpace n) (hx : x ∈ S) : L x = q ⟨x,hx⟩ := dif_pos hx
  have hlim : ∀ x ∈ S, Tendsto (p x) atTop (𝓝 (L x)) := by
    intro x hx
    rw [hL x hx]
    exact hq ⟨x,hx⟩
  refine ⟨L,hlim,?_,?_⟩
  · intro x hx k
    rw [hL x hx]
    exact htail ⟨x,hx⟩ k
  · intro x hx y hy
    by_cases he : x=y
    · subst y
      simp only [sub_self,norm_zero,Real.zero_rpow hα.ne',mul_zero,le_refl]
    · exact l2_campanato_limits_holder j G x y (hS x hx) (hS y hy) (p x) (p y)
        (L x) (L y) hR hC hα (hdiam x hx y hy) (norm_pos_iff.mpr (sub_ne_zero.mpr he))
        (hI x hx) (hI y hy) (hE x hx) (hE y hy) (hlim x hx) (hlim y hy)

end GaussianTilt.MomentMapLinearDirichlet
