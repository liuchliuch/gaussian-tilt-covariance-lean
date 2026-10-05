import GaussianTilt.MomentMapLinearDirichletNewtonianPotentialJetBounds
import GaussianTilt.MomentMapLinearDirichletNewtonianPotentialMollify

/-! # Actual compatible Hölder jets of the nonsmooth-data Newtonian potential -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Convolution BoundedContinuousFunction
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder GaussianTilt.HolderSpace
variable {n : ℕ}

/-- Actual mollified potentials have a compatible C²,α jet limit, whose
value is the literal Newtonian integral and whose Hessian is the limit of
actual Hessians. Neither jet compatibility nor potential regularity is assumed. -/
theorem exists_newtonianPotential_holder_jet [NeZero n]
    {f : KernelSpace n → ℝ} (hf : Continuous f) (hs : HasCompactSupport f)
    {α H R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) :
    ∃ j : Jet (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) R) α,
      (∀ x : Metric.closedBall (0 : KernelSpace n) R,
        value _ ℝ α (jetValue (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) R) α j) x = newtonianPotential f x) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ x : Metric.closedBall (0 : KernelSpace n) R,
          Tendsto (fun k => fderiv ℝ (fderiv ℝ (newtonianPotential (harmonicMollify (φ k) f))) x)
            atTop (𝓝 (value _ (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) α
              (jetSecond (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) R) α j) x)) := by
  obtain ⟨A, hA, hsA⟩ := hs.isBounded.subset_closedBall_lt 0 (0 : KernelSpace n)
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous hf
  let F := max B 0
  have hF : 0 ≤ F := le_max_right _ _
  have hfb : ∀ x, |f x| ≤ F := by
    intro x
    have hb : |f x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
    exact hb.trans (le_max_left B 0)
  have hfs : Function.support f ⊆ Metric.closedBall 0 A := fun x hx => hsA (subset_tsupport f hx)
  obtain ⟨C, hC, hjet⟩ := exists_newtonianPotential_jet_bound (n := n) (A := A + 1) hα hα1 hR hF hH
  have hm (k : ℕ) := harmonicMollify_smooth hf.locallyIntegrable k
  have hmc (k : ℕ) := harmonicMollify_compact hs k
  have hms (k : ℕ) := harmonicMollify_support_bound hfs k
  have hmb (k : ℕ) := harmonicMollify_bound hfb k
  have hmh (k : ℕ) := harmonicMollify_holder hf hholder k
  choose js hjs hj₀ hj₁ hj₂ using (fun k => hjet (harmonicMollify k f) (hm k) (hmc k) (hms k) (hmb k) (hmh k))
  obtain ⟨j, hj, φ, hφ, ht₀, ht₁, ht₂⟩ := exists_jet_uniform_subseq
    (convex_closedBall (0 : KernelSpace n) R) (isCompact_closedBall 0 R) hα hC js hjs
  refine ⟨j, ?_, φ, hφ, ?_⟩
  · intro x
    have ht := ((BoundedContinuousFunction.evalCLM ℝ x).continuous.tendsto _).comp ht₀
    have hp := (newtonianPotential_tendsto hF (fun k => (hm k).continuous) hmb hms
      (harmonicMollify_tendsto_of_continuous hf) x).comp hφ.tendsto_atTop
    have ht' : Tendsto (fun k => newtonianPotential (harmonicMollify (φ k) f) x) atTop
        (𝓝 (value _ ℝ α (jetValue (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) R) α j) x)) := by
      simpa only [Function.comp_def, BoundedContinuousFunction.evalCLM_apply, hj₀] using ht
    exact tendsto_nhds_unique ht' hp
  · intro x
    have ht := (BoundedContinuousFunction.continuous_eval_const (x := x)).tendsto _ |>.comp ht₂
    simpa only [Function.comp_def, BoundedContinuousFunction.evalCLM_apply, hj₂] using ht

end GaussianTilt.MomentMapLinearDirichlet
