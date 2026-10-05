import GaussianTilt.MomentMapSchauderLocalSpatialHighest
import GaussianTilt.MomentMapSchauderLocalLogdetBootstrap

/-! # Smooth local smooth spatial logdet solutions without global extensions of the PDE -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2400000
open Set Filter
open scoped ContDiff Topology
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma exists_local_spatial_patch (m : ℕ) {φ F : KernelSpace n → ℝ}
    {U : Set (KernelSpace n)} (hU : IsOpen U) (hφ : ContDiffOn ℝ (m : WithTop ℕ∞) φ U)
    (hF : ContDiffOn ℝ ∞ F U)
    {α : ℝ} (hpos : ∀ x ∈ U, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x ∈ U, Real.log (euclideanHessianMatrix φ x).det=F x)
    (hloc : LocallyHolderJetOn α m φ U) {a : KernelSpace n} (ha : a ∈ U) :
    ∃ R : ℝ, ∃ v g : KernelSpace n → ℝ, 0 < R ∧ Metric.ball a (4*R) ⊆ U ∧
      ContDiff ℝ (m : WithTop ℕ∞) v ∧ ContDiff ℝ (↑(m+1) : WithTop ℕ∞) g ∧ EqOn v φ (Metric.ball a (4*R)) ∧
      (∀ x ∈ Metric.ball a (4*R), (euclideanHessianMatrix v x).PosDef) ∧
      (∀ x ∈ Metric.ball a (4*R), Real.log (euclideanHessianMatrix v x).det=g x) ∧
      HolderJetOn α m v (Metric.closedBall a (2*R)) := by
  obtain ⟨r, hr, hrU, hj⟩ := hloc a ha
  let R := r/16
  have hR : 0 < R := by dsimp [R]; positivity
  have hbig : Metric.ball a (8*R) ⊆ U :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by dsimp [R]; linarith))).trans hrU
  obtain ⟨v, hv, _, he⟩ := exists_global_contDiff_patch hU m hφ a
    (r := 4*R) (R := 8*R) (by positivity) (by linarith) hbig
  obtain ⟨g, hg, _, hge⟩ := exists_global_contDiff_patch hU (m+1) (contDiffOn_infty.mp hF (m+1)) a
    (r := 4*R) (R := 8*R) (by positivity) (by linarith) hbig
  have hsmall : Metric.ball a (4*R) ⊆ U := (Metric.ball_subset_ball (by linarith)).trans hbig
  have hH : ∀ x ∈ Metric.ball a (4*R), euclideanHessianMatrix v x=euclideanHessianMatrix φ x :=
    fun x hx => euclideanHessianMatrix_eq_of_eqOn_open Metric.isOpen_ball he hx
  refine ⟨R, v, g, hR, hsmall, hv, hg, he, ?_, ?_, ?_⟩
  · intro x hx
    rw [hH x hx]
    exact hpos x (hsmall hx)
  · intro x hx
    rw [hH x hx]
    exact (hMA x (hsmall hx)).trans (hge hx).symm
  · have hS : Metric.closedBall a (2*R) ⊆ Metric.closedBall a r :=
      Metric.closedBall_subset_closedBall (by dsimp [R]; linarith)
    exact (hj.mono_set hS).congr_of_eqOn_open Metric.isOpen_ball
      (Metric.closedBall_subset_ball (by linarith)) (fun x hx => (he hx).symm)

theorem local_spatial_first_gain [NeZero n] {φ F : KernelSpace n → ℝ}
    {U : Set (KernelSpace n)} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    (hF : ContDiffOn ℝ ∞ F U)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ U, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x ∈ U, Real.log (euclideanHessianMatrix φ x).det=F x)
    (hloc : LocallyHolderJetOn α 2 φ U) :
    ContDiffOn ℝ 3 φ U ∧ LocallyHolderJetOn α 3 φ U := by
  have hgain : ∀ a ∈ U, ∃ R r C : ℝ, ∃ v : KernelSpace n → ℝ,
      0 < R ∧ 0 < r ∧ r ≤ R ∧ 0 < C ∧ Metric.ball a (4*R) ⊆ U ∧
      EqOn v φ (Metric.ball a (4*R)) ∧ ContDiffOn ℝ 3 v (Metric.ball a r) ∧
      BoundedHolderOn α (fderiv ℝ (fderiv ℝ (fderiv ℝ v))) (Metric.closedBall a (r/2)) := by
    intro a ha
    obtain ⟨R, v, g, hR, hdom, hv, hg, he, hPv, hEv, hjv⟩ := exists_local_spatial_patch 2 hU hφ hF hpos hMA hloc ha
    obtain ⟨H, hH, _, hh⟩ := hjv.fderiv.fderiv.value
    have hsub : Metric.closedBall a (2*R) ⊆ Metric.ball a (4*R) := Metric.closedBall_subset_ball (by linarith)
    obtain ⟨r, C, hr, hrR, hC, hc, hb, hh⟩ := exists_local_spatial_third_order hv (hg.of_le (by norm_num)) a hR hH hα hα1
      (fun x hx => hPv x (hsub hx)) (fun x hx => hEv x (hsub hx)) hh
    have hsub' : Metric.closedBall a (r/2) ⊆ Metric.ball a r := Metric.closedBall_subset_ball (by linarith)
    exact ⟨R, r, C, v, hR, hr, hrR, hC, hdom, he, hc,
      ⟨C, hC.le, fun x hx => hb x (hsub' hx), fun x hx y hy => hh x (hsub' hx) y (hsub' hy)⟩⟩
  constructor
  · intro a ha
    obtain ⟨R, r, C, v, hR, hr, _, _, _, he, hc, _⟩ := hgain a ha
    have he' : φ =ᶠ[𝓝 a] v := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by positivity : 0 < 4*R))] with x hx
      exact (he hx).symm
    exact ((hc.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).congr_of_eventuallyEq he').contDiffWithinAt
  · intro a ha
    obtain ⟨R, r, C, v, hR, hr, hrR, _, hdom, he, hc, hh⟩ := hgain a ha
    have hsub : Metric.closedBall a (r/2) ⊆ Metric.ball a r := Metric.closedBall_subset_ball (by linarith)
    have hsubDom : Metric.closedBall a (r/2) ⊆ Metric.ball a (4*R) := Metric.closedBall_subset_ball (by linarith)
    have hj := holderJetOn_of_top_on Metric.isOpen_ball hc (isCompact_closedBall a (r/2))
      (convex_closedBall a (r/2)) hsub hα.le hα1.le (boundedHolderOn_iteratedFDeriv_three hh)
    exact ⟨r/2, by positivity, hsubDom.trans hdom,
      hj.congr_of_eqOn_open Metric.isOpen_ball hsubDom he⟩

theorem local_spatial_higher_gain [NeZero n] (k : ℕ) {φ F : KernelSpace n → ℝ}
    {U : Set (KernelSpace n)} (hU : IsOpen U) (hφ : ContDiffOn ℝ (↑(k+3) : WithTop ℕ∞) φ U)
    (hF : ContDiffOn ℝ ∞ F U)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ U, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x ∈ U, Real.log (euclideanHessianMatrix φ x).det=F x)
    (hloc : LocallyHolderJetOn α (k+3) φ U) :
    ContDiffOn ℝ (↑(k+4) : WithTop ℕ∞) φ U ∧ LocallyHolderJetOn α (k+4) φ U := by
  have hnext : ContDiffOn ℝ (↑(k+4) : WithTop ℕ∞) φ U := by
    intro a ha
    obtain ⟨R, v, g, hR, hdom, hv, hg, he, hPv, hEv, hjv⟩ := exists_local_spatial_patch (k+3) hU hφ hF hpos hMA hloc ha
    have hc := contDiffAt_local_spatial_succ k hv
      (hg.of_le (by exact_mod_cast (show k+3 ≤ (k+3)+1 by omega))) a hR hα hα1 hPv hEv hjv
    have he' : φ =ᶠ[𝓝 a] v := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by positivity : 0 < 4*R))] with x hx
      exact (he hx).symm
    exact (hc.congr_of_eventuallyEq he').contDiffWithinAt
  refine ⟨hnext, ?_⟩
  intro a ha
  obtain ⟨R, v, g, hR, hdom, hv, hg, he, hPv, hEv, hjv⟩ := exists_local_spatial_patch (k+3) hU hφ hF hpos hMA hloc ha
  have hvNext : ContDiffOn ℝ (↑(k+4) : WithTop ℕ∞) v (Metric.ball a (4*R)) := by
    intro x hx
    have he' : v =ᶠ[𝓝 x] φ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
      exact he hy
    exact ((hnext.contDiffAt (hU.mem_nhds (hdom hx))).congr_of_eventuallyEq he').contDiffWithinAt
  obtain ⟨r, hr, hrR, hj⟩ := exists_local_spatial_next_holderJetOn k hv
    (hg.of_le (by exact_mod_cast (show k+3 ≤ (k+3)+1 by omega))) a hR hα hα1 hvNext hPv hEv hjv
  have hsub : Metric.closedBall a (2*r) ⊆ Metric.ball a (4*R) := Metric.closedBall_subset_ball (by linarith)
  exact ⟨2*r, by positivity, hsub.trans hdom, hj.congr_of_eqOn_open Metric.isOpen_ball hsub he⟩

/-- Smoothness of genuine local smooth spatial logdet solutions from local
C²,α data. The PDE and positivity are never extended beyond U. -/
theorem local_spatial_contDiffOn_infty_of_holderJets [NeZero n]
    {φ F : KernelSpace n → ℝ} {U : Set (KernelSpace n)} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    (hF : ContDiffOn ℝ ∞ F U)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ U, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x ∈ U, Real.log (euclideanHessianMatrix φ x).det=F x)
    (hloc : LocallyHolderJetOn α 2 φ U) : ContDiffOn ℝ ∞ φ U := by
  have hbase := local_spatial_first_gain hU hφ hF hα hα1 hpos hMA hloc
  have hind : ∀ k : ℕ, ContDiffOn ℝ (↑(k+3) : WithTop ℕ∞) φ U ∧ LocallyHolderJetOn α (k+3) φ U := by
    intro k
    induction k with
    | zero => exact hbase
    | succ k ih => exact local_spatial_higher_gain k hU ih.1 hF hα hα1 hpos hMA ih.2
  apply contDiffOn_infty.mpr
  intro k
  exact (hind k).1.of_le (by exact_mod_cast (show k ≤ k+3 by omega))

end GaussianTilt.MomentMapSchauder
