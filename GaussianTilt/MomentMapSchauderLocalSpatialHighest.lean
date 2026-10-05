import GaussianTilt.MomentMapSchauderLocalSpatialGain
import GaussianTilt.MomentMapSchauderLocalHighestJet

/-! # Higher local Hölder reconstruction for smooth spatial forcing -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2000000
open Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

theorem exists_local_spatial_next_holderJetOn [NeZero n] (k : ℕ)
    {φ g : KernelSpace n → ℝ} (hφ : ContDiff ℝ (↑(k+3) : WithTop ℕ∞) φ)
    (hg : ContDiff ℝ (↑(k+3) : WithTop ℕ∞) g)
    (a : KernelSpace n) {R α : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1)
    (hφnext : ContDiffOn ℝ (↑(k+4) : WithTop ℕ∞) φ (Metric.ball a (4*R)))
    (hpos : ∀ x ∈ Metric.ball a (4*R), (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x ∈ Metric.ball a (4*R), Real.log (euclideanHessianMatrix φ x).det=g x)
    (hφj : HolderJetOn α (k+3) φ (Metric.closedBall a (2*R))) :
    ∃ r : ℝ, 0 < r ∧ 2*r ≤ R ∧ HolderJetOn α (k+4) φ (Metric.closedBall a (2*r)) := by
  let f : (Fin (k+4) → Fin n) → KernelSpace n → ℝ := fun q x =>
    iteratedFDeriv ℝ (k+4) φ x (fun i => EuclideanSpace.basisFun (Fin n) ℝ (q i))
  have hcoords : ∀ q, ∃ r : ℝ, 0 < r ∧ BoundedHolderOn α (f q) (Metric.closedBall a r) := by
    intro q
    let z : Fin (k+4) → KernelSpace n := fun i => EuclideanSpace.basisFun (Fin n) ℝ (q i)
    let w := Fin.tail (Fin.tail (Fin.tail z))
    obtain ⟨r, C, hr, hrR, hC, _, hb, hh⟩ :=
      exists_local_spatial_jet_third_order k hφ hg a hR hα hα1 hpos hMA hφj w
    have hsub : Metric.closedBall a (r/2) ⊆ Metric.ball a r := Metric.closedBall_subset_ball (by linarith)
    have hfield : BoundedHolderOn α
        (fderiv ℝ (fderiv ℝ (fderiv ℝ (scalarDerivativeJet (k+1) φ w)))) (Metric.closedBall a (r/2)) :=
      ⟨C, hC.le, fun x hx => hb x (hsub hx), fun x hx y hy => hh x (hsub hx) y (hsub hy)⟩
    let L := (ContinuousLinearMap.apply ℝ ℝ (Fin.tail (Fin.tail z) 0)).comp
      ((ContinuousLinearMap.apply ℝ (KernelSpace n →L[ℝ] ℝ) (Fin.tail z 0)).comp
        (ContinuousLinearMap.apply ℝ (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) (z 0)))
    refine ⟨r/2, by linarith, (hfield.map L).congr ?_⟩
    intro x hx
    have hz : Fin.cons (z 0) (Fin.cons (Fin.tail z 0) (Fin.cons (Fin.tail (Fin.tail z) 0) w))=z := by
      dsimp [w]
      simp only [Fin.cons_self_tail]
    have hdom : x ∈ Metric.ball a (4*R) :=
      (Metric.closedBall_subset_ball (by linarith : r/2 < 4*R)) hx
    have he := scalarDerivativeJet_cons_three_at k
      (hφnext.contDiffAt (Metric.isOpen_ball.mem_nhds hdom)) w (z 0) (Fin.tail z 0) (Fin.tail (Fin.tail z) 0)
    rw [hz] at he
    exact he.symm
  obtain ⟨r, hr, hcommon⟩ := exists_common_closedBall_holder a hcoords
  have htop : BoundedHolderOn α (iteratedFDeriv ℝ (k+4) φ) (Metric.closedBall a r) :=
    boundedHolderOn_multilinear_of_basis (k+4) hcommon
  let ρ := min r R
  have hρ : 0 < ρ := lt_min hr hR
  have hρR : ρ ≤ R := min_le_right _ _
  have hρsub : Metric.closedBall a ρ ⊆ Metric.ball a (4*R) := Metric.closedBall_subset_ball (by linarith)
  have hj := holderJetOn_of_top_on Metric.isOpen_ball hφnext (isCompact_closedBall a ρ)
    (convex_closedBall a ρ) hρsub hα.le hα1.le
    (htop.mono (Metric.closedBall_subset_closedBall (min_le_left _ _)))
  refine ⟨ρ/2, by positivity, by linarith, ?_⟩
  have he : 2*(ρ/2)=ρ := by ring
  simpa only [he] using hj

end GaussianTilt.MomentMapSchauder
