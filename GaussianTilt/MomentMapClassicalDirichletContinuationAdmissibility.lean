import GaussianTilt.MomentMapClassicalDirichletContinuationClosedness
import GaussianTilt.MomentMapSchauderUniformEllipticity

/-! # Actual openness of positive-Hessian Hölder jets on a compact convex body -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology BoundedContinuousFunction ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma holder_hessianMatrix_isSymm_on_body
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S)
    (hint : (interior S).Nonempty) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α) (x : S) : (hessianMatrix hS α j x).IsSymm := by
  have hcl : closure (interior S) = S :=
    (hS.closure_interior_eq_closure_of_nonempty_interior hint).trans hSc.closure_eq
  have hpair (i l : Fin n) : ∀ y ∈ interior S,
      extendValue α (hessianFields hS α j i l) y = extendValue α (hessianFields hS α j l i) y := by
    intro y hy
    rw [extendValue_mem α _ (interior_subset hy),extendValue_mem α _ (interior_subset hy)]
    change hessianMatrix hS α j ⟨y,interior_subset hy⟩ i l = hessianMatrix hS α j ⟨y,interior_subset hy⟩ l i
    rw [hessianMatrix_eq_actual hS hα j _ hy]
    exact (coordinateHessian_isSymm_at ((jet_contDiffOn_two hS hα j).contDiffAt (isOpen_interior.mem_nhds hy))).apply l i
  have hc (i l : Fin n) : ContinuousOn (extendValue α (hessianFields hS α j i l)) (closure (interior S)) := by
    rw [hcl]
    exact continuousOn_extendValue α _
  have hxc : (x : CoordinateSpace n) ∈ closure (interior S) := by rw [hcl]; exact x.2
  ext i l
  have h1 := le_on_closure (fun y hy => (hpair l i y hy).le) (hc l i) (hc i l) hxc
  have h2 := le_on_closure (fun y hy => (hpair i l y hy).le) (hc i l) (hc l i) hxc
  simpa only [extendValue_mem α _ x.2] using le_antisymm h1 h2

lemma continuous_holder_hessianMatrix {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ) :
    Continuous (fun p : Jet (CoordinateSpace n) ℝ hS α × S => hessianMatrix hS α p.1 p.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro l
  let L : Jet (CoordinateSpace n) ℝ hS α →L[ℝ] (S →ᵇ ℝ) :=
    (value S ℝ α).comp ((ContinuousLinearMap.proj l).comp ((ContinuousLinearMap.proj i).comp (hessianFields hS α)))
  exact BoundedContinuousFunction.continuous_eval.comp ((L.continuous.comp continuous_fst).prodMk continuous_snd)

lemma posDef_of_unit_euclideanQuadratic_pos {H : Matrix (Fin n) (Fin n) ℝ}
    (hs : H.IsSymm) (hq : ∀ v : E n, ‖v‖ = 1 → 0 < euclideanQuadratic H v) : H.PosDef := by
  refine ⟨?_,fun v hv => ?_⟩
  · simpa only [Matrix.IsSymm,Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hs
  · let w : E n := (coordinateEquiv n).symm v
    have hw : w ≠ 0 := fun h => hv ((coordinateEquiv n).symm.injective (by simpa [w] using h))
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hunit : ‖‖w‖⁻¹ • w‖ = 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have hp := hq (‖w‖⁻¹ • w) hunit
    rw [euclideanQuadratic_smul] at hp
    have he : 0 < euclideanQuadratic H w := (mul_pos_iff_of_pos_left (sq_pos_of_pos (inv_pos.mpr hn))).mp hp
    simpa only [euclideanQuadratic,w,star_trivial] using he

/-- Positivity of the real Hessian is an open condition in the constructed
jet Banach norm, using the actual compact body and its full-dimensionality. -/
theorem isOpen_positive_holder_hessians
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (hSc : IsCompact S)
    (hint : (interior S).Nonempty) {α : ℝ} (hα : 0 < α) :
    IsOpen {j : Jet (CoordinateSpace n) ℝ hS α | ∀ x : S, (hessianMatrix hS α j x).PosDef} := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hSc
  let K : Set (S × E n) := univ ×ˢ Metric.sphere 0 1
  have hK : IsCompact K := isCompact_univ.prod (isCompact_sphere _ _)
  let q := fun p : Jet (CoordinateSpace n) ℝ hS α × (S × E n) =>
    euclideanQuadratic (hessianMatrix hS α p.1 p.2.1) p.2.2
  have hq : Continuous q := continuous_euclideanQuadratic.comp
    (((continuous_holder_hessianMatrix hS α).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd))
  apply isOpen_iff_mem_nhds.mpr
  intro j hj
  have hnear : ∀ᶠ k in 𝓝 j, ∀ p ∈ K, 0 < q (k,p) :=
    hK.eventually_forall_of_forall_eventually (fun p hp =>
      hq.continuousAt.eventually (eventually_gt_nhds (euclideanQuadratic_pos (hj p.1)
        (fun hz => by
          change p.2 = 0 at hz
          have hh := hp.2
          simp [hz] at hh))))
  filter_upwards [hnear] with k hk
  intro x
  apply posDef_of_unit_euclideanQuadratic_pos (holder_hessianMatrix_isSymm_on_body hS hSc.isClosed hint hα k x)
  intro v hv
  exact hk (x,v) ⟨mem_univ _,by simpa only [Metric.mem_sphere,dist_zero_right] using hv⟩

end GaussianTilt.MomentMapRegularity
