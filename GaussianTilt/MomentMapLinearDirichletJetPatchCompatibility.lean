import GaussianTilt.MomentMapHolderInteriorEmbedding
import GaussianTilt.MomentMapHolderCompactCover
import GaussianTilt.MomentMapHolderSmoothEmbedding

/-! # Genuine compatibility of local C² fields at interior and boundary points -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped Topology
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma convex_patch_subset_closure_interior {S U : Set E}
    (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty) (hU : IsOpen U) :
    S ∩ U ⊆ closure (interior S ∩ U) := by
  have hcl : closure (interior S)=S := (hS.closure_interior_eq_closure_of_nonempty_interior hint).trans hSc.closure_eq
  simpa only [hcl] using hU.closure_inter (s := interior S)

lemma closed_patch_eq_of_interior_eq {S U : Set E}
    (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty) (hU : IsOpen U)
    {f g : E → F} (hf : ContinuousOn f (S ∩ U)) (hg : ContinuousOn g (S ∩ U))
    (he : EqOn f g (interior S ∩ U)) : EqOn f g (S ∩ U) :=
  he.of_subset_closure hf hg (inter_subset_inter_left U interior_subset)
    (convex_patch_subset_closure_interior hS hSc hint hU)

/-- The first derivative fields agree on overlapping closed-domain patches
because their actual interior derivatives agree. Boundary agreement follows
from continuity and the genuine full-dimensional convex-body density. -/
theorem local_first_fields_compatible {S U V : Set E}
    (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty)
    (hU : IsOpen U) (hV : IsOpen V) {u : E → F} {D G : E → E →L[ℝ] F}
    (hD : ContinuousOn D (S ∩ U)) (hG : ContinuousOn G (S ∩ V))
    (hdu : ∀ x ∈ interior S ∩ U, HasFDerivAt u (D x) x)
    (hgu : ∀ x ∈ interior S ∩ V, HasFDerivAt u (G x) x) :
    EqOn D G (S ∩ (U ∩ V)) := by
  apply closed_patch_eq_of_interior_eq hS hSc hint (hU.inter hV)
    (hD.mono (fun x hx => ⟨hx.1,hx.2.1⟩)) (hG.mono (fun x hx => ⟨hx.1,hx.2.2⟩))
  intro x hx
  exact (hdu x ⟨hx.1,hx.2.1⟩).unique (hgu x ⟨hx.1,hx.2.2⟩)

/-- The second fields also agree without a compatibility premise. The
first-field equality is proved on an actual open neighborhood before its
Fréchet derivative is taken. -/
theorem local_second_fields_compatible {S U V : Set E}
    (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty)
    (hU : IsOpen U) (hV : IsOpen V) {u : E → F} {D G : E → E →L[ℝ] F}
    {H K : E → E →L[ℝ] E →L[ℝ] F}
    (hD : ContinuousOn D (S ∩ U)) (hG : ContinuousOn G (S ∩ V))
    (hH : ContinuousOn H (S ∩ U)) (hK : ContinuousOn K (S ∩ V))
    (hdu : ∀ x ∈ interior S ∩ U, HasFDerivAt u (D x) x)
    (hgu : ∀ x ∈ interior S ∩ V, HasFDerivAt u (G x) x)
    (hdD : ∀ x ∈ interior S ∩ U, HasFDerivAt D (H x) x)
    (hdG : ∀ x ∈ interior S ∩ V, HasFDerivAt G (K x) x) :
    EqOn H K (S ∩ (U ∩ V)) := by
  have hDG := local_first_fields_compatible hS hSc hint hU hV hD hG hdu hgu
  apply closed_patch_eq_of_interior_eq hS hSc hint (hU.inter hV)
    (hH.mono (fun x hx => ⟨hx.1,hx.2.1⟩)) (hK.mono (fun x hx => ⟨hx.1,hx.2.2⟩))
  intro x hx
  have he : D =ᶠ[𝓝 x] G := by
    filter_upwards [(isOpen_interior.inter (hU.inter hV)).mem_nhds hx] with y hy
    exact hDG ⟨interior_subset hy.1,hy.2⟩
  exact (hdD x ⟨hx.1,hx.2.1⟩).fderiv.symm.trans
    (he.fderiv_eq.trans (hdG x ⟨hx.1,hx.2.2⟩).fderiv)

/-- Local continuous representatives agreeing almost everywhere in the
interior agree on the actual closed patch, including its boundary. -/
theorem local_value_eq_of_ae_interior [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsOpenPosMeasure] {S U : Set E}
    (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty) (hU : IsOpen U)
    {f g : E → F} (hf : ContinuousOn f (S ∩ U)) (hg : ContinuousOn g (S ∩ U))
    (hae : ∀ᵐ x ∂μ, x ∈ interior S ∩ U → f x=g x) : EqOn f g (S ∩ U) := by
  apply closed_patch_eq_of_interior_eq hS hSc hint hU hf hg
  have hOpen : IsOpen (interior S ∩ U) := isOpen_interior.inter hU
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hOpen.measurableSet).mpr hae) hOpen
    (hf.mono (inter_subset_inter_left U interior_subset)) (hg.mono (inter_subset_inter_left U interior_subset))

end GaussianTilt.MomentMapLinearDirichlet
