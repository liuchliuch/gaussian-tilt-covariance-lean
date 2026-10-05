import GaussianTilt.MomentMapHolderJetCompactness

/-! # Genuine closed-domain jet compatibility from interior derivatives

Continuous derivative fields on a full-dimensional closed convex body extend
as within-derivatives by the actual mean-value theorem. The segment FTC then
constructs both compatibility constraints in the Hölder Banach domain.
-/
noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The boundary derivative is proved, not assumed: continuous limits of
actual interior derivatives determine the true within-derivative. -/
theorem hasFDerivWithinAt_of_continuous_interior_field
    {S : Set E} (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty)
    {u : E → F} {D : E → E →L[ℝ] F} (hu : ContinuousOn u S) (hD : ContinuousOn D S)
    (hd : ∀ x ∈ interior S, HasFDerivAt u (D x) x) {x : E} (hx : x ∈ S) :
    HasFDerivWithinAt u (D x) S x := by
  have hcl : closure (interior S) = S :=
    (hS.closure_interior_eq_closure_of_nonempty_interior hint).trans hSc.closure_eq
  have ht : Tendsto (fderiv ℝ u) (𝓝[interior S] x) (𝓝 (D x)) := by
    apply ((hD x hx).mono interior_subset).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hd y hy).fderiv.symm
  have he := hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt) hS.interior isOpen_interior
    (fun y hy => (hu y (by simpa only [hcl] using hy)).mono interior_subset) ht
  simpa only [hcl] using he

/-- Actual closed-segment FTC, with no derivative assumption at the
boundary. Both endpoint continuity and the interior derivative field are literal. -/
theorem segment_ftc_of_continuous_interior_field
    {S : Set E} (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty)
    {u : E → F} {D : E → E →L[ℝ] F} (hu : ContinuousOn u S) (hD : ContinuousOn D S)
    (hd : ∀ x ∈ interior S, HasFDerivAt u (D x) x) (x y : S) :
    u y - u x = ∫ t in (0 : ℝ)..1, D (segmentPoint hS x y t) ((y : E) - x) := by
  let path : ℝ → E := fun t => (x : E) + t • ((y : E) - x)
  have hp (t : ℝ) : HasDerivAt path ((y : E) - x) t := by
    simpa only [path, one_smul] using ((hasDerivAt_id t).smul_const ((y : E) - x)).const_add (x : E)
  have hmaps : MapsTo path (Icc (0 : ℝ) 1) S := by
    intro t ht
    change (x : E) + t • ((y : E) - x) ∈ S
    rw [← segmentPoint_eq hS x y ht]
    exact (segmentPoint hS x y t).2
  have hc : ContinuousOn (fun t => u (path t)) (Icc (0 : ℝ) 1) :=
    hu.comp (by unfold path; fun_prop) hmaps
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun t => u (path t))
        (D (segmentPoint hS x y t) ((y : E) - x)) (Ioi t) t := by
    intro t ht
    have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hf := hasFDerivWithinAt_of_continuous_interior_field hS hSc hint hu hD hd (hmaps htcc)
    have hh := hf.comp_hasDerivWithinAt t (hp t).hasDerivWithinAt hmaps
    have hh' := hh.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    rw [segmentPoint_eq hS x y htcc]
    exact hh'.hasDerivWithinAt
  have hi : IntervalIntegrable (fun t => D (segmentPoint hS x y t) ((y : E) - x)) volume 0 1 := by
    have hcD : Continuous (fun t => D (segmentPoint hS x y t)) :=
      hD.comp_continuous ((continuous_subtype_val).comp (continuous_segmentPoint hS x y))
        (fun t => (segmentPoint hS x y t).2)
    exact (hcD.clm_apply continuous_const).intervalIntegrable 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hc hderiv hi
  simpa only [path, zero_smul, add_zero, one_smul, add_sub_cancel] using he.symm

/-- Actual continuous Hölder fields with the true interior derivative
identities determine a compatible Hölder jet on the whole closed convex body. -/
theorem exists_jet_of_continuous_holder_interior_fields
    {S : Set E} (hS : Convex ℝ S) (hSc : IsCompact S) (hint : (interior S).Nonempty)
    {α Cu CD CH : ℝ} (u : E → F) (D : E → E →L[ℝ] F) (H : E → E →L[ℝ] E →L[ℝ] F)
    (hu : ContinuousOn u S) (hD : ContinuousOn D S) (hH : ContinuousOn H S)
    (huh : ∀ x ∈ S, ∀ y ∈ S, ‖u x - u y‖ ≤ Cu * dist x y ^ α)
    (hDh : ∀ x ∈ S, ∀ y ∈ S, ‖D x - D y‖ ≤ CD * dist x y ^ α)
    (hHh : ∀ x ∈ S, ∀ y ∈ S, ‖H x - H y‖ ≤ CH * dist x y ^ α)
    (hdu : ∀ x ∈ interior S, HasFDerivAt u (D x) x)
    (hdD : ∀ x ∈ interior S, HasFDerivAt D (H x) x) :
    ∃ j : Jet E F hS α,
      (∀ x : S, value S F α (jetValue E F hS α j) x = u x) ∧
      (∀ x : S, value S (E →L[ℝ] F) α (jetFirst E F hS α j) x = D x) ∧
      (∀ x : S, value S (E →L[ℝ] E →L[ℝ] F) α (jetSecond E F hS α j) x = H x) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hSc
  let bu : S →ᵇ F := BoundedContinuousFunction.mkOfCompact ⟨fun x => u x,
    continuousOn_iff_continuous_restrict.mp hu⟩
  let bD : S →ᵇ (E →L[ℝ] F) := BoundedContinuousFunction.mkOfCompact ⟨fun x => D x,
    continuousOn_iff_continuous_restrict.mp hD⟩
  let bH : S →ᵇ (E →L[ℝ] E →L[ℝ] F) := BoundedContinuousFunction.mkOfCompact ⟨fun x => H x,
    continuousOn_iff_continuous_restrict.mp hH⟩
  let U := ofBounded S F α bu Cu (fun x y => huh x x.2 y y.2)
  let G := ofBounded S (E →L[ℝ] F) α bD CD (fun x y => hDh x x.2 y y.2)
  let K := ofBounded S (E →L[ℝ] E →L[ℝ] F) α bH CH (fun x y => hHh x x.2 y y.2)
  have h₀ : ∀ x y, value S F α U y - value S F α U x = segmentIntegral hS α x y G := by
    intro x y
    exact segment_ftc_of_continuous_interior_field hS hSc.isClosed hint hu hD hdu x y
  have h₁ : ∀ x y, value S (E →L[ℝ] F) α G y - value S (E →L[ℝ] F) α G x = segmentIntegral hS α x y K := by
    intro x y
    exact segment_ftc_of_continuous_interior_field hS hSc.isClosed hint hD hH hdD x y
  exact ⟨ofFields hS α U G K h₀ h₁, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

end GaussianTilt.HolderSpace
