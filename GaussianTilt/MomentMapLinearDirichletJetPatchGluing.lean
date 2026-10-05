import GaussianTilt.MomentMapLinearDirichletJetPatchCompatibility

/-! # Actual global derivative fields from compatible local closed-domain patches -/
noncomputable section
set_option maxHeartbeats 2500000
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Compatible continuous local fields glue by pointwise choice; the
result agrees throughout every closed patch, and is genuinely continuous
on the whole set. -/
theorem exists_continuous_glued_field {ι : Type*} {S : Set E}
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x ∈ S, ∃ i, x ∈ U i)
    (f : ι → E → F) (hf : ∀ i, ContinuousOn (f i) (S ∩ U i))
    (hcompat : ∀ i j, EqOn (f i) (f j) (S ∩ (U i ∩ U j))) :
    ∃ g : E → F, ContinuousOn g S ∧ ∀ i, EqOn g (f i) (S ∩ U i) := by
  classical
  let pick := fun x hx => Classical.choose (hcover x hx)
  have hpick (x : E) (hx : x ∈ S) : x ∈ U (pick x hx) := Classical.choose_spec (hcover x hx)
  let g := fun x => if hx : x ∈ S then f (pick x hx) x else 0
  have hg (i : ι) : EqOn g (f i) (S ∩ U i) := by
    intro x hx
    simp only [g,dif_pos hx.1]
    exact hcompat (pick x hx.1) i ⟨hx.1,hpick x hx.1,hx.2⟩
  refine ⟨g,?_,hg⟩
  apply continuousOn_of_locally_continuousOn
  intro x hx
  obtain ⟨i,hi⟩ := hcover x hx
  exact ⟨U i,hU i,hi,(hf i).congr (hg i)⟩

/-- The actual first and second local derivative identities supply the
compatibility automatically. No overlap-compatibility assumption or
boundary extension of the unknown function is required. -/
theorem exists_global_derivative_fields_of_patches {ι : Type*} {S : Set E}
    (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x ∈ S, ∃ i, x ∈ U i)
    (u : E → F) (D : ι → E → E →L[ℝ] F) (H : ι → E → E →L[ℝ] E →L[ℝ] F)
    (hD : ∀ i, ContinuousOn (D i) (S ∩ U i)) (hH : ∀ i, ContinuousOn (H i) (S ∩ U i))
    (hdu : ∀ i x, x ∈ interior S ∩ U i → HasFDerivAt u (D i x) x)
    (hdD : ∀ i x, x ∈ interior S ∩ U i → HasFDerivAt (D i) (H i x) x) :
    ∃ G : E → E →L[ℝ] F, ∃ K : E → E →L[ℝ] E →L[ℝ] F,
      ContinuousOn G S ∧ ContinuousOn K S ∧
      (∀ i, EqOn G (D i) (S ∩ U i)) ∧ (∀ i, EqOn K (H i) (S ∩ U i)) ∧
      (∀ x ∈ interior S, HasFDerivAt u (G x) x) ∧
      (∀ x ∈ interior S, HasFDerivAt G (K x) x) := by
  have hcD (i j : ι) : EqOn (D i) (D j) (S ∩ (U i ∩ U j)) :=
    local_first_fields_compatible hS hSc hint (hU i) (hU j) (hD i) (hD j) (hdu i) (hdu j)
  have hcH (i j : ι) : EqOn (H i) (H j) (S ∩ (U i ∩ U j)) :=
    local_second_fields_compatible hS hSc hint (hU i) (hU j) (hD i) (hD j) (hH i) (hH j)
      (hdu i) (hdu j) (hdD i) (hdD j)
  obtain ⟨G,hGc,hGeq⟩ := exists_continuous_glued_field U hU hcover D hD hcD
  obtain ⟨K,hKc,hKeq⟩ := exists_continuous_glued_field U hU hcover H hH hcH
  refine ⟨G,K,hGc,hKc,hGeq,hKeq,?_,?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := hcover x (interior_subset hx)
    rw [hGeq i ⟨interior_subset hx,hi⟩]
    exact hdu i x ⟨hx,hi⟩
  · intro x hx
    obtain ⟨i,hi⟩ := hcover x (interior_subset hx)
    have he : G =ᶠ[𝓝 x] D i := by
      filter_upwards [(isOpen_interior.inter (hU i)).mem_nhds ⟨hx,hi⟩] with y hy
      exact hGeq i ⟨interior_subset hy.1,hy.2⟩
    rw [hKeq i ⟨interior_subset hx,hi⟩]
    exact (hdD i x ⟨hx,hi⟩).congr_of_eventuallyEq he

/-- Local pairwise Hölder estimates become one global bound through an
actual compact finite cover and its Lebesgue radius. -/
theorem exists_holder_bound_of_glued_patches {ι : Type*} {S : Set E}
    (hSc : IsCompact S) {α : ℝ} (hα : 0 ≤ α)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x ∈ S, ∃ i, x ∈ U i)
    (f : ι → E → F) (g : E → F) (hgc : ContinuousOn g S)
    (heq : ∀ i, EqOn g (f i) (S ∩ U i))
    (hholder : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S ∩ U i, ∀ y ∈ S ∩ U i,
      ‖f i x-f i y‖ ≤ C*(dist x y)^α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ y ∈ S, ‖g x-g y‖ ≤ C*(dist x y)^α := by
  obtain ⟨B,hB⟩ := hSc.exists_bound_of_continuousOn hgc
  obtain ⟨C,hC,hbound⟩ := uniform_holder_of_compact_local_bounds (Γ := Unit) hSc hα
    (fun _ => g) (fun _ => True) (fun _ => 1) (fun _ _ => zero_le_one) (by
      intro a ha
      obtain ⟨i,hi⟩ := hcover a ha
      obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp (hU i) a hi
      obtain ⟨L,hL,hLoc⟩ := hholder i
      refine ⟨r,max (max B 0) L,hr,(le_max_right B 0).trans (le_max_left _ _),?_⟩
      intro unit hunit
      constructor
      · intro x hx hxa
        simpa only [mul_one] using (hB x hx).trans ((le_max_left B 0).trans (le_max_left _ _))
      · intro x hx hxa y hy hya
        have hxU := hrU (show x ∈ Metric.ball a r from hxa)
        have hyU := hrU (show y ∈ Metric.ball a r from hya)
        change ‖g x-g y‖ ≤ max (max B 0) L*1*(dist x y)^α
        rw [heq i ⟨hx,hxU⟩,heq i ⟨hy,hyU⟩]
        exact (hLoc x ⟨hx,hxU⟩ y ⟨hy,hyU⟩).trans (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_right (le_max_right (max B 0) L) (Real.rpow_nonneg dist_nonneg _)))
  refine ⟨C,hC,?_⟩
  simpa only [mul_one] using (hbound () trivial).2

end GaussianTilt.MomentMapLinearDirichlet
