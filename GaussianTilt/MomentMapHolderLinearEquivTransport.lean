import GaussianTilt.MomentMapHolderChartComposition

/-! # Value-faithful two-sided norm transport of Dirichlet jets

A genuine linear coordinate equivalence transports compatible jets and
zero boundary values. The reverse norm bound follows from actual jet
faithfulness, rather than independently assigning derivative fields.
-/
noncomputable section
set_option maxHeartbeats 2000000
open Set
open scoped ContDiff BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_zeroBoundary_linearEquiv_transport
    {S : Set F} {T : Set E} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hSc : IsCompact S) (hTc : IsCompact T)
    (hSi : (interior S).Nonempty) (hTi : (interior T).Nonempty)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (e : E ≃L[ℝ] F) (hTS : e '' T = S) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ J : zeroBoundary F ℝ hS α,
      ∃ j : zeroBoundary E ℝ hT α,
        ‖j‖ ≤ C*‖J‖ ∧ ‖J‖ ≤ D*‖j‖ ∧
        (∀ x : T, value T ℝ α (jetValue E ℝ hT α j.1) x =
          extendValue α (jetValue F ℝ hS α J.1) (e x)) ∧
        (∀ x : T, value T (E →L[ℝ] ℝ) α (jetFirst E ℝ hT α j.1) x =
          chartFirst (extendValue α (jetFirst F ℝ hS α J.1)) e x) ∧
        (∀ x : T, value T (E →L[ℝ] E →L[ℝ] ℝ) α (jetSecond E ℝ hT α j.1) x =
          chartSecond (extendValue α (jetFirst F ℝ hS α J.1))
            (extendValue α (jetSecond F ℝ hS α J.1)) e x) := by
  have hm : MapsTo e T S := by intro x hx; rw [← hTS]; exact mem_image_of_mem e hx
  have hm' : MapsTo e.symm S T := by
    intro x hx
    rw [← hTS] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    simpa using hy
  have hTiS : e '' interior T = interior S := by
    rw [← hTS]
    exact e.toHomeomorph.image_interior T
  have hmi : MapsTo e (interior T) (interior S) := by
    intro x hx; rw [← hTiS]; exact mem_image_of_mem e hx
  have hmi' : MapsTo e.symm (interior S) (interior T) := by
    intro x hx
    rw [← hTiS] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    simpa using hy
  have hfront : MapsTo e (frontier T) (frontier S) := by
    intro x hx
    have hf : e '' frontier T = frontier (e '' T) := e.toHomeomorph.image_frontier T
    rw [← hTS, ← hf]
    exact mem_image_of_mem e hx
  obtain ⟨C,hC,hforward⟩ := exists_jet_smooth_chart_composition hS hT hTc hTi hα hα1 e e.contDiff hm hmi
  obtain ⟨D,hD,hreverse⟩ := exists_jet_smooth_chart_composition hT hS hSc hSi hα hα1 e.symm e.symm.contDiff hm' hmi'
  refine ⟨C,D,hC,hD,?_⟩
  intro J
  obtain ⟨j,hjn,hjv,hjD,hjH⟩ := hforward J.1
  have hjzero : j ∈ zeroBoundary E ℝ hT α := by
    simp only [zeroBoundary,Submodule.mem_iInf,LinearMap.mem_ker]
    intro x
    change value T ℝ α (jetValue E ℝ hT α j) x.1 = 0
    rw [hjv x.1]
    exact zeroBoundary_value hS hSc.isClosed α J (hfront x.2)
  obtain ⟨k,hkn,hkv,hkD,hkH⟩ := hreverse j
  have hke : k = J.1 := by
    apply jetValue_injective hS hSi hα
    apply value_injective S ℝ α
    apply BoundedContinuousFunction.ext
    intro x
    rw [hkv x,extendValue_mem α _ (hm' x.2),hjv ⟨e.symm x,hm' x.2⟩]
    simp only [e.apply_symm_apply,extendValue_mem α _ x.2]
  refine ⟨⟨j,hjzero⟩,hjn,?_,hjv,hjD,hjH⟩
  simpa only [hke] using hkn

end GaussianTilt.HolderSpace
