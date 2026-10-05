import GaussianTilt.MomentMapLinearDirichletComparison
import GaussianTilt.EllipticRegularitySobolevProduct
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Actual compact localization in the zero-boundary Sobolev space

Domain inclusions and multiplication by smooth interior cutoffs are proved
on the genuine compact cores and extended by continuity. A Sobolev jet
whose value vanishes off a compact interior set therefore belongs to H₀¹
of that domain, without an assumed trace or support characterization.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal Manifold
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma dirichletSobolev_mono {Ω U : Set (CoordinateSpace n)} (h : Ω ⊆ U) :
    dirichletSobolev Ω ≤ dirichletSobolev U := by
  apply Submodule.topologicalClosure_mono
  rintro _ ⟨f, rfl⟩
  exact ⟨⟨f.1, f.2.trans h⟩, rfl⟩

/-- The inclusion preserves the actual value and all derivative coordinates. -/
def dirichletInclusion {Ω U : Set (CoordinateSpace n)} (h : Ω ⊆ U) :
    dirichletSobolev Ω →L[ℝ] dirichletSobolev U :=
  (Submodule.inclusion (dirichletSobolev_mono h)).mkContinuous 1 (by
    intro u
    simp)

@[simp] lemma dirichletInclusion_value {Ω U : Set (CoordinateSpace n)} (h : Ω ⊆ U)
    (u : dirichletSobolev Ω) : dirichletValue U (dirichletInclusion h u) = dirichletValue Ω u := rfl

@[simp] lemma norm_dirichletInclusion {Ω U : Set (CoordinateSpace n)} (h : Ω ⊆ U)
    (u : dirichletSobolev Ω) : ‖dirichletInclusion h u‖ = ‖u‖ := rfl

lemma exists_smooth_interior_cutoff {Ω K : Set (CoordinateSpace n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ χ : smoothCompactCore n, tsupport χ.1 ⊆ Ω ∧ EqOn χ.1 1 K := by
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_smooth_zero_one_nhds_of_isClosed
    𝓘(ℝ, CoordinateSpace n) hΩ.isClosed_compl hK.isClosed
      (disjoint_left.mpr (fun x hx hxK => hx (hKΩ hxK)))
  have hs : tsupport (f : CoordinateSpace n → ℝ) ⊆ Ω := by
    intro x hx
    by_contra hxΩ
    have hz : ∀ᶠ y in 𝓝 x, f y = 0 := hf0.filter_mono (nhds_le_nhdsSet hxΩ)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx
  have hc : HasCompactSupport (f : CoordinateSpace n → ℝ) :=
    (hΩb.subset hs).isCompact_closure.of_isClosed_subset (isClosed_tsupport _) subset_closure
  exact ⟨⟨f, f.contMDiff.contDiff, hc⟩, hs,
    fun x hx => hf1.self_of_nhdsSet x hx⟩

/-- Compact interior multiplication lands in the actual smaller Dirichlet
space, even when the input is a jet on a larger domain. -/
theorem exists_dirichletSobolev_mul_cutoff {Ω U : Set (CoordinateSpace n)}
    (a : smoothCompactCore n) (haΩ : tsupport a.1 ⊆ Ω) (u : dirichletSobolev U) :
    ∃ v : dirichletSobolev Ω,
      (dirichletValue Ω v =ᵐ[volume] fun x => a.1 x * dirichletValue U u x) ∧
      ∀ i, v.1 i.succ =ᵐ[volume] fun x =>
        a.1 x * u.1 i.succ x + coordinateDerivative i a.1 x * dirichletValue U u x := by
  let μ : Measure (CoordinateSpace n) := volume
  obtain ⟨B, hB⟩ := a.2.2.exists_bound_of_continuous a.2.1.continuous
  have hd (i : Fin n) : ∃ D, ∀ x, ‖coordinateDerivative i a.1 x‖ ≤ D :=
    (a.2.2.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).exists_bound_of_continuous
      (smooth_coordinateDerivative a.2.1 i).continuous
  choose D hD using hd
  let M := boundedL2Multiplier a.2.1.continuous.aestronglyMeasurable
    ((norm_nonneg (a.1 0)).trans (hB 0)) (ae_of_all μ hB) (μ := μ)
  let MD := fun i => boundedL2Multiplier (smooth_coordinateDerivative a.2.1 i).continuous.aestronglyMeasurable
    ((norm_nonneg (coordinateDerivative i a.1 0)).trans (hD i 0)) (ae_of_all μ (hD i)) (μ := μ)
  have hM (f : Lp ℝ 2 μ) : M f =ᵐ[μ] fun x => a.1 x * f x := boundedL2Multiplier_ae _ _ _ _
  have hMD (i : Fin n) (f : Lp ℝ 2 μ) : MD i f =ᵐ[μ] fun x => coordinateDerivative i a.1 x * f x :=
    boundedL2Multiplier_ae _ _ _ _
  let T := sobolevJetMultiply M MD
  have hclosed : IsClosed (T ⁻¹' (dirichletSobolev Ω : Set (SobolevJet μ))) :=
    (LinearMap.range (dirichletJet Ω)).isClosed_topologicalClosure.preimage T.continuous
  have hcore : (LinearMap.range (dirichletJet U) : Set (SobolevJet μ)) ⊆
      T ⁻¹' (dirichletSobolev Ω : Set (SobolevJet μ)) := by
    rintro _ ⟨f, rfl⟩
    change T (smoothCompactJet μ f.1) ∈ dirichletSobolev Ω
    rw [show T (smoothCompactJet μ f.1) = smoothCompactJet μ (smoothCompactMultiply a.2.1 f.1) from
      sobolevJetMultiply_core a.2.1 (Measure.AbsolutelyContinuous.refl μ) M MD hM hMD f.1]
    apply (LinearMap.range (dirichletJet Ω)).le_topologicalClosure
    refine ⟨⟨smoothCompactMultiply a.2.1 f.1, ?_⟩, rfl⟩
    exact tsupport_mul_subset_left.trans haΩ
  let v : dirichletSobolev Ω := ⟨T u.1, closure_minimal hcore hclosed u.2⟩
  refine ⟨v, hM (u.1 0), ?_⟩
  intro i
  filter_upwards [Lp.coeFn_add (M (u.1 i.succ)) (MD i (u.1 0)), hM (u.1 i.succ), hMD i (u.1 0)] with x hx hm hd
  change (M (u.1 i.succ) + MD i (u.1 0)) x = _
  simpa only [Pi.add_apply, hm, hd] using hx

/-- A compact interior support condition on the actual value suffices to
put an ambient Sobolev jet in the genuine H₀¹ closure. -/
theorem dirichletSobolev_mem_of_compact_value_support {Ω U K : Set (CoordinateSpace n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΩU : Ω ⊆ U)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (u : dirichletSobolev U)
    (hu : ∀ᵐ x ∂volume, x ∉ K → dirichletValue U u x = 0) :
    u.1 ∈ dirichletSobolev Ω := by
  obtain ⟨a, haΩ, haK⟩ := exists_smooth_interior_cutoff hΩ hΩb hK hKΩ
  obtain ⟨v, hv, _⟩ := exists_dirichletSobolev_mul_cutoff a haΩ u
  have he : dirichletValue U (dirichletInclusion hΩU v) = dirichletValue U u := by
    apply Lp.ext
    filter_upwards [hv, hu] with x hx hux
    change dirichletValue Ω v x = dirichletValue U u x
    rw [hx]
    by_cases hxK : x ∈ K
    · rw [haK hxK]; simp
    · rw [hux hxK, mul_zero]
  have heq := dirichletValue_injective U he
  have hj := congrArg (fun z : dirichletSobolev U => z.1) heq
  change v.1 = u.1 at hj
  rw [← hj]
  exact v.2

end GaussianTilt.MomentMapLinearDirichlet
