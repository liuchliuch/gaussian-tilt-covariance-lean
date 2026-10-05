import GaussianTilt.NegativeSobolevSpace
import Mathlib.Analysis.Normed.Module.WeakDual

/-! # Bounded Hilbert lifts and actual Sobolev limits

Banach–Alaoglu and the Riesz representation theorem construct a bounded lift
of a strong limit of projected Hilbert-space vectors. Applied to the actual
closed Sobolev graph this gives the weak compactness step of local elliptic
regularity without assuming a Sobolev representative exists.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal

namespace GaussianTilt.Letwin

lemma mapClusterPt_eq_of_tendsto {α Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {l : Filter α} {u : α → Y} {a b : Y}
    (hc : MapClusterPt a l u) (ht : Tendsto u l (𝓝 b)) : a = b := by
  letI : NeBot (𝓝 a ⊓ map u l) := hc
  apply tendsto_nhds_unique
    (f := id) (l := 𝓝 a ⊓ map u l)
  · simpa only [tendsto_id'] using (inf_le_left : 𝓝 a ⊓ map u l ≤ 𝓝 a)
  · simpa only [tendsto_id'] using
      ((inf_le_right : 𝓝 a ⊓ map u l ≤ map u l).trans ht)

/-- Bounded lifts of a strongly convergent projected sequence admit a
genuine Hilbert-space lift, with the same norm bound. -/
theorem exists_hilbert_lift_of_bounded_sequence
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (A : H →L[ℝ] K) (u : ℕ → H) {f : K} {B : ℝ}
    (hb : ∀ j, ‖u j‖ ≤ B) (hf : Tendsto (fun j ↦ A (u j)) atTop (𝓝 f)) :
    ∃ v : H, A v = f ∧ ‖v‖ ≤ B := by
  let w : ℕ → WeakDual ℝ H := fun j ↦ StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ H) (u j))
  have hw : ∀ j, w j ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) B := by
    intro j
    change ‖(InnerProductSpace.toDual ℝ H) (u j) - 0‖ ≤ B
    simpa only [sub_zero, LinearIsometryEquiv.norm_map] using hb j
  obtain ⟨w₀, hw₀, hc⟩ := (WeakDual.isCompact_closedBall ℝ (0 : StrongDual ℝ H) B).exists_mapClusterPt
    (show map w atTop ≤ 𝓟 (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) B) from
      le_principal_iff.mpr (eventually_map.mpr (Eventually.of_forall hw)))
  let v : H := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual w₀)
  refine ⟨v, ?_, ?_⟩
  · apply ext_inner_right ℝ
    intro y
    have hcl := hc.continuousAt_comp (WeakDual.eval_continuous (A.adjoint y)).continuousAt
    have hlim : Tendsto (fun j ↦ (w j) (A.adjoint y)) atTop (𝓝 (inner ℝ f y)) := by
      have h : Tendsto (fun j ↦ inner ℝ (A (u j)) y) atTop (𝓝 (inner ℝ f y)) :=
        hf.inner tendsto_const_nhds
      have heval (j : ℕ) : (w j) (A.adjoint y) = inner ℝ (A (u j)) y := by
        change ((InnerProductSpace.toDual ℝ H) (u j)) (A.adjoint y) = _
        rw [InnerProductSpace.toDual_apply, A.adjoint_inner_right]
      exact h.congr' (Eventually.of_forall (fun j ↦ (heval j).symm))
    have heq := mapClusterPt_eq_of_tendsto hcl hlim
    calc
      inner ℝ (A v) y = inner ℝ v (A.adjoint y) := (A.adjoint_inner_right v y).symm
      _ = (WeakDual.toStrongDual w₀) (A.adjoint y) := InnerProductSpace.toDual_symm_apply
      _ = inner ℝ f y := heq
  · change ‖(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual w₀)‖ ≤ B
    rw [LinearIsometryEquiv.norm_map]
    simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using hw₀

/-- Uniformly bounded actual smooth jets whose values converge in L² have
an actual value/gradient representative in the closed Sobolev graph. -/
theorem exists_weightedSobolev_of_bounded_smooth_jets {n : ℕ}
    (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ]
    (u : ℕ → smoothCompactCore n) {f : Lp ℝ 2 μ} {B : ℝ}
    (hb : ∀ j, ‖smoothCompactJet μ (u j)‖ ≤ B)
    (hf : Tendsto (fun j ↦ smoothCompactToL2 μ (u j)) atTop (𝓝 f)) :
    ∃ v : weightedSobolev μ, weightedSobolevValue μ v = f ∧ ‖v‖ ≤ B := by
  let v : ℕ → weightedSobolev μ := fun j ↦ ⟨smoothCompactJet μ (u j),
    (LinearMap.range (smoothCompactJet μ)).le_topologicalClosure ⟨u j, rfl⟩⟩
  exact exists_hilbert_lift_of_bounded_sequence (weightedSobolevValue μ) v hb hf

end GaussianTilt.Letwin
