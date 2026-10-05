import GaussianTilt.MomentMapLinearDirichletComposition

/-!
# Absolute-value contraction in the actual Dirichlet Sobolev space

Smooth zero-preserving contractions are applied only to genuine compact
interior tests. Their values converge in L² and their jets remain bounded.
Proved Hilbert weak compactness then supplies the H₀¹ absolute value; the
injective value map gives the sharp norm and energy bounds.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma exists_dirichletCore_sequence {Ω : Set (CoordinateSpace n)} (u : dirichletSobolev Ω) :
    ∃ f : ℕ → dirichletCore Ω, Tendsto (fun k => dirichletCoreToSobolev Ω (f k)) atTop (𝓝 u) := by
  have hmem : u.1 ∈ closure (Set.range (dirichletJet Ω)) := u.2
  obtain ⟨v, hv, hvt⟩ := mem_closure_iff_seq_limit.mp hmem
  choose f hf using hv
  refine ⟨f, tendsto_subtype_rng.mpr ?_⟩
  exact hvt.congr' (Eventually.of_forall (fun k => (hf k).symm))

/-- A sharp bounded lift follows from the proved Hilbert weak compactness
and injectivity of the actual value map. The bounds need hold only eventually. -/
theorem exists_dirichlet_lift_of_eventual_norm_bound {Ω : Set (CoordinateSpace n)}
    (u : ℕ → dirichletSobolev Ω) {f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))} {B : ℝ}
    (hb : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ‖u k‖ ≤ B + ε)
    (hf : Tendsto (fun k => dirichletValue Ω (u k)) atTop (𝓝 f)) :
    ∃ v : dirichletSobolev Ω, dirichletValue Ω v = f ∧ ‖v‖ ≤ B := by
  have hex (ε : ℝ) (hε : 0 < ε) :
      ∃ v : dirichletSobolev Ω, dirichletValue Ω v = f ∧ ‖v‖ ≤ B + ε := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hb ε hε)
    have hshift : Tendsto (fun k : ℕ => k + N) atTop atTop := by
      apply tendsto_atTop.mpr
      intro m
      filter_upwards [eventually_ge_atTop m] with k hk
      omega
    exact exists_hilbert_lift_of_bounded_sequence (dirichletValue Ω) (fun k => u (k + N))
      (fun k => hN (k + N) (by omega)) (hf.comp hshift)
  obtain ⟨v, hv, hvb⟩ := hex 1 zero_lt_one
  refine ⟨v, hv, ?_⟩
  by_contra hnot
  have hpos : 0 < (‖v‖ - B) / 2 := by linarith
  obtain ⟨w, hw, hwb⟩ := hex ((‖v‖ - B) / 2) hpos
  have hweq : w = v := dirichletValue_injective Ω (hw.trans hv.symm)
  rw [hweq] at hwb
  linarith

/-- Absolute value belongs to the actual H₀¹ space and does not increase
its full norm or its genuine gradient energy. No Sobolev chain rule or
Markov-property theorem is assumed. -/
theorem exists_abs_dirichletSobolev {Ω : Set (CoordinateSpace n)} (u : dirichletSobolev Ω) :
    ∃ v : dirichletSobolev Ω, dirichletValue Ω v = |dirichletValue Ω u| ∧
      ‖v‖ ≤ ‖u‖ ∧ dirichletEnergy Ω v v ≤ dirichletEnergy Ω u u := by
  obtain ⟨f, hf⟩ := exists_dirichletCore_sequence u
  let η := fun k => smoothAbs (absRegularizationScale k)
  let c := fun k => composeDirichletCore
    (contDiff_smoothAbs (absRegularizationScale_pos k))
    (smoothAbs_zero (absRegularizationScale_pos k)) (f k)
  let v := fun k => dirichletCoreToSobolev Ω (c k)
  have hvnorm (k : ℕ) : ‖v k‖ ≤ ‖dirichletCoreToSobolev Ω (f k)‖ :=
    norm_smoothCompactJet_compose_le (contDiff_smoothAbs (absRegularizationScale_pos k))
      (smoothAbs_zero (absRegularizationScale_pos k))
      (lipschitzWith_smoothAbs (absRegularizationScale_pos k)) (f k).1
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ‖v k‖ ≤ ‖u‖ + ε := by
    intro ε hε
    filter_upwards [(tendsto_order.mp hf.norm).2 (‖u‖ + ε) (by linarith)] with k hk
    exact (hvnorm k).trans hk.le
  have hbase : Tendsto (fun k => dirichletValue Ω (dirichletCoreToSobolev Ω (f k))) atTop
      (𝓝 (dirichletValue Ω u)) := (dirichletValue Ω).continuous.continuousAt.tendsto.comp hf
  have hcomp := smoothAbs_compLp_tendsto_abs_of_tendsto hbase
  have he (k : ℕ) : dirichletValue Ω (v k) =
      (lipschitzWith_smoothAbs (absRegularizationScale_pos k)).compLp
        (smoothAbs_zero (absRegularizationScale_pos k))
          (dirichletValue Ω (dirichletCoreToSobolev Ω (f k))) :=
    smoothCompactToL2_compose (contDiff_smoothAbs (absRegularizationScale_pos k))
      (smoothAbs_zero (absRegularizationScale_pos k))
      (lipschitzWith_smoothAbs (absRegularizationScale_pos k)) (f k).1
  have hvalue : Tendsto (fun k => dirichletValue Ω (v k)) atTop (𝓝 |dirichletValue Ω u|) :=
    hcomp.congr' (Eventually.of_forall (fun k => (he k).symm))
  obtain ⟨w, hw, hwn⟩ := exists_dirichlet_lift_of_eventual_norm_bound v hbound hvalue
  refine ⟨w, hw, hwn, ?_⟩
  have hsq := pow_le_pow_left₀ (norm_nonneg w) hwn 2
  rw [norm_dirichletSobolev_sq, norm_dirichletSobolev_sq, hw, norm_abs_eq_norm] at hsq
  linarith

end GaussianTilt.MomentMapLinearDirichlet
