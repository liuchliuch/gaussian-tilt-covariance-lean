import GaussianTilt.MomentMapLinearDirichletLocalization

/-!
# The genuine Dirichlet space is an order ideal

Positive parts of an interior compact core minus a nonnegative ambient
Sobolev function have compact interior value support. Localization and
weak compactness then pass this fact to all H₀¹ functions. This supplies
actual admissible truncations for nonzero-boundary barriers.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

def dirichletPositivePart {Ω : Set (CoordinateSpace n)} (u : dirichletSobolev Ω) :
    dirichletSobolev Ω := (exists_positivePart_dirichletSobolev u).choose

lemma dirichletPositivePart_value {Ω : Set (CoordinateSpace n)} (u : dirichletSobolev Ω) :
    dirichletValue Ω (dirichletPositivePart u) =
      (2 : ℝ)⁻¹ • (dirichletValue Ω u + |dirichletValue Ω u|) :=
  (exists_positivePart_dirichletSobolev u).choose_spec.1

lemma dirichletPositivePart_nonneg {Ω : Set (CoordinateSpace n)} (u : dirichletSobolev Ω) :
    0 ≤ dirichletValue Ω (dirichletPositivePart u) :=
  (exists_positivePart_dirichletSobolev u).choose_spec.2.1

lemma dirichletPositivePart_energy {Ω : Set (CoordinateSpace n)} (u : dirichletSobolev Ω) :
    dirichletEnergy Ω (dirichletPositivePart u) (dirichletPositivePart u) ≤
      dirichletEnergy Ω u (dirichletPositivePart u) :=
  (exists_positivePart_dirichletSobolev u).choose_spec.2.2

lemma dirichletPositivePart_ae {Ω : Set (CoordinateSpace n)} (u : dirichletSobolev Ω) :
    dirichletValue Ω (dirichletPositivePart u) =ᵐ[volume]
      fun x => (dirichletValue Ω u x + |dirichletValue Ω u x|) / 2 := by
  rw [dirichletPositivePart_value]
  filter_upwards [Lp.coeFn_smul ((2 : ℝ)⁻¹) (dirichletValue Ω u + |dirichletValue Ω u|),
    Lp.coeFn_add (dirichletValue Ω u) |dirichletValue Ω u|,
    Lp.coeFn_abs (dirichletValue Ω u)] with x hx hy hz
  simp only [hx, hy, hz, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

lemma norm_dirichletPositivePart_le {Ω : Set (CoordinateSpace n)} (u : dirichletSobolev Ω) :
    ‖dirichletPositivePart u‖ ≤ ‖u‖ := by
  obtain ⟨a, ha, hnorm, _⟩ := exists_abs_dirichletSobolev u
  have he : dirichletPositivePart u = (2 : ℝ)⁻¹ • (u + a) := by
    apply dirichletValue_injective Ω
    simp [dirichletPositivePart_value, ha]
  have hnormc : ‖(2 : ℝ)⁻¹‖ = 1 / 2 := by norm_num
  rw [he, norm_smul, hnormc]
  have hadd := norm_add_le u a
  linarith

/-- For bounded open Ω, the positive part of u-v really has zero boundary
when u belongs to H₀¹(Ω) and v is a nonnegative ambient H₀¹ function. -/
theorem dirichletPositivePart_sub_mem {Ω U : Set (CoordinateSpace n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΩU : Ω ⊆ U)
    (u : dirichletSobolev Ω) (v : dirichletSobolev U)
    (hv : 0 ≤ dirichletValue U v) :
    (dirichletPositivePart (dirichletInclusion hΩU u - v)).1 ∈ dirichletSobolev Ω := by
  obtain ⟨f, hf⟩ := exists_dirichletCore_sequence u
  let q := fun k => dirichletInclusion hΩU (dirichletCoreToSobolev Ω (f k)) - v
  let p := fun k => dirichletPositivePart (q k)
  have hp (k : ℕ) : (p k).1 ∈ dirichletSobolev Ω := by
    apply dirichletSobolev_mem_of_compact_value_support hΩ hΩb hΩU
      (f k).1.2.2 (f k).2 (p k)
    filter_upwards [dirichletPositivePart_ae (q k),
      Lp.coeFn_sub (dirichletValue Ω (dirichletCoreToSobolev Ω (f k))) (dirichletValue U v),
      smoothCompactToL2_ae volume (f k).1, (Lp.coeFn_nonneg _).mpr hv] with x hx hsub hfx hvx hxK
    have heq : dirichletValue U (q k) x = (f k).1.1 x - dirichletValue U v x := by
      change (dirichletValue Ω (dirichletCoreToSobolev Ω (f k)) - dirichletValue U v) x = _
      rw [hsub]
      change smoothCompactToL2 volume (f k).1 x - _ = _
      rw [hfx]
    rw [hx, heq, image_eq_zero_of_notMem_tsupport hxK, zero_sub,
      abs_of_nonpos (neg_nonpos.mpr hvx)]
    ring
  let w := fun k => (⟨(p k).1, hp k⟩ : dirichletSobolev Ω)
  have hqt : Tendsto q atTop (𝓝 (dirichletInclusion hΩU u - v)) :=
    ((dirichletInclusion hΩU).continuous.continuousAt.tendsto.comp hf).sub_const v
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ‖w k‖ ≤ ‖dirichletInclusion hΩU u - v‖ + ε := by
    intro ε hε
    filter_upwards [(tendsto_order.mp hqt.norm).2 (‖dirichletInclusion hΩU u - v‖ + ε) (by linarith)] with k hk
    exact (norm_dirichletPositivePart_le (q k)).trans hk.le
  have hval := (dirichletValue U).continuous.continuousAt.tendsto.comp hqt
  have hpt : Tendsto (fun k => dirichletValue Ω (w k)) atTop
      (𝓝 (dirichletValue U (dirichletPositivePart (dirichletInclusion hΩU u - v)))) := by
    have habs : Tendsto (fun k => |dirichletValue U (q k)|) atTop
        (𝓝 |dirichletValue U (dirichletInclusion hΩU u - v)|) := by
      simpa only [abs] using hval.sup_nhds hval.neg
    have hh := (hval.add habs).const_smul ((2 : ℝ)⁻¹)
    dsimp only [Function.comp_def] at hh
    simp_rw [← dirichletPositivePart_value] at hh
    exact hh
  obtain ⟨z, hz, _⟩ := exists_dirichlet_lift_of_eventual_norm_bound w hbound hpt
  have he := dirichletValue_injective U (show
      dirichletValue U (dirichletInclusion hΩU z) =
        dirichletValue U (dirichletPositivePart (dirichletInclusion hΩU u - v)) from hz)
  have hj := congrArg (fun a : dirichletSobolev U => a.1) he
  change z.1 = (dirichletPositivePart (dirichletInclusion hΩU u - v)).1 at hj
  rw [← hj]
  exact z.2

end GaussianTilt.MomentMapLinearDirichlet
