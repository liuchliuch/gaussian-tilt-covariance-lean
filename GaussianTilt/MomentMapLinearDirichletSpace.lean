import GaussianTilt.MomentMapLinearDirichletPoincare

/-!
# The actual zero-boundary Sobolev space and derived coercivity

The space is the Hilbert closure of actual smooth compact tests whose
closed support lies inside the domain. The bounded-strip Poincaré estimate
extends through that closure and makes the literal gradient energy coercive.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Actual compactly supported smooth tests interior to the domain. -/
def dirichletCore (Ω : Set (CoordinateSpace n)) : Submodule ℝ (smoothCompactCore n) where
  carrier := {u | tsupport u.1 ⊆ Ω}
  zero_mem' := by
    change tsupport (0 : CoordinateSpace n → ℝ) ⊆ Ω
    simp [tsupport]
  add_mem' := by
    intro u v hu hv
    exact tsupport_add.trans (union_subset hu hv)
  smul_mem' := by
    intro c u hu
    exact (tsupport_smul_subset_right (fun _ => c) u.1).trans hu

/-- The actual L² value/gradient jet of a zero-boundary test. -/
def dirichletJet (Ω : Set (CoordinateSpace n)) :
    dirichletCore Ω →ₗ[ℝ] SobolevJet (volume : Measure (CoordinateSpace n)) :=
  (smoothCompactJet volume).comp (dirichletCore Ω).subtype

/-- H₀¹ as the closed Hilbert graph of the actual interior-supported tests. -/
def dirichletSobolev (Ω : Set (CoordinateSpace n)) :
    Submodule ℝ (SobolevJet (volume : Measure (CoordinateSpace n))) :=
  (LinearMap.range (dirichletJet Ω)).topologicalClosure

instance dirichletSobolev_complete (Ω : Set (CoordinateSpace n)) : CompleteSpace (dirichletSobolev Ω) :=
  (LinearMap.range (dirichletJet Ω)).isClosed_topologicalClosure.completeSpace_coe

/-- Value coordinate of the actual zero-boundary Sobolev jet. -/
def dirichletValue (Ω : Set (CoordinateSpace n)) :
    dirichletSobolev Ω →L[ℝ] Lp ℝ 2 (volume : Measure (CoordinateSpace n)) :=
  (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (volume : Measure (CoordinateSpace n))) 0).comp
    (dirichletSobolev Ω).subtypeL

/-- An actual interior test regarded as an element of its closure. -/
def dirichletCoreToSobolev (Ω : Set (CoordinateSpace n)) : dirichletCore Ω →ₗ[ℝ] dirichletSobolev Ω where
  toFun u := ⟨dirichletJet Ω u, subset_closure ⟨u, rfl⟩⟩
  map_add' u v := Subtype.ext (map_add (dirichletJet Ω) u v)
  map_smul' c u := Subtype.ext (map_smul (dirichletJet Ω) c u)

/-- The actual gradient pairing, written as full Hilbert pairing minus
its value-coordinate pairing. This is a bounded bilinear form. -/
def dirichletEnergy (Ω : Set (CoordinateSpace n)) :
    dirichletSobolev Ω →L[ℝ] dirichletSobolev Ω →L[ℝ] ℝ :=
  (innerSL ℝ : dirichletSobolev Ω →L[ℝ] dirichletSobolev Ω →L[ℝ] ℝ) -
    (innerSL ℝ : Lp ℝ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ] ℝ).bilinearComp
        (dirichletValue Ω) (dirichletValue Ω)

lemma dirichletEnergy_apply (Ω : Set (CoordinateSpace n)) (u v : dirichletSobolev Ω) :
    dirichletEnergy Ω u v = ∑ i : Fin n, inner ℝ (u.1 i.succ) (v.1 i.succ) := by
  change inner ℝ u v - inner ℝ (u.1 0) (v.1 0) = _
  change inner ℝ u.1 v.1 - inner ℝ (u.1 0) (v.1 0) = _
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  ring

lemma dirichletEnergy_self (Ω : Set (CoordinateSpace n)) (u : dirichletSobolev Ω) :
    dirichletEnergy Ω u u = ∑ i : Fin n, ‖u.1 i.succ‖ ^ 2 := by
  rw [dirichletEnergy_apply]
  simp only [real_inner_self_eq_norm_sq]

lemma norm_dirichletSobolev_sq (Ω : Set (CoordinateSpace n)) (u : dirichletSobolev Ω) :
    ‖u‖ ^ 2 = ‖dirichletValue Ω u‖ ^ 2 + dirichletEnergy Ω u u := by
  change ‖u.1‖ ^ 2 = ‖u.1 0‖ ^ 2 + _
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, dirichletEnergy_self]

/-- The proved smooth Poincaré inequality extends to every actual H₀¹ jet. -/
theorem dirichlet_poincare_strip {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R) (u : dirichletSobolev Ω) :
    ‖dirichletValue Ω u‖ ≤ 2 * R * ‖u.1 i.succ‖ := by
  let μ : Measure (CoordinateSpace n) := volume
  have hclosed : IsClosed {v : SobolevJet μ | ‖v 0‖ ≤ 2 * R * ‖v i.succ‖} :=
    isClosed_le (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin (n + 1) => Lp ℝ 2 μ) 0).continuous.norm
      (continuous_const.mul (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin (n + 1) => Lp ℝ 2 μ) i.succ).continuous.norm)
  have hcore : (LinearMap.range (dirichletJet Ω) : Set (SobolevJet μ)) ⊆
      {v | ‖v 0‖ ≤ 2 * R * ‖v i.succ‖} := by
    rintro _ ⟨f, rfl⟩
    exact smoothCompact_poincare_strip f.1 i hR (fun x hx => hΩ x (f.2 hx))
  exact (closure_minimal hcore hclosed) u.2

/-- The full H¹ norm is quantitatively controlled by the actual gradient
energy on a bounded domain. -/
theorem dirichlet_norm_sq_le_energy {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R) (u : dirichletSobolev Ω) :
    ‖u‖ ^ 2 ≤ (1 + 4 * R ^ 2) * dirichletEnergy Ω u u := by
  have hp := dirichlet_poincare_strip i hR hΩ u
  have hsquare := pow_le_pow_left₀ (norm_nonneg (dirichletValue Ω u)) hp 2
  have hi : ‖u.1 i.succ‖ ^ 2 ≤ dirichletEnergy Ω u u := by
    rw [dirichletEnergy_self]
    exact Finset.single_le_sum (f := fun j : Fin n => ‖u.1 j.succ‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hscale := mul_le_mul_of_nonneg_left hi (show 0 ≤ 4 * R ^ 2 by positivity)
  rw [norm_dirichletSobolev_sq]
  nlinarith

/-- Coercivity is a theorem derived from the actual bounded-domain
Poincaré estimate, ready for the genuine Lax--Milgram construction. -/
theorem dirichletEnergy_isCoercive {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R) : IsCoercive (dirichletEnergy Ω) := by
  have hD : 0 < 1 + 4 * R ^ 2 := by positivity
  refine ⟨(1 + 4 * R ^ 2)⁻¹, inv_pos.mpr hD, ?_⟩
  intro u
  calc
    (1 + 4 * R ^ 2)⁻¹ * ‖u‖ * ‖u‖ = ‖u‖ ^ 2 / (1 + 4 * R ^ 2) := by ring
    _ ≤ dirichletEnergy Ω u u := (div_le_iff₀ hD).mpr (by
      simpa only [mul_comm] using dirichlet_norm_sq_le_energy i hR hΩ u)

end GaussianTilt.MomentMapLinearDirichlet
