import Mathlib

/-! # Linear method of continuity from the actual uniform inverse estimate

This Banach-space argument needs no assumed elliptic solvability theorem.
The separate PDE estimates must supply the displayed coercive bound and
the actual starting inverse.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapLinearDirichlet
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma isOpen_bijective_continuousLinearMaps :
    IsOpen {L : X →L[ℝ] Y | Function.Bijective L} := by
  have he : {L : X →L[ℝ] Y | Function.Bijective L} =
      range (fun e : X ≃L[ℝ] Y => (e : X →L[ℝ] Y)) := by
    ext L
    constructor
    · intro hL
      exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hL.1)
        (LinearMap.range_eq_top.mpr hL.2), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
    · rintro ⟨e, rfl⟩
      exact e.bijective
  rw [he]
  exact ContinuousLinearEquiv.isOpen

/-- Operator-norm limits preserve surjectivity when their genuine inverse
estimates are uniform. The range is actually closed by the limiting bound;
fixed right-hand-side preimages have genuinely vanishing limiting residuals. -/
theorem surjective_of_tendsto_operators_of_uniform_bound
    {L : ℕ → X →L[ℝ] Y} {A : X →L[ℝ] Y}
    (hL : Tendsto L atTop (𝓝 A)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ k x, ‖x‖ ≤ C * ‖L k x‖)
    (hA : ∀ x, ‖x‖ ≤ C * ‖A x‖)
    (hsurj : ∀ k, Function.Surjective (L k)) : Function.Surjective A := by
  have ha : AntilipschitzWith ⟨C, hC⟩ A := A.antilipschitz_of_bound hA
  have hrange : IsClosed (range A) := ha.isClosed_range A.uniformContinuous
  intro y
  choose u hu using fun k => hsurj k y
  have hub (k : ℕ) : ‖u k‖ ≤ C * ‖y‖ := by simpa only [hu] using hbound k (u k)
  have hconv : Tendsto (fun k => A (u k)) atTop (𝓝 y) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have ht : Tendsto (fun k => ‖A - L k‖ * (C * ‖y‖)) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero, zero_mul] using
        (((tendsto_const_nhds (x := A)).sub hL).norm.mul_const (C * ‖y‖))
    apply squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) ht
    have he : A (u k) - y = (A - L k) (u k) := by simp only [ContinuousLinearMap.sub_apply, hu]
    rw [he]
    exact ((A - L k).le_opNorm (u k)).trans
      (mul_le_mul_of_nonneg_left (hub k) (norm_nonneg _))
  exact hrange.mem_of_tendsto hconv (Eventually.of_forall (fun k => mem_range_self (u k)))

/-- The full linear continuation theorem. Its two real PDE inputs are the
uniform coercive estimate and the starting operator's surjectivity. -/
theorem linear_dirichlet_method_of_continuity
    (L : ℝ → X →L[ℝ] Y) (hL : Continuous L) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖x‖ ≤ C * ‖L t x‖)
    (hzero : Function.Surjective (L 0)) :
    ∀ t ∈ Icc (0 : ℝ) 1, Function.Bijective (L t) := by
  have hinj (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Function.Injective (L t) :=
    (show AntilipschitzWith ⟨C, hC⟩ (L t) from (L t).antilipschitz_of_bound (hbound t ht)).injective
  let T : Set (Icc (0 : ℝ) 1) := {t | Function.Bijective (L t)}
  have hopen : IsOpen T := isOpen_bijective_continuousLinearMaps.preimage
    (hL.comp continuous_subtype_val)
  have hclosed : IsClosed T := by
    apply isSeqClosed_iff_isClosed.mp
    intro s t hs ht
    have hsL : Tendsto (fun k => L (s k)) atTop (𝓝 (L t)) :=
      ((hL.comp continuous_subtype_val).tendsto t).comp ht
    refine ⟨hinj t t.2, ?_⟩
    exact surjective_of_tendsto_operators_of_uniform_bound hsL hC
      (fun k => hbound (s k) (s k).2) (hbound t t.2) (fun k => (hs k).2)
  have hne : T.Nonempty := ⟨⟨0, by norm_num⟩, hinj 0 (by norm_num), hzero⟩
  have hall : T = univ := (show IsClopen T from ⟨hclosed, hopen⟩).eq_univ hne
  intro t ht
  have hm : (⟨t, ht⟩ : Icc (0 : ℝ) 1) ∈ T := by rw [hall]; trivial
  exact hm

end GaussianTilt.MomentMapLinearDirichlet
