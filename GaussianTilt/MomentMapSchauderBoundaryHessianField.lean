import GaussianTilt.MomentMapSchauderBoundaryGluing

/-! # A genuine Hölder Hessian field on the closed flat half-ball -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2600000
open Set InnerProductSpace
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def flatClosedPatch (j : Fin n) (R : ℝ) : Set (KernelSpace n) :=
  Metric.closedBall 0 R ∩ {x | 0 ≤ x j}

def flatSecondField (j : Fin n) (u : KernelSpace n → ℝ)
    (T : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n) (x : KernelSpace n) :
    KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ :=
  if 0 < x j then fderiv ℝ (fderiv ℝ u) x else operatorBilinear (T (flatProjection j x))

/-- The actual boundary polynomial data are exactly the output of the
constructed half-ball approximation theorem. No derivative field is supplied. -/
structure FlatPolynomialData (j : Fin n) (u f : KernelSpace n → ℝ) (α M : ℝ)
    (p : KernelSpace n → KernelSpace n) (T : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n) : Prop where
  symmetric : ∀ a, ‖a‖ ≤ 1 → a j=0 → ∀ v w, inner ℝ (T a v) w=inner ℝ v (T a w)
  first_bound : ∀ a, ‖a‖ ≤ 1 → a j=0 → ‖p a‖ ≤ M
  second_bound : ∀ a, ‖a‖ ≤ 1 → a j=0 → ‖T a‖ ≤ M
  equation : ∀ a, ‖a‖ ≤ 1 → a j=0 → ∀ h, kernelLaplacian (quadraticJet 0 (p a) 0 (T a)) h= -f a
  remainder : ∀ a, ‖a‖ ≤ 1 → a j=0 → ∀ h, ‖h‖ ≤ 1/4 → 0 ≤ h j →
    |u (a+h)-quadraticJet 0 (p a) 0 (T a) h| ≤ M*‖h‖^(2+α)

lemma flat_patch_norm {j : Fin n} {R : ℝ} {x : KernelSpace n} (hx : x ∈ flatClosedPatch j R) : ‖x‖ ≤ R := by
  simpa only [Metric.mem_closedBall,dist_zero_right] using hx.1

/-- The local C² Poisson equation and actual boundary approximations
construct a continuous Hölder extension of the true interior Hessian. -/
theorem exists_flat_second_field_bounds [NeZero n] {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin n) (u f : KernelSpace n → ℝ),
      ContDiffOn ℝ 2 u (flatUpperBall j 2) → Continuous f →
      (∀ x ∈ flatUpperBall j 2, kernelLaplacian u x= -f x) →
      ∀ M H : ℝ, 0 ≤ M → 0 ≤ H → (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) →
      ∀ p T, FlatPolynomialData j u f α M p T →
      (∀ x ∈ flatClosedPatch j (1/16), ‖flatSecondField j u T x‖ ≤ C*(M+H)) ∧
      (∀ x ∈ flatClosedPatch j (1/32), ∀ y ∈ flatClosedPatch j (1/32),
        ‖flatSecondField j u T x-flatSecondField j u T y‖ ≤ C*(M+H)*‖x-y‖^α) ∧
      ContinuousOn (flatSecondField j u T) (flatClosedPatch j (1/32)) := by
  obtain ⟨K,hK,hconv⟩ := exists_flat_boundary_interior_jet_convergence (n := n) hα hα1
  let J := 128*(2:ℝ)^(2+α)*2^α
  let C := K+1+K*(128^α+129^α)+J
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro j u f hu hf heq M H hM hH hfH p T hp
  let B := fun x => operatorBilinear (T (flatProjection j x))
  have hproj (x : KernelSpace n) (hx : x ∈ flatClosedPatch j (1/16)) : ‖flatProjection j x‖ ≤ 1 := by
    have hn := norm_flatProjection_le j x
    have hx' := flat_patch_norm hx
    linarith
  have hsmall : flatClosedPatch j (1/32) ⊆ flatClosedPatch j (1/16) := by
    intro x hx
    exact ⟨Metric.closedBall_subset_closedBall (by norm_num) hx.1,hx.2⟩
  have hlim (x : KernelSpace n) (hx : x ∈ flatClosedPatch j (1/16)) (hxj : 0 < x j) :=
    hconv j u f hu hf heq M H hM hH hfH (flatProjection j x) (p (flatProjection j x)) (T (flatProjection j x))
      (hproj x hx) (flatProjection_plane j x) (hp.symmetric _ (hproj x hx) (flatProjection_plane j x))
      (hp.equation _ (hproj x hx) (flatProjection_plane j x)) (hp.remainder _ (hproj x hx) (flatProjection_plane j x))
      x (x j) hxj (by
        have hh : |x j| ≤ ‖x‖ := PiLp.norm_apply_le x j
        rw [abs_of_pos hxj] at hh
        have hn := flat_patch_norm hx
        linarith) rfl (by rw [norm_sub_flatProjection_eq,abs_of_pos hxj])
  have herror : ∀ x ∈ flatClosedPatch j (1/16), ‖flatSecondField j u T x-B x‖ ≤ K*(M+H)*(x j)^α := by
    intro x hx
    by_cases hxj : 0 < x j
    · simpa only [flatSecondField,if_pos hxj,B] using (hlim x hx hxj).2.1
    · simp only [flatSecondField,if_neg hxj,B,sub_self,norm_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg hx.2 α)
  have hB : ∀ x ∈ flatClosedPatch j (1/16), ‖B x‖ ≤ M := by
    intro x hx
    rw [show B x=operatorBilinear (T (flatProjection j x)) from rfl,norm_operatorBilinear]
    exact hp.second_bound _ (hproj x hx) (flatProjection_plane j x)
  have hsup : ∀ x ∈ flatClosedPatch j (1/16), ‖flatSecondField j u T x‖ ≤ (K+1)*(M+H) := by
    intro x hx
    have hh : (x j)^α ≤ 1 := Real.rpow_le_one hx.2 (by
      have ht := le_abs_self (x j)
      have hc : |x j| ≤ ‖x‖ := PiLp.norm_apply_le x j
      have hn := flat_patch_norm hx
      linarith) hα.le
    have h1 := (herror x hx).trans (mul_le_of_le_one_right (by positivity) hh)
    have h2 : ‖flatSecondField j u T x‖ ≤ ‖flatSecondField j u T x-B x‖+‖B x‖ := by
      simpa only [sub_add_cancel] using norm_add_le (flatSecondField j u T x-B x) (B x)
    nlinarith [hB x hx]
  have hboundary : ∀ x ∈ flatClosedPatch j (1/32), ∀ y ∈ flatClosedPatch j (1/32),
      ‖B x-B y‖ ≤ (J*(M+H))*‖x-y‖^α := by
    intro x hx y hy
    let a := flatProjection j x
    let b := flatProjection j y
    by_cases hab : a=b
    · simp only [B,show flatProjection j x=flatProjection j y from hab,sub_self,norm_zero]
      positivity
    · have hd : 0 < ‖a-b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
      have hdist : ‖a-b‖ ≤ 2*‖x-y‖ := flatProjection_lipschitz j x y
      have hdr : 2*‖a-b‖ ≤ 1/4 := by
        have hx' := flat_patch_norm hx
        have hy' := flat_patch_norm hy
        have hh := norm_sub_le x y
        linarith
      have hh := (flat_boundary_jet_cross_center_coherence j u a b (p a) (p b) (T a) (T b)
        (flatProjection_plane j x) (flatProjection_plane j y)
        (hp.symmetric a (hproj x (hsmall hx)) (flatProjection_plane j x))
        (hp.symmetric b (hproj y (hsmall hy)) (flatProjection_plane j y)) hM hα.le hd hdr
        (hp.remainder a (hproj x (hsmall hx)) (flatProjection_plane j x))
        (hp.remainder b (hproj y (hsmall hy)) (flatProjection_plane j y))).1
      have hpw := Real.rpow_le_rpow (norm_nonneg (a-b)) hdist hα.le
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (norm_nonneg _)] at hpw
      change ‖operatorBilinear (T a)-operatorBilinear (T b)‖ ≤ _
      rw [← operatorBilinear_sub,norm_operatorBilinear]
      apply (hh.trans (mul_le_mul_of_nonneg_left hpw (by positivity))).trans
      have hm := mul_le_mul_of_nonneg_left (show M ≤ M+H by linarith) hJ
      have ht := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (norm_nonneg (x-y)) α)
      dsimp [J] at ht
      nlinarith
  have hinterior : ∀ x ∈ flatClosedPatch j (1/32), ∀ y ∈ flatClosedPatch j (1/32),
      ‖x-y‖ < x j/128 → ‖flatSecondField j u T x-flatSecondField j u T y‖ ≤ (K*(M+H))*‖x-y‖^α := by
    intro x hx y hy hxy
    have hxj : 0 < x j := by linarith [norm_nonneg (x-y)]
    have hyj : 0 < y j := by
      have hh : |x j-y j| ≤ ‖x-y‖ := PiLp.norm_apply_le (x-y) j
      linarith [le_abs_self (x j-y j)]
    rw [flatSecondField,if_pos hxj,flatSecondField,if_pos hyj]
    exact (hlim x (hsmall hx) hxj).2.2 x (Metric.mem_ball_self (by positivity)) y (by
      rw [Metric.mem_ball,dist_eq_norm,norm_sub_rev]
      linarith)
  have hholder := flat_field_holder_of_boundary_and_interior j (fun x hx => hx.2) (flatSecondField j u T) B
    hα.le (by positivity : 0 ≤ K*(M+H)) (by positivity : 0 ≤ J*(M+H)) (by positivity : 0 ≤ K*(M+H))
    (fun x hx => herror x (hsmall hx)) hboundary hinterior
  have hholder' : ∀ x ∈ flatClosedPatch j (1/32), ∀ y ∈ flatClosedPatch j (1/32),
      ‖flatSecondField j u T x-flatSecondField j u T y‖ ≤ C*(M+H)*‖x-y‖^α := by
    intro x hx y hy
    apply (hholder x hx y hy).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) α)
    dsimp [C]
    nlinarith
  refine ⟨?_,hholder',continuousOn_of_norm_holder_bound hα hholder'⟩
  intro x hx
  apply (hsup x hx).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  dsimp [C]
  have hh : 0 ≤ K*(128^α+129^α) := by positivity
  linarith

end GaussianTilt.MomentMapSchauder
