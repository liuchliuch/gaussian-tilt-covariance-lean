import GaussianTilt.MomentMapSchauderBoundaryHessianField

/-! # A genuine Lipschitz first-derivative field on the closed half-ball -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2800000
open Set InnerProductSpace
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def flatFirstField (j : Fin n) (u : KernelSpace n → ℝ)
    (p : KernelSpace n → KernelSpace n) (x : KernelSpace n) : KernelSpace n →L[ℝ] ℝ :=
  if 0 < x j then fderiv ℝ u x else toDual ℝ (KernelSpace n) (p (flatProjection j x))

/-- The first field is Lipschitz with a constant determined solely by the
actual boundary approximation and forcing data. It agrees with the true
Fréchet derivative at every interior point. -/
theorem exists_flat_first_field_bounds [NeZero n] {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin n) (u f : KernelSpace n → ℝ),
      ContDiffOn ℝ 2 u (flatUpperBall j 2) → Continuous f →
      (∀ x ∈ flatUpperBall j 2, kernelLaplacian u x= -f x) →
      ∀ M H : ℝ, 0 ≤ M → 0 ≤ H → (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) →
      ∀ p T, FlatPolynomialData j u f α M p T →
      (∀ x ∈ flatClosedPatch j (1/32), ‖flatFirstField j u p x‖ ≤ C*(M+H)) ∧
      (∀ x ∈ flatClosedPatch j (1/32), ∀ y ∈ flatClosedPatch j (1/32),
        ‖flatFirstField j u p x-flatFirstField j u p y‖ ≤ C*(M+H)*‖x-y‖) ∧
      ContinuousOn (flatFirstField j u p) (flatClosedPatch j (1/32)) := by
  obtain ⟨K,hK,hconv⟩ := exists_flat_boundary_interior_jet_convergence (n := n) hα hα1
  obtain ⟨Q,hQ,hsecond⟩ := exists_flat_second_field_bounds (n := n) hα hα1
  let J := 2*(72*(2:ℝ)^(2+α)+1)
  let C := Q+(K+1)*257+J+K+2
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro j u f hu hf heq M H hM hH hfH p T hp
  have hHs := (hsecond j u f hu hf heq M H hM hH hfH p T hp).1
  let B := fun x => toDual ℝ (KernelSpace n) (p (flatProjection j x))
  have hproj (x : KernelSpace n) (hx : x ∈ flatClosedPatch j (1/32)) : ‖flatProjection j x‖ ≤ 1 := by
    have hn := norm_flatProjection_le j x
    have hx' := flat_patch_norm hx
    linarith
  have hheight (x : KernelSpace n) (hx : x ∈ flatClosedPatch j (1/32)) : x j ≤ 1/32 := by
    have hc : |x j| ≤ ‖x‖ := PiLp.norm_apply_le x j
    have hn := flat_patch_norm hx
    linarith [le_abs_self (x j)]
  have herror : ∀ x ∈ flatClosedPatch j (1/32), ‖flatFirstField j u p x-B x‖ ≤ (K+1)*(M+H)*(x j) := by
    intro x hx
    by_cases hxj : 0 < x j
    · have hl := (hconv j u f hu hf heq M H hM hH hfH
        (flatProjection j x) (p (flatProjection j x)) (T (flatProjection j x))
        (hproj x hx) (flatProjection_plane j x) (hp.symmetric _ (hproj x hx) (flatProjection_plane j x))
        (hp.equation _ (hproj x hx) (flatProjection_plane j x)) (hp.remainder _ (hproj x hx) (flatProjection_plane j x))
        x (x j) hxj (by linarith [hheight x hx]) rfl (by rw [norm_sub_flatProjection_eq,abs_of_pos hxj])).1
      have hpw : (x j)^α ≤ 1 := Real.rpow_le_one hxj.le (by linarith [hheight x hx]) hα.le
      have hl' := hl.trans (mul_le_of_le_one_right (by positivity) hpw)
      have hb : ‖toDual ℝ (KernelSpace n) (p (flatProjection j x)+T (flatProjection j x) (x-flatProjection j x))-B x‖ ≤ M*(x j) := by
        rw [show B x=toDual ℝ (KernelSpace n) (p (flatProjection j x)) from rfl,← map_sub,
          add_sub_cancel_left,(toDual ℝ (KernelSpace n)).norm_map]
        exact ((T (flatProjection j x)).le_opNorm _).trans (by
          rw [norm_sub_flatProjection_eq,abs_of_pos hxj]
          exact mul_le_mul_of_nonneg_right (hp.second_bound _ (hproj x hx) (flatProjection_plane j x)) hxj.le)
      rw [flatFirstField,if_pos hxj]
      have ht := norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ u x)
        (toDual ℝ (KernelSpace n) (p (flatProjection j x)+T (flatProjection j x) (x-flatProjection j x))) (B x)
      nlinarith [mul_nonneg hH hxj.le]
    · simp only [flatFirstField,if_neg hxj,B,sub_self,norm_zero]
      exact mul_nonneg (by positivity) hx.2
  have hboundary : ∀ x ∈ flatClosedPatch j (1/32), ∀ y ∈ flatClosedPatch j (1/32),
      ‖B x-B y‖ ≤ (J*(M+H))*‖x-y‖ := by
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
        (hp.symmetric a (hproj x hx) (flatProjection_plane j x))
        (hp.symmetric b (hproj y hy) (flatProjection_plane j y)) hM hα.le hd hdr
        (hp.remainder a (hproj x hx) (flatProjection_plane j x))
        (hp.remainder b (hproj y hy) (flatProjection_plane j y))).2
      have hpw : ‖a-b‖^(1+α) ≤ ‖a-b‖ := by
        rw [Real.rpow_add hd,Real.rpow_one]
        exact mul_le_of_le_one_right (norm_nonneg _) (Real.rpow_le_one (norm_nonneg _) (by linarith) hα.le)
      have hh' := hh.trans (mul_le_mul_of_nonneg_left hpw (by positivity))
      have hTb : ‖T b (a-b)‖ ≤ M*‖a-b‖ :=
        ((T b).le_opNorm _).trans (mul_le_mul_of_nonneg_right
          (hp.second_bound b (hproj y hy) (flatProjection_plane j y)) (norm_nonneg _))
      have ht : ‖p a-p b‖ ≤ ‖p a-p b-T b (a-b)‖+‖T b (a-b)‖ := by
        simpa only [sub_add_cancel] using norm_add_le (p a-p b-T b (a-b)) (T b (a-b))
      change ‖toDual ℝ (KernelSpace n) (p a)-toDual ℝ (KernelSpace n) (p b)‖ ≤ _
      rw [← map_sub,(toDual ℝ (KernelSpace n)).norm_map]
      have hb : ‖p a-p b‖ ≤ (72*2^(2+α)+1)*M*‖a-b‖ := by nlinarith
      apply hb.trans
      have hm := mul_le_mul_of_nonneg_left hdist (show 0 ≤ (72*2^(2+α)+1)*M by positivity)
      have hN := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (show M ≤ M+H by linarith) hJ) (norm_nonneg (x-y))
      dsimp [J] at hN
      nlinarith
  have hinterior : ∀ x ∈ flatClosedPatch j (1/32), ∀ y ∈ flatClosedPatch j (1/32),
      ‖x-y‖ < x j/128 → ‖flatFirstField j u p x-flatFirstField j u p y‖ ≤ (Q*(M+H))*‖x-y‖ := by
    intro x hx y hy hxy
    have hxj : 0 < x j := by linarith [norm_nonneg (x-y)]
    have hyj : 0 < y j := by
      have hh : |x j-y j| ≤ ‖x-y‖ := PiLp.norm_apply_le (x-y) j
      linarith [le_abs_self (x j-y j)]
    have hball : ∀ z ∈ Metric.ball x (x j/64), z ∈ flatClosedPatch j (1/16) ∧ z ∈ flatUpperBall j 2 := by
      intro z hz
      have hzx : ‖z-x‖ < x j/64 := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
      have hzj : 0 < z j := by
        have ht : |z j-x j| ≤ ‖z-x‖ := PiLp.norm_apply_le (z-x) j
        linarith [neg_abs_le (z j-x j)]
      have hzn : ‖z‖ < 1/16 := by
        have ht : ‖z‖ ≤ ‖z-x‖+‖x‖ := by simpa only [sub_add_cancel] using norm_add_le (z-x) x
        have hx' := flat_patch_norm hx
        linarith [hheight x hx]
      exact ⟨⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hzn.le,hzj.le⟩,
        ⟨by simpa only [Metric.mem_ball,dist_zero_right] using (show ‖z‖ < 2 by linarith),hzj⟩⟩
    have hdif : ∀ z ∈ Metric.ball x (x j/64), DifferentiableAt ℝ (fderiv ℝ u) z := by
      intro z hz
      exact ((hu.contDiffAt ((isOpen_flatUpperBall j 2).mem_nhds (hball z hz).2)).fderiv_right
        (m := 1) (by norm_num)).differentiableAt le_rfl
    have hDb : ∀ z ∈ Metric.ball x (x j/64), ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ Q*(M+H) := by
      intro z hz
      have hh := hHs z (hball z hz).1
      have hzj : 0 < z j := (hball z hz).2.2
      simpa only [flatSecondField,if_pos hzj] using hh
    rw [flatFirstField,if_pos hxj,flatFirstField,if_pos hyj]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le hdif hDb (convex_ball x (x j/64))
      (by rw [Metric.mem_ball,dist_eq_norm,norm_sub_rev]; linarith)
      (Metric.mem_ball_self (by positivity))
  have hLip := flat_field_holder_of_boundary_and_interior j (S := flatClosedPatch j (1/32)) (fun x hx => hx.2) (flatFirstField j u p) B
    (by norm_num : (0:ℝ)≤1) (by positivity : 0 ≤ (K+1)*(M+H))
    (by positivity : 0 ≤ J*(M+H)) (by positivity : 0 ≤ Q*(M+H))
    (by simpa only [Real.rpow_one] using herror) (by simpa only [Real.rpow_one] using hboundary)
    (by simpa only [Real.rpow_one] using hinterior)
  have hLip' : ∀ x ∈ flatClosedPatch j (1/32), ∀ y ∈ flatClosedPatch j (1/32),
      ‖flatFirstField j u p x-flatFirstField j u p y‖ ≤ C*(M+H)*‖x-y‖ := by
    intro x hx y hy
    have hh := hLip x hx y hy
    simp only [Real.rpow_one] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    dsimp [C]
    nlinarith [mul_nonneg (show 0 ≤ K+2 by positivity) (show 0 ≤ M+H by positivity)]
  refine ⟨?_,hLip',continuousOn_of_norm_holder_bound (by norm_num : (0:ℝ)<1)
    (by simpa only [Real.rpow_one] using hLip')⟩
  intro x hx
  have hB : ‖B x‖ ≤ M := by
    change ‖toDual ℝ (KernelSpace n) (p (flatProjection j x))‖ ≤ M
    rw [(toDual ℝ (KernelSpace n)).norm_map]
    exact hp.first_bound _ (hproj x hx) (flatProjection_plane j x)
  have he := (herror x hx).trans (mul_le_of_le_one_right (by positivity) (by linarith [hheight x hx]))
  have ht : ‖flatFirstField j u p x‖ ≤ ‖flatFirstField j u p x-B x‖+‖B x‖ := by
    simpa only [sub_add_cancel] using norm_add_le (flatFirstField j u p x-B x) (B x)
  have hsmall : ‖flatFirstField j u p x‖ ≤ (K+2)*(M+H) := by nlinarith
  apply hsmall.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  dsimp [C]
  linarith [mul_nonneg (show 0 ≤ K+1 by positivity) (by norm_num : (0:ℝ)≤257)]

end GaussianTilt.MomentMapSchauder
