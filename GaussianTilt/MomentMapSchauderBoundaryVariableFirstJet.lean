import GaussianTilt.MomentMapSchauderBoundaryVariableLocalization

/-! # Normalized local boundary Schauder estimate with lower-jet data -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 3200000
open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- Actual local normalized boundary freezing, product commutator and
highest-derivative absorption. The original Hessian Hölder constant is
absent from the conclusion; only lower jets and the forcing remain. -/
theorem exists_normalized_boundary_first_jet_bound [NeZero n] {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (j : Fin n) (u f : KernelSpace n → ℝ)
      (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
      (D : KernelSpace n → KernelSpace n →L[ℝ] ℝ)
      (B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ),
      (∀ x, x j ≤ 0 → u x=0) → ContDiffOn ℝ 2 u (flatUpperBall j 2) →
      (∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ L*|x j|) →
      (∀ x ∈ flatUpperBall j 2, D x=fderiv ℝ u x) →
      (∀ x ∈ flatUpperBall j 2, B x=fderiv ℝ (fderiv ℝ u) x) →
      BoundedHolderOn α B (flatClosedPatch j 2) →
      (∀ x ∈ flatClosedPatch j 2, (A x).IsSymm) →
      (∀ x ∈ flatClosedPatch j 2, ∀ i k, |(1 : Matrix (Fin n) (Fin n) ℝ) i k-A x i k| ≤ ε) →
      (∀ x ∈ flatClosedPatch j 2, ∀ y ∈ flatClosedPatch j 2, ∀ i k, |A x i k-A y i k| ≤ ε*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j 2, matrixContraction (A x) (bilinearEntryMatrix (B x))=f x) →
      ∀ U V HU HD F H : ℝ, 0 ≤ U → 0 ≤ V → 0 ≤ HU → 0 ≤ HD → 0 ≤ F → 0 ≤ H →
      (∀ x ∈ flatClosedPatch j 2, |u x| ≤ U) → (∀ x ∈ flatClosedPatch j 2, ‖D x‖ ≤ V) →
      (∀ x ∈ flatClosedPatch j 2, ∀ y ∈ flatClosedPatch j 2, |u x-u y| ≤ HU*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j 2, ∀ y ∈ flatClosedPatch j 2, ‖D x-D y‖ ≤ HD*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j 2, |f x| ≤ F) →
      (∀ x ∈ flatClosedPatch j 2, ∀ y ∈ flatClosedPatch j 2, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j (1/512), ‖B x‖ ≤ C*(U+V+HU+HD+F+H)) ∧
      (∀ x ∈ flatClosedPatch j (1/512), ∀ y ∈ flatClosedPatch j (1/512),
        ‖B x-B y‖ ≤ C*(U+V+HU+HD+F+H)*‖x-y‖^α) := by
  obtain ⟨ε,C0,hε,hC0,hbase⟩ := exists_compact_flat_small_coefficient_bound (n := n) hα hα1
  let χ := scaledInteriorCutoff (0 : KernelSpace n) (1/256)
  have hχ : ContDiff ℝ ∞ χ := scaledInteriorCutoff_contDiff 0 (1/256)
  have hχs : HasCompactSupport χ := scaledInteriorCutoff_compact 0 (by norm_num)
  obtain ⟨T0,hT0,hχB,hχH⟩ := exists_contDiff_holder_bound_on_compact_convex
    (contDiff_infty.mp hχ 1) (isCompact_closedBall (0 : KernelSpace n) 2) (convex_closedBall 0 2) hα.le hα1.le
  obtain ⟨T1,hT1,hχ1,hχH1⟩ := exists_contDiff_holder_bound_on_compact_convex
    (contDiff_infty.mp (hχ.fderiv_right (m := ∞) (by simp)) 1)
    (isCompact_closedBall (0 : KernelSpace n) 2) (convex_closedBall 0 2) hα.le hα1.le
  obtain ⟨T2,hT2,hχ2,hχH2⟩ := exists_contDiff_holder_bound_on_compact_convex
    (contDiff_infty.mp ((hχ.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)) 1)
    (isCompact_closedBall (0 : KernelSpace n) 2) (convex_closedBall 0 2) hα.le hα1.le
  let T := T0+T1+T2+1
  have hT : 0 < T := by dsimp [T]; positivity
  have hT0T : T0 ≤ T := by dsimp [T]; linarith
  have hT1T : T1 ≤ T := by dsimp [T]; linarith
  have hT2T : T2 ≤ T := by dsimp [T]; linarith
  let C := C0*(3+T+(n:ℝ)^2*(9*(1+ε)*T+3*ε*T))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ε,C,hε,hC,?_⟩
  intro j u f A D B hu0 hu hgrowth hD hB hBH hAsymm hA hAH heq U V HU HD F H hU hV hHU hHD hF hH huB hDB huH hDH hfB hfH
  let S := flatClosedPatch j 2
  let w := fun x => χ x*u x
  let Q := boundaryCutoffSecond χ u D B
  let g := boundaryLocalizedForcing A χ u D f
  have hχb : ∀ x, |χ x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (scaledInteriorCutoff_nonneg 0 x (1/256))]
    exact scaledInteriorCutoff_le_one 0 x (1/256)
  have hχH' : ∀ x ∈ S, ∀ y ∈ S, |χ x-χ y| ≤ T*‖x-y‖^α := by
    intro x hx y hy
    have hh : |χ x-χ y| ≤ T0*‖x-y‖^α := by simpa only [Real.norm_eq_abs] using hχH x hx.1 y hy.1
    exact hh.trans (mul_le_mul_of_nonneg_right hT0T (Real.rpow_nonneg (norm_nonneg _) α))
  have hχ1' : ∀ x ∈ S, ‖fderiv ℝ χ x‖ ≤ T := fun x hx => (hχ1 x hx.1).trans hT1T
  have hχ2' : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ T := fun x hx => (hχ2 x hx.1).trans hT2T
  have hχH1' : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ χ x-fderiv ℝ χ y‖ ≤ T*‖x-y‖^α := by
    intro x hx y hy
    exact (hχH1 x hx.1 y hy.1).trans (mul_le_mul_of_nonneg_right hT1T (Real.rpow_nonneg (norm_nonneg _) α))
  have hχH2' : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ (fderiv ℝ χ) x-fderiv ℝ (fderiv ℝ χ) y‖ ≤ T*‖x-y‖^α := by
    intro x hx y hy
    exact (hχH2 x hx.1 y hy.1).trans (mul_le_mul_of_nonneg_right hT2T (Real.rpow_nonneg (norm_nonneg _) α))
  have huBH : BoundedHolderOn α u S := by
    refine ⟨U+HU,by positivity,fun x hx => ?_,fun x hx y hy => ?_⟩
    · simpa only [Real.norm_eq_abs] using (huB x hx).trans (show U ≤ U+HU by linarith)
    · rw [Real.norm_eq_abs]
      exact (huH x hx y hy).trans
        (mul_le_mul_of_nonneg_right (show HU ≤ U+HU by linarith) (Real.rpow_nonneg (norm_nonneg _) α))
  have hDBH : BoundedHolderOn α D S :=
    ⟨V+HD,by positivity,fun x hx => (hDB x hx).trans (by linarith),fun x hx y hy =>
      (hDH x hx y hy).trans (mul_le_mul_of_nonneg_right (by linarith : HD ≤ V+HD) (Real.rpow_nonneg (norm_nonneg _) α))⟩
  have hQBH := boundedHolderOn_boundaryCutoffSecond hα.le hα1.le (isCompact_flatClosedPatch j 2)
    (convex_flatClosedPatch j 2) hχ huBH hDBH hBH
  have hQc : ContinuousOn Q S := by
    obtain ⟨q,hq,hqb,hqH⟩ := hQBH
    exact continuousOn_of_norm_holder_bound hα hqH
  have hχsupp : tsupport χ ⊆ Metric.closedBall (0 : KernelSpace n) (1/128) := by
    simpa only [show (2:ℝ)*(1/256)=1/128 by norm_num] using tsupport_scaledInteriorCutoff_subset (0 : KernelSpace n) (by norm_num : (0:ℝ)<1/256)
  have hχball : tsupport χ ⊆ Metric.ball (0 : KernelSpace n) 2 :=
    hχsupp.trans (Metric.closedBall_subset_ball (by norm_num))
  obtain ⟨L,hL,huL⟩ := hgrowth
  obtain ⟨hwL2,hw0,hwC2,hwgrowth⟩ := boundary_cutoff_classical_data j hu0 hu hL huL hχ hχs hχball
    (fun x => scaledInteriorCutoff_nonneg 0 x (1/256)) (fun x => scaledInteriorCutoff_le_one 0 x (1/256))
  have hQeq : ∀ x ∈ flatUpperBall j 2, Q x=fderiv ℝ (fderiv ℝ w) x := by
    intro x hx
    exact boundaryCutoffSecond_eq_actual (hu.contDiffAt ((isOpen_flatUpperBall j 2).mem_nhds hx))
      (contDiff_infty.mp hχ 2) (hD x hx) (hB x hx)
  have hQ0 : ∀ x ∈ S, 1/64 ≤ ‖x‖ → Q x=0 := by
    intro x hx hxn
    exact boundaryCutoffSecond_zero_off hχsupp (by
      intro hh
      have ht : ‖x‖ ≤ 1/128 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hh
      linarith)
  have hAb : ∀ x ∈ S, ∀ i k, |A x i k| ≤ 1+ε := by
    intro x hx i k
    have hi : |(1:Matrix (Fin n) (Fin n) ℝ) i k| ≤ 1 := by
      classical
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num
    have hh := abs_sub ((1:Matrix (Fin n) (Fin n) ℝ) i k) (((1:Matrix (Fin n) (Fin n) ℝ) i k)-A x i k)
    rw [sub_sub_cancel] at hh
    linarith [hA x hx i k]
  obtain ⟨hRb,hRH⟩ := boundaryCutoffRemainder_bounds_on hT.le hT.le hT.le hT.le hU hV hHU hHD
    hχ1' hχ2' hχH1' hχH2' huB hDB huH hDH
  let R := T*U+2*(T*V)
  let HR := T*HU+U*T+2*(T*HD+V*T)
  obtain ⟨hgB,hgH⟩ := boundaryLocalizedForcing_bounds_on (by positivity : 0 ≤ 1+ε) hε.le zero_le_one hT.le hF hH
    (by positivity : 0 ≤ R) (by positivity : 0 ≤ HR) hAb hAH (fun x _ => hχb x) hχH' hfB hfH hRb hRH
  have hwB : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |w x| ≤ U := by
    intro x hx
    by_cases hxj : 0 ≤ x j
    · exact (abs_mul _ _).le.trans ((mul_le_mul (hχb x) (huB x ⟨Metric.ball_subset_closedBall hx,hxj⟩)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul U))
    · simp only [w,hu0 x (le_of_not_ge hxj),mul_zero,abs_zero]
      exact hU
  have hBounds := hbase j w g A Q hwL2 hw0 hwC2 ⟨L,hL,hwgrowth⟩ hQc hQeq hQ0 hQBH hA hAH
    (fun x hx => boundaryLocalizedForcing_eq_operator A χ u f D B (hAsymm x hx) (heq x hx))
    U (F+(n:ℝ)^2*(1+ε)*R) (H+F*T+(n:ℝ)^2*((1+ε)*HR+ε*R)) hU (by positivity) (by positivity)
    hwB (by simpa only [one_mul] using hgB) (by simpa only [one_mul] using hgH)
  let W := U+V+HU+HD+F+H
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hRW : R ≤ 3*T*W := by dsimp [R,W]; nlinarith [mul_nonneg hT.le hU,mul_nonneg hT.le hV,mul_nonneg hT.le hHU,mul_nonneg hT.le hHD,mul_nonneg hT.le hF,mul_nonneg hT.le hH]
  have hHRW : HR ≤ 6*T*W := by dsimp [HR,W]; nlinarith [mul_nonneg hT.le hU,mul_nonneg hT.le hV,mul_nonneg hT.le hHU,mul_nonneg hT.le hHD,mul_nonneg hT.le hF,mul_nonneg hT.le hH]
  have htotal : C0*(U+(F+(n:ℝ)^2*(1+ε)*R)+(H+F*T+(n:ℝ)^2*((1+ε)*HR+ε*R))) ≤ C*W := by
    have h1 := mul_le_mul_of_nonneg_left hRW (show 0 ≤ (n:ℝ)^2*(1+ε) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hHRW (show 0 ≤ (n:ℝ)^2*(1+ε) by positivity)
    have h3 := mul_le_mul_of_nonneg_left hRW (show 0 ≤ (n:ℝ)^2*ε by positivity)
    have hFW : F ≤ W := by dsimp [W]; linarith
    have hFWT := mul_le_mul_of_nonneg_left hFW hT.le
    have hbaseW : U+F+H ≤ 3*W := by dsimp [W]; linarith
    have hh : U+(F+(n:ℝ)^2*(1+ε)*R)+(H+F*T+(n:ℝ)^2*((1+ε)*HR+ε*R)) ≤
        (3+T+(n:ℝ)^2*(9*(1+ε)*T+3*ε*T))*W := by nlinarith
    exact (mul_le_mul_of_nonneg_left hh hC0.le).trans_eq (by dsimp [C]; ring)
  have hsmall : flatClosedPatch j (1/512) ⊆ S := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (by norm_num) hx.1,hx.2⟩
  have hQB : ∀ x ∈ flatClosedPatch j (1/512), Q x=B x := by
    intro x hx
    apply boundaryCutoffSecond_eq_of_one_neighborhood
    have hx' : x ∈ Metric.ball (0 : KernelSpace n) (1/256) := by
      rw [Metric.mem_ball,dist_zero_right]
      exact (flat_patch_norm hx).trans_lt (by norm_num)
    filter_upwards [Metric.isOpen_ball.mem_nhds hx'] with y hy
    exact scaledInteriorCutoff_one (by norm_num) (by
      simpa only [sub_zero] using (show ‖y‖ < 1/256 by simpa only [Metric.mem_ball,dist_zero_right] using hy).le)
  refine ⟨?_,?_⟩
  · intro x hx
    rw [← hQB x hx]
    exact (hBounds.1 x (hsmall hx)).trans htotal
  · intro x hx y hy
    rw [← hQB x hx,← hQB y hy]
    exact (hBounds.2 x (hsmall hx) y (hsmall hy)).trans (mul_le_mul_of_nonneg_right htotal (Real.rpow_nonneg (norm_nonneg _) α))

end GaussianTilt.MomentMapSchauder
