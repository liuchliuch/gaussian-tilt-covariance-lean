import GaussianTilt.MomentMapSchauderBoundaryVariableWeak

/-! # A proved compact-support half-space estimate suitable for absorption -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- The actual flat Poisson estimate controls a compactly localized Hessian
field on the whole working half-ball. Continuous boundary values are
identified with the constructed jet by density of the interior. -/
theorem exists_compact_flat_poisson_hessian_bound [NeZero n] {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin n) (u g : KernelSpace n → ℝ),
      MemLp u 2 volume → (∀ x, x j ≤ 0 → u x=0) →
      ContDiffOn ℝ 2 u (flatUpperBall j 2) →
      (∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ A*|x j|) →
      Continuous g → (∀ x ∈ flatUpperBall j 2, kernelLaplacian u x= -g x) →
      ∀ U F H : ℝ, 0 ≤ U → 0 ≤ F → 0 ≤ H →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ U) →
      (∀ x, |g x| ≤ F) → (∀ x y, |g x-g y| ≤ H*‖x-y‖^α) →
      ∀ B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ,
      ContinuousOn B (flatClosedPatch j 2) →
      (∀ x ∈ flatUpperBall j 2, B x=fderiv ℝ (fderiv ℝ u) x) →
      (∀ x ∈ flatClosedPatch j 2, 1/64 ≤ ‖x‖ → B x=0) →
      (∀ x ∈ flatClosedPatch j 2, ‖B x‖ ≤ C*(U+F+H)) ∧
      (∀ x ∈ flatClosedPatch j 2, ∀ y ∈ flatClosedPatch j 2,
        ‖B x-B y‖ ≤ C*(U+F+H)*‖x-y‖^α) := by
  obtain ⟨C0,hC0,hbase⟩ := exists_flat_boundary_schauder_jet (n := n) hα hα1
  let C := C0*(1+64^α)
  have hC : 0 < C := by dsimp [C]; positivity
  have hC0C : C0 ≤ C := by dsimp [C]; nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ)≤64) α]
  refine ⟨C,hC,?_⟩
  intro j u g huL2 hu0 hu hgrowth hg heq U F H hU hF hH huB hgB hgH B hBc hBeq hB0
  have huw := flatWeakPoisson_of_classical huL2 hu0 hu hgrowth heq
  obtain ⟨J,hJn,hJu,_,hJQ⟩ := hbase j u g huw hg U H F hU hH hF hgH huB (fun x _ => hgB x)
  let S := flatClosedPatch j (1/32)
  let Q := HolderSpace.jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch j (1/32)) α J
  let q := HolderSpace.extendValue α Q
  have hS2 : S ⊆ flatClosedPatch j 2 := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (by norm_num) hx.1,hx.2⟩
  have hEqI : EqOn B q (interior S) := by
    intro x hx
    have hxu := flatClosedPatch_interior_subset_upper (by norm_num : (1:ℝ)/32<2) hx
    rw [hBeq x hxu,show q x=HolderSpace.value S _ α Q ⟨x,interior_subset hx⟩ from HolderSpace.extendValue_mem α Q (interior_subset hx)]
    exact (hJQ ⟨x,interior_subset hx⟩ hxu.2).symm
  have hcl : closure (interior S)=S :=
    ((convex_flatClosedPatch j (1/32)).closure_interior_eq_closure_of_nonempty_interior
      (flatClosedPatch_nonempty_interior j (by norm_num : (0:ℝ)<1/32))).trans
      (isCompact_flatClosedPatch j (1/32)).isClosed.closure_eq
  have hEq : EqOn B q S := hEqI.of_subset_closure (hBc.mono hS2)
    (HolderSpace.continuousOn_extendValue α Q) interior_subset (by rw [hcl])
  have hQn : ‖Q‖ ≤ C0*(U+F+H) := by
    have hh := (HolderSpace.norm_jetSecond_le (convex_flatClosedPatch j (1/32)) α J).trans hJn
    exact hh.trans_eq (by ring)
  have hsupSmall : ∀ x ∈ S, ‖B x‖ ≤ C0*(U+F+H) := by
    intro x hx
    rw [hEq hx,show q x=HolderSpace.value S _ α Q ⟨x,hx⟩ from HolderSpace.extendValue_mem α Q hx]
    exact (HolderSpace.norm_value_apply_le S _ α Q ⟨x,hx⟩).trans hQn
  have hholderSmall : ∀ x ∈ S, ∀ y ∈ S, ‖B x-B y‖ ≤ C0*(U+F+H)*‖x-y‖^α := by
    intro x hx y hy
    rw [hEq hx,hEq hy,show q x=HolderSpace.value S _ α Q ⟨x,hx⟩ from HolderSpace.extendValue_mem α Q hx,
      show q y=HolderSpace.value S _ α Q ⟨y,hy⟩ from HolderSpace.extendValue_mem α Q hy]
    exact (HolderSpace.norm_value_sub_le S _ α Q ⟨x,hx⟩ ⟨y,hy⟩).trans
      (mul_le_mul_of_nonneg_right hQn (Real.rpow_nonneg (norm_nonneg (x-y)) α))
  have hsup : ∀ x ∈ flatClosedPatch j 2, ‖B x‖ ≤ C0*(U+F+H) := by
    intro x hx
    by_cases hxn : ‖x‖ ≤ 1/32
    · exact hsupSmall x ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxn,hx.2⟩
    · rw [hB0 x hx (by linarith [le_of_not_ge hxn]),norm_zero]
      positivity
  have hfar : ∀ x ∈ flatClosedPatch j 2, ∀ y ∈ flatClosedPatch j 2, ¬‖y‖ ≤ 1/32 →
      ‖B x-B y‖ ≤ C*(U+F+H)*‖x-y‖^α := by
    intro x hx y hy hyn
    have hy0 : B y=0 := hB0 y hy (by linarith [le_of_not_ge hyn])
    rw [hy0,sub_zero]
    by_cases hxn : 1/64 ≤ ‖x‖
    · rw [hB0 x hx hxn,norm_zero]
      positivity
    · have hdist : 1/64 ≤ ‖x-y‖ := by
        have ht : ‖y‖ ≤ ‖x-y‖+‖x‖ := by
          have hh := norm_sub_le_norm_sub_add_norm_sub y x 0
          simpa only [sub_zero,norm_sub_rev y x] using hh
        linarith [lt_of_not_ge hxn,lt_of_not_ge hyn]
      have hp : 1 ≤ 64^α*‖x-y‖^α := by
        rw [← Real.mul_rpow (by norm_num : (0:ℝ)≤64) (norm_nonneg _)]
        exact Real.one_le_rpow (by linarith) hα.le
      have hb := mul_le_mul_of_nonneg_left hp (show 0 ≤ C0*(U+F+H) by positivity)
      have hc : C0*64^α ≤ C := by dsimp [C]; nlinarith
      have hc' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ U+F+H))
        (Real.rpow_nonneg (norm_nonneg (x-y)) α)
      exact (hsup x hx).trans (by nlinarith)
  constructor
  · intro x hx
    exact (hsup x hx).trans (mul_le_mul_of_nonneg_right hC0C (by positivity))
  · intro x hx y hy
    by_cases hxn : ‖x‖ ≤ 1/32
    · by_cases hyn : ‖y‖ ≤ 1/32
      · have hxS : x ∈ S := ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxn,hx.2⟩
        have hyS : y ∈ S := ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hyn,hy.2⟩
        exact (hholderSmall x hxS y hyS).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC0C (by positivity : 0 ≤ U+F+H)) (Real.rpow_nonneg (norm_nonneg _) α))
      · exact hfar x hx y hy hyn
    · simpa only [norm_sub_rev] using hfar y hy x hx hxn

end GaussianTilt.MomentMapSchauder
