import GaussianTilt.MomentMapHolderJetEmbedding

/-! # Actual quadratic Taylor remainder of a closed compatible Hölder jet -/
noncomputable section
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Symmetry reaches the boundary by continuity from the actual interior
second derivative; no symmetric-jet premise is added. -/
theorem jet_second_symmetric_closed {S : Set E} (hS : Convex ℝ S) (hSc : IsClosed S)
    (hint : (interior S).Nonempty) {α : ℝ} (hα : 0 < α) (j : Jet E ℝ hS α)
    (x : S) (v w : E) :
    value S (E →L[ℝ] E →L[ℝ] ℝ) α (jetSecond E ℝ hS α j) x v w =
      value S (E →L[ℝ] E →L[ℝ] ℝ) α (jetSecond E ℝ hS α j) x w v := by
  let H := extendValue α (jetSecond E ℝ hS α j)
  have hc : ContinuousOn H S := continuousOn_extendValue α _
  have hclosed : IsClosed {y ∈ S | H y v w = H y w v} :=
    hSc.isClosed_eq ((hc.clm_apply continuousOn_const).clm_apply continuousOn_const)
      ((hc.clm_apply continuousOn_const).clm_apply continuousOn_const)
  have hsub : interior S ⊆ {y ∈ S | H y v w = H y w v} := by
    intro y hy
    exact ⟨interior_subset hy, jet_second_symmetric hS hα j hy v w⟩
  have hx : (x : E) ∈ closure (interior S) := by
    rw [hS.closure_interior_eq_closure_of_nonempty_interior hint, hSc.closure_eq]
    exact x.2
  have he := (closure_minimal hsub hclosed hx).2
  simpa only [H, extendValue_mem α _ x.2] using he

/-- The literal quadratic polynomial of the stored true fields has a
controlled remainder even when the base point lies on the boundary. -/
theorem jet_quadratic_remainder_norm {S : Set E} (hS : Convex ℝ S) {α : ℝ}
    (hα : 0 ≤ α) (j : Jet E ℝ hS α) (x y : S) :
    |value S ℝ α (jetValue E ℝ hS α j) y - value S ℝ α (jetValue E ℝ hS α j) x -
      value S (E →L[ℝ] ℝ) α (jetFirst E ℝ hS α j) x ((y : E)-x) -
      (1/2 : ℝ)*value S (E →L[ℝ] E →L[ℝ] ℝ) α (jetSecond E ℝ hS α j) x ((y : E)-x) ((y : E)-x)| ≤
        ‖jetSecond E ℝ hS α j‖ * ‖(y : E)-x‖^α * ‖(y : E)-x‖^2 := by
  let D := jetFirst E ℝ hS α j
  let H := jetSecond E ℝ hS α j
  let h : E := (y : E)-x
  let q := value S (E →L[ℝ] E →L[ℝ] ℝ) α H x h h
  let err : ℝ → ℝ := fun t =>
    (value S (E →L[ℝ] ℝ) α D (segmentPoint hS x y t) -
      value S (E →L[ℝ] ℝ) α D x - t • value S (E →L[ℝ] E →L[ℝ] ℝ) α H x h) h
  have hcont : Continuous err := by
    exact ((((value S (E →L[ℝ] ℝ) α D).continuous.comp (continuous_segmentPoint hS x y)).sub
      continuous_const).sub (continuous_id.smul continuous_const)).clm_apply continuous_const
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖err t‖ ≤ ‖H‖*‖h‖^α*‖h‖^2 := by
    intro t ht
    have htcc : t ∈ Icc (0 : ℝ) 1 := by
      simp only [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at ht
      exact ⟨ht.1.le,ht.2⟩
    let z := segmentPoint hS x y t
    have hz : (z : E)-x = t • h := by
      rw [segmentPoint_eq hS x y htcc]
      dsimp only [h]
      abel
    have hzn : ‖(z : E)-x‖ ≤ ‖h‖ := by
      rw [hz,norm_smul,Real.norm_eq_abs,abs_of_nonneg htcc.1]
      exact mul_le_of_le_one_left (norm_nonneg _) htcc.2
    have hDrem := segmentIntegral_remainder_norm hS hα H x z
    rw [← (jet_ftc E ℝ hS α j x z).2] at hDrem
    rw [hz,map_smul] at hDrem
    have hp := Real.rpow_le_rpow (norm_nonneg ((z : E)-x)) hzn hα
    have hB : ‖H‖*‖t • h‖^α*‖t • h‖ ≤ ‖H‖*‖h‖^α*‖h‖ := by
      have hzn' : ‖t • h‖ ≤ ‖h‖ := by simpa only [hz] using hzn
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by simpa only [hz] using hp) (norm_nonneg _))
        hzn' (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
    have hOp := (value S (E →L[ℝ] ℝ) α D z - value S (E →L[ℝ] ℝ) α D x -
      t • value S (E →L[ℝ] E →L[ℝ] ℝ) α H x h).le_opNorm h
    exact hOp.trans ((mul_le_mul_of_nonneg_right (hDrem.trans hB) (norm_nonneg _)).trans_eq (by ring))
  have he : (∫ t in (0 : ℝ)..1, err t) =
      segmentIntegral hS α x y D - value S (E →L[ℝ] ℝ) α D x h - (1/2 : ℝ)*q := by
    simp only [err, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    change (∫ t in (0 : ℝ)..1,
      (value S (E →L[ℝ] ℝ) α D (segmentPoint hS x y t) h - value S (E →L[ℝ] ℝ) α D x h) - t*q) = _
    have hiD : IntervalIntegrable (fun t => value S (E →L[ℝ] ℝ) α D (segmentPoint hS x y t) h) volume 0 1 :=
      (continuous_segmentIntegrand hS α D x y).intervalIntegrable 0 1
    have hi1 : IntervalIntegrable (fun t => value S (E →L[ℝ] ℝ) α D (segmentPoint hS x y t) h -
        value S (E →L[ℝ] ℝ) α D x h) volume 0 1 := hiD.sub intervalIntegrable_const
    have hi2 : IntervalIntegrable (fun t : ℝ => t*q) volume 0 1 :=
      (continuous_id.mul continuous_const).intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_sub hiD intervalIntegrable_const,
      intervalIntegral.integral_const, intervalIntegral.integral_mul_const, integral_id]
    norm_num only [sub_zero, one_smul, one_pow, zero_pow (by omega : (2:ℕ)≠0)]
    rfl
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [he] at hb
  rw [(jet_ftc E ℝ hS α j x y).1]
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one, D, H, h, q] using hb

end GaussianTilt.HolderSpace
