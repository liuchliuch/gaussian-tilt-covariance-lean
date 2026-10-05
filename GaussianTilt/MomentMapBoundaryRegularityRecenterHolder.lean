import GaussianTilt.MomentMapBoundaryRegularityRecenter

/-! # Uniform boundary approach from every flat boundary center -/
noncomputable section
set_option maxHeartbeats 1000000
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma hasFDerivWithinAt_recentered_flat_solution {j : Fin n}
    {u : CoordinateSpace n → ℝ} {D : CoordinateSpace n → CoordinateSpace n →L[ℝ] ℝ}
    (hD : ∀ y ∈ flatClosedHalfBall j, HasFDerivWithinAt u (D y) (flatClosedHalfBall j) y)
    {c : CoordinateSpace n} {r : ℝ} (hc : c j = 0) (hr : 0 < r)
    (hcr : ‖(coordinateEquiv n).symm c‖ + r ≤ 1)
    {y : CoordinateSpace n} (hy : y ∈ flatClosedHalfBall j) :
    HasFDerivWithinAt (fun z => r⁻¹*u (ellipticRescalePoint c r z))
      (D (ellipticRescalePoint c r y)) (flatClosedHalfBall j) y := by
  have hm := (ellipticRescalePoint_flat_maps hc hr hcr).2
  have hp : HasFDerivAt (ellipticRescalePoint c r)
      (r • ContinuousLinearMap.id ℝ (CoordinateSpace n)) y := by
    simpa [ellipticRescalePoint] using ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul r).const_add c
  have hd := ((hD _ (hm hy)).comp y hp.hasFDerivWithinAt hm).const_mul r⁻¹
  convert hd using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  field_simp

/-- The original origin estimate is transported by a genuine affine map.
The same constants work at every flat point in the smaller patch. -/
theorem exists_local_flat_gradient_holder_all_centers [NeZero n] {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ (j : Fin n) (u f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (D : CoordinateSpace n → CoordinateSpace n →L[ℝ] ℝ) (M B : ℝ),
      0 ≤ M → 0 ≤ B → LocalFlatEllipticSystem j u f A lam Λ K M →
      ContinuousOn D (flatClosedHalfBall j) →
      (∀ y ∈ flatClosedHalfBall j, HasFDerivWithinAt u (D y) (flatClosedHalfBall j) y) →
      (∀ y ∈ flatClosedHalfBall j, ‖D y‖ ≤ B) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → y j=0 → u y=0) →
      ∀ c, ‖(coordinateEquiv n).symm c‖ ≤ 1/4 → c j = 0 →
      ∀ x, ‖(coordinateEquiv n).symm (x-c)‖ ≤ 1/32 → 0 ≤ x j →
      ∀ i, |D x (Pi.single i 1)-D c (Pi.single i 1)| ≤
        C*(B+M)*‖(coordinateEquiv n).symm (x-c)‖^α := by
  obtain ⟨α,C,hα,hα1,hC,hest⟩ := exists_local_flat_gradient_holder_of_zero_boundary (n := n) hlam hΛ hK
  refine ⟨α, 4*C, hα, hα1, by positivity, ?_⟩
  intro j u f A D M B hM hB hs hDc hD hDb hzero c hcn hcj x hxn hxj i
  let r : ℝ := 1/4
  let P := ellipticRescalePoint c r
  let y : CoordinateSpace n := (4 : ℝ) • (x-c)
  have hr : 0 < r := by norm_num [r]
  have hcr : ‖(coordinateEquiv n).symm c‖ + r ≤ 1 := by change ‖(coordinateEquiv n).symm c‖ + (1/4 : ℝ) ≤ 1; linarith
  have hmaps := (ellipticRescalePoint_flat_maps hcj hr hcr).2
  have hPr : ContDiff ℝ ∞ P := contDiff_ellipticRescalePoint c r
  have hnew := hs.recenter hcj hr hcr
  have hnewD : ∀ z ∈ flatClosedHalfBall j,
      HasFDerivWithinAt (fun z => r⁻¹*u (P z)) (D (P z)) (flatClosedHalfBall j) z :=
    fun z hz => hasFDerivWithinAt_recentered_flat_solution hD hcj hr hcr hz
  have hnewzero : ∀ z, ‖(coordinateEquiv n).symm z‖ ≤ 1 → z j = 0 → r⁻¹*u (P z) = 0 := by
    intro z hzn hzj
    have hzS : z ∈ flatClosedHalfBall j := ⟨hzn, hzj.ge⟩
    rw [hzero (P z) (hmaps hzS).1 (by change ellipticRescalePoint c r z j = 0; rw [ellipticRescalePoint_flat_coordinate hcj, hzj, mul_zero]), mul_zero]
  have hyn : ‖(coordinateEquiv n).symm y‖ = 4 * ‖(coordinateEquiv n).symm (x-c)‖ := by
    simp only [y, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hyj : 0 ≤ y j := by dsimp [y]; change 0 ≤ 4*(x j-c j); rw [hcj, sub_zero]; positivity
  have hPy : P y = x := by dsimp [P, ellipticRescalePoint, y, r]; module
  have hP0 : P 0 = c := by simp [P, ellipticRescalePoint]
  have hh := hest j (fun z => r⁻¹*u (P z)) (fun z => r*f (P z)) (fun z => A (P z))
    (fun z => D (P z)) (r*M) B (mul_nonneg hr.le hM) hB hnew
    (hDc.comp hPr.continuous.continuousOn hmaps) hnewD
    (fun z hz => hDb (P z) (hmaps hz)) hnewzero y (by rw [hyn]; linarith) hyj i
  rw [hPy, hP0, hyn, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (norm_nonneg _)] at hh
  have hfour : (4 : ℝ)^α ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hα1
  have hBM : B+r*M ≤ B+M := by dsimp [r]; nlinarith
  have hmul := mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg (norm_nonneg ((coordinateEquiv n).symm (x-c))) α)
  exact hh.trans (by
    have hb := mul_le_mul hBM hmul (by positivity : 0 ≤ (4 : ℝ)^α*‖(coordinateEquiv n).symm (x-c)‖^α)
      (add_nonneg hB hM)
    have hc := mul_le_mul_of_nonneg_left hb hC.le
    nlinarith)

end GaussianTilt.MomentMapRegularity
