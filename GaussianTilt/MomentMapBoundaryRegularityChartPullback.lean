import GaussianTilt.MomentMapBoundaryRegularityChartPullbackAlgebra
import GaussianTilt.MomentMapBoundaryRegularityRecenterHolder
import GaussianTilt.MomentMapLinearDirichletQuantitativeChartNeighborhood

/-! # Actual all-center Hölder approach in original physical charts -/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- The proved all-center flat estimate is pulled back through the actual
inverse derivative. One physical neighborhood and one approach radius work
for all boundary centers and all solutions of the fixed coefficient class. -/
theorem exists_chart_derivative_holder_all_boundary_centers [NeZero n]
    {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    {s ρ lam Λ K : ℝ} (hs : 0 < s) (hρ : 0 < ρ)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K)
    (hXs : ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 →
      ContDiffAt ℝ ∞ (scaledRawInverseChart hw a j hj s) y) :
    ∃ α r C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < r ∧ r ≤ 1 ∧ 2*r ≤ ρ ∧ 0 < C ∧
      ∀ (T f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (DT : CoordinateSpace n → CoordinateSpace n →L[ℝ] ℝ) (M B : ℝ),
      let X := scaledRawInverseChart hw a j hj s
      let D := fun y => (DT (X y)).comp (fderiv ℝ X y)
      0 ≤ M → 0 ≤ B → LocalFlatEllipticSystem j (T ∘ X) f A lam Λ K M →
      ContinuousOn D (flatClosedHalfBall j) →
      (∀ y ∈ flatClosedHalfBall j, HasFDerivWithinAt (T ∘ X) (D y) (flatClosedHalfBall j) y) →
      (∀ y ∈ flatClosedHalfBall j, ‖D y‖ ≤ B) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → y j=0 → T (X y)=0) →
      ∀ z ∈ Metric.ball a r, w z=w a →
      ∀ x, w x ≤ w a → dist x z ≤ r →
      ∀ k, |DT (coordinateEquiv n x) (Pi.single k 1)-DT (coordinateEquiv n z) (Pi.single k 1)| ≤
        C*(B+M)*(dist x z)^α := by
  obtain ⟨r,Q,hr,hr1,hrρ,hQ,hQr,hnear,hpair⟩ := exists_scaled_chart_approach_neighborhood hw a j hj s hρ
  obtain ⟨α,C₀,hα,hα1,hC₀,hflat⟩ := exists_local_flat_gradient_holder_all_centers (n := n) hlam hΛ hK
  let C := (n:ℝ)*C₀*Q^α*Q+Q
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨α,r,C,hα,hα1,hr,hr1,hrρ,hC,?_⟩
  intro T f A DT M B
  dsimp only
  intro hM hB hsys hDc hD hDb hzero z hz hwz x hwx hxz k
  let X := scaledRawInverseChart hw a j hj s
  let Y := scaledRawForwardChart w a j s
  let D := fun y => (DT (X y)).comp (fderiv ℝ X y)
  let ex := coordinateEquiv n x
  let ez := coordinateEquiv n z
  have hz2 : z ∈ Metric.closedBall a (2*r) := by
    change dist z a < r at hz
    change dist z a ≤ 2*r
    linarith
  have hx2 : x ∈ Metric.closedBall a (2*r) := by
    change dist z a < r at hz
    change dist x a ≤ 2*r
    linarith [dist_triangle x z a]
  have hzN := hnear z hz2
  have hxN := hnear x hx2
  have hxy := hpair x hx2 z hz2
  have hYz0 : Y ez j=0 := by
    dsimp only [Y,ez]
    rw [scaledRawForward_normal,ContinuousLinearEquiv.symm_apply_apply,hwz,sub_self,mul_zero]
  have hYx0 : 0 ≤ Y ex j := by
    dsimp only [Y,ex]
    rw [scaledRawForward_normal,ContinuousLinearEquiv.symm_apply_apply]
    exact mul_nonneg (inv_nonneg.mpr hs.le) (sub_nonneg.mpr hwx)
  have hzFlat : Y ez ∈ flatClosedHalfBall j := ⟨by linarith [hzN.2.1],hYz0.ge⟩
  have hxFlat : Y ex ∈ flatClosedHalfBall j := ⟨by linarith [hxN.2.1],hYx0⟩
  have hClose : ‖(coordinateEquiv n).symm (Y ex-Y ez)‖ ≤ 1/32 :=
    hxy.2.trans ((mul_le_mul_of_nonneg_left hxz hQp.le).trans hQr)
  have hh := hflat j (T ∘ X) f A D M B hM hB hsys hDc hD hDb hzero
    (Y ez) hzN.2.1 hYz0 (Y ex) hClose hYx0
  have hDiff (i : Fin n) : |D (Y ex) (Pi.single i 1)-D (Y ez) (Pi.single i 1)| ≤
      (C₀*(B+M)*Q^α)*(dist x z)^α := by
    have hp := Real.rpow_le_rpow (norm_nonneg _) hxy.2 hα.le
    rw [Real.mul_rpow hQp.le dist_nonneg] at hp
    exact (hh i).trans (by nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg hC₀.le (add_nonneg hB hM))])
  have hXx : X (Y ex)=ex := scaledRawInverse_forward hw a j hj hs.ne'
    (by simpa only [ex,ContinuousLinearEquiv.symm_apply_apply] using hxN.1)
  have hXz : X (Y ez)=ez := scaledRawInverse_forward hw a j hj hs.ne'
    (by simpa only [ez,ContinuousLinearEquiv.symm_apply_apply] using hzN.1)
  have hxDer := scaled_raw_chart_derivative_left_inverse hw a j hj hs.ne'
    (x := ex) (by simpa only [ex,ContinuousLinearEquiv.symm_apply_apply] using hxN.1)
    ((hXs _ hxFlat.1).differentiableAt (by simp))
  have hzDer := scaled_raw_chart_derivative_left_inverse hw a j hj hs.ne'
    (x := ez) (by simpa only [ez,ContinuousLinearEquiv.symm_apply_apply] using hzN.1)
    ((hXs _ hzFlat.1).differentiableAt (by simp))
  have hrecx : (D (Y ex)).comp (fderiv ℝ Y ex)=DT ex := by
    dsimp only [D]
    rw [hXx]
    exact intrinsic_derivative_recovery rfl hxDer
  have hrecz : (D (Y ez)).comp (fderiv ℝ Y ez)=DT ez := by
    dsimp only [D]
    rw [hXz]
    exact intrinsic_derivative_recovery rfl hzDer
  have hbound := intrinsic_derivative_difference_bound (DT ex) (DT ez) (D (Y ex)) (D (Y ez))
    (fderiv ℝ Y ex) (fderiv ℝ Y ez) (by positivity : 0 ≤ C₀*(B+M)*Q^α) hB hQp.le
    dist_nonneg (hxz.trans hr1) hα hα1 hrecx hrecz hDiff (hDb _ hzFlat) hxN.2.2 hxy.1 k
  exact hbound.trans (by
    have hm := mul_le_mul_of_nonneg_left hM hQp.le
    have hpow := Real.rpow_nonneg (dist_nonneg (x := x) (y := z)) α
    dsimp only [C]
    nlinarith [mul_le_mul_of_nonneg_right hm hpow])

end GaussianTilt.MomentMapRegularity
