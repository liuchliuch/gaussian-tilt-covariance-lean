import GaussianTilt.MomentMapRegularityConstantDensityCalabiBall
import GaussianTilt.MomentMapCalabiEstimate
import GaussianTilt.MomentMapCalabiCoercivity

/-! # Actual interior Calabi energy estimates with explicit lower-order constants -/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- A determinant-one inverse bound derived from the actual adjugate formula.
The deliberately coarse factorial bound avoids a spectral assumption. -/
lemma inverse_entry_bound_of_det_one {H : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
    (hH : H.det = 1) (hK : ∀ i j, |H i j| ≤ K) (i j : Fin n) :
    |H⁻¹ i j| ≤ (n.factorial : ℝ) * (max K 1)^n := by
  rw [matrix_inv_eq_adjugate_of_det_one hH, Matrix.adjugate_apply]
  have hh := Matrix.det_le (A := H.updateRow j (Pi.single i 1)) (abv := AbsoluteValue.abs)
    (x := max K 1) (by
      intro a b
      change |H.updateRow j (Pi.single i 1) a b| ≤ max K 1
      by_cases ha : a = j
      · subst a
        by_cases hb : b = i
        · simpa [Matrix.updateRow_apply, Pi.single_apply, hb] using le_max_right K 1
        · simpa [Matrix.updateRow_apply, Pi.single_apply, hb] using
            (show (0 : ℝ) ≤ max K 1 from (by positivity : (0 : ℝ) ≤ 1).trans (le_max_right K 1))
      · simp only [Matrix.updateRow_apply, ha, if_false]
        exact (hK a b).trans (le_max_left K 1))
  simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] using hh

lemma quadraticForm_upper_of_entry_bound {A : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hA : ∀ i j, |A i j| ≤ K) (v : CoordinateSpace n) :
    v ⬝ᵥ (A *ᵥ v) ≤ (n : ℝ)^2 * K * ‖(coordinateEquiv n).symm v‖^2 := by
  let N := ‖(coordinateEquiv n).symm v‖
  have hv (i : Fin n) : |v i| ≤ N := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ((coordinateEquiv n).symm v) i
  have ht (i j : Fin n) : v i * (A i j * v j) ≤ N * (K * N) := by
    calc
      _ ≤ |v i * (A i j * v j)| := le_abs_self _
      _ = |v i| * (|A i j| * |v j|) := by rw [abs_mul, abs_mul]
      _ ≤ N * (K * N) := mul_le_mul (hv i)
        (mul_le_mul (hA i j) (hv j) (abs_nonneg _) hK)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _)
  calc
    _ = ∑ i, ∑ j, v i * (A i j * v j) := by simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, N * (K * N) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ht i j))
    _ = _ := by simp [N]; ring

/-- Genuine Calabi interior energy bound on a Euclidean ball. The actual
constant-density equation supplies the quadratic differential inequality. -/
theorem calabiEnergy_bound_on_ball (hn : 0 < n) {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (c : CoordinateSpace n) {R Λ : ℝ} (hR : 0 < R) (hΛ : 0 ≤ Λ)
    (hH : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      (coordinateHessian u y).PosDef)
    (hMA : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      (coordinateHessian u y).det = 1)
    (hEll : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      ∀ v : CoordinateSpace n, v ⬝ᵥ ((coordinateHessian u y)⁻¹ *ᵥ v) ≤ Λ * ‖(coordinateEquiv n).symm v‖^2) :
    calabiEnergy u c ≤ 8 * (n : ℝ) * ((n : ℝ) + 6) * Λ / R^2 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnearMA {y : CoordinateSpace n}
      (hy : ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R) :
      ∀ᶠ z in 𝓝 y, (coordinateHessian u z).det = 1 := by
    have hopen : IsOpen {z : CoordinateSpace n | ‖(coordinateEquiv n).symm z - (coordinateEquiv n).symm c‖ < R} := by
      apply isOpen_lt _ continuous_const
      exact (((coordinateEquiv n).symm.continuous.sub continuous_const).norm)
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact hMA z hz
  have hh := calabi_ball_center_bound (contDiff_infty.mp (contDiff_calabiAdjugateEnergy hu) 2)
    (A := fun y => (coordinateHessian u y)⁻¹) c hR
    (by positivity : 0 < (1 : ℝ) / (2 * n)) hΛ
    (fun y hy => (hH y hy).inv.posSemidef) hEll (fun y hy => by
      have h := calabiAdjugateEnergy_differential_inequality hn hu y (hH y hy) (hnearMA hy)
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using h)
  have hdet : (coordinateHessian u c).det = 1 := hMA c (by simpa using hR)
  have he : calabiEnergy u c = calabiAdjugateEnergy u c := by
    unfold calabiEnergy calabiAdjugateEnergy cubicMetricEnergy
    rw [matrix_inv_eq_adjugate_of_det_one hdet]
  rw [he]
  convert hh using 1
  field_simp
  ring

/-- A coordinate Hessian bound supplies the inverse ellipticity constant
by finite adjugate algebra, so the resulting Calabi energy estimate assumes
no third-derivative bound. -/
theorem calabiEnergy_bound_on_ball_of_hessian_bound (hn : 0 < n) {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (c : CoordinateSpace n) {R K : ℝ} (hR : 0 < R)
    (hH : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      (coordinateHessian u y).PosDef)
    (hMA : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      (coordinateHessian u y).det = 1)
    (hK : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      ∀ i j, |coordinateHessian u y i j| ≤ K) :
    calabiEnergy u c ≤ 8 * (n : ℝ) * ((n : ℝ) + 6) *
      ((n : ℝ)^2 * n.factorial * (max K 1)^n) / R^2 := by
  apply calabiEnergy_bound_on_ball hn hu c hR (by positivity) hH hMA
  intro y hy v
  have hI : 0 ≤ (n.factorial : ℝ) * (max K 1)^n := by positivity
  have hh := quadraticForm_upper_of_entry_bound hI (inverse_entry_bound_of_det_one (hMA y hy) (hK y hy)) v
  convert hh using 1 <;> ring

/-- An explicit coordinate third-derivative bound after the genuine Calabi
ball estimate and the derived inverse-metric bound. -/
def calabiThirdDerivativeBound (n : ℕ) (K R : ℝ) : ℝ :=
  Real.sqrt ((max K 1)^3 * (8 * (n : ℝ) * ((n : ℝ) + 6) *
    ((n : ℝ)^2 * n.factorial * (max K 1)^n) / R^2))

/-- Actual individual third derivatives satisfy the explicit interior Calabi
estimate. The only derivative assumption is the already established
lower-order Hessian bound, which supplies ellipticity through det Hess=1. -/
theorem thirdDerivative_bound_on_ball_of_hessian_bound (hn : 0 < n) {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (c : CoordinateSpace n) {R K : ℝ} (hR : 0 < R)
    (hH : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      (coordinateHessian u y).PosDef)
    (hMA : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      (coordinateHessian u y).det = 1)
    (hK : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      ∀ i j, |coordinateHessian u y i j| ≤ K) (i j k : Fin n) :
    |coordinateThirdDerivative u c i j k| ≤ calabiThirdDerivativeBound n K R := by
  have hc : ‖(coordinateEquiv n).symm c - (coordinateEquiv n).symm c‖ < R := by simpa using hR
  have hHc := hH c hc
  have hcoe := cubic_coefficient_square_le_metric_energy (coordinateHessian u c) hHc
    (coordinateThirdDerivative u c) i j k
  change (coordinateThirdDerivative u c i j k)^2 ≤
    (coordinateHessian u c i i * coordinateHessian u c j j * coordinateHessian u c k k) * calabiEnergy u c at hcoe
  have hprod : 0 < coordinateHessian u c i i * coordinateHessian u c j j * coordinateHessian u c k k :=
    mul_pos (mul_pos (coordinateHessian_diagonal_pos hHc i) (coordinateHessian_diagonal_pos hHc j))
      (coordinateHessian_diagonal_pos hHc k)
  have hEn : 0 ≤ calabiEnergy u c :=
    (mul_le_mul_left hprod).mp (by simpa only [mul_zero] using (sq_nonneg _).trans hcoe)
  have hd (a : Fin n) : coordinateHessian u c a a ≤ max K 1 :=
    ((le_abs_self _).trans (hK c hc a a)).trans (le_max_left _ _)
  have hprodBound : coordinateHessian u c i i * coordinateHessian u c j j * coordinateHessian u c k k ≤
      (max K 1)^3 := by
    have hhh := mul_le_mul (mul_le_mul (hd i) (hd j)
      (coordinateHessian_diagonal_pos hHc j).le (by positivity)) (hd k)
      (coordinateHessian_diagonal_pos hHc k).le (by positivity)
    convert hhh using 1 <;> ring
  have henergy := calabiEnergy_bound_on_ball_of_hessian_bound hn hu c hR hH hMA hK
  have hsq := hcoe.trans ((mul_le_mul_of_nonneg_right hprodBound hEn).trans
    (mul_le_mul_of_nonneg_left henergy (by positivity)))
  unfold calabiThirdDerivativeBound
  apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
  simpa only [sq_abs] using hsq

end GaussianTilt.MomentMapRegularity
