import GaussianTilt.MomentMapRegularityVariableDensityCalabiNormalization
import GaussianTilt.MomentMapRegularityVariableDensityCalabiCutoff
import GaussianTilt.MomentMapRegularityConstantDensityCalabiBounds

/-! # Genuine variable-density interior Calabi energy and cubic estimates -/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma inverseRoot_entry_bound_of_quadratic_bound {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hEll : ∀ v : CoordinateSpace n, v ⬝ᵥ (H⁻¹ *ᵥ v) ≤ Λ*‖(coordinateEquiv n).symm v‖^2)
    (i j : Fin n) : |Whitening.inverseRoot H i j| ≤ Λ+1 := by
  let R := Whitening.inverseRoot H
  have hRs : Rᵀ = R := (Whitening.inverseRoot_symm hH).eq
  have hRR : Rᵀ*R = H⁻¹ := by
    rw [hRs]
    dsimp [R, Whitening.inverseRoot]
    rw [← Matrix.mul_inv_rev, Whitening.root_mul_root hH.posSemidef]
  have hdiag : H⁻¹ j j ≤ Λ := by
    have hh := hEll (Pi.single j 1)
    simpa [Matrix.mulVec_single_one, single_dotProduct, Matrix.col, coordinateEquiv,
      EuclideanSpace.norm_eq, PiLp.norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq] using hh
  have hs : R i j^2 ≤ H⁻¹ j j := by
    rw [← hRR]
    change R i j^2 ≤ ∑ k, R k j*R k j
    simpa only [pow_two] using Finset.single_le_sum (f := fun k => R k j^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  change |R i j| ≤ Λ+1
  nlinarith [sq_abs (R i j), sq_nonneg (|R i j|-(1/2 : ℝ))]

def variableCalabiLinearError (n : ℕ) (Λ K₂ : ℝ) : ℝ :=
  3*(n : ℝ)*((n : ℝ)^2*(Λ+1)^2*K₂)+1

def variableCalabiConstantError (n : ℕ) (Λ K₃ : ℝ) : ℝ :=
  (n : ℝ)^3*((n : ℝ)^3*(Λ+1)^3*K₃)^2

def variableCalabiBallConstant (n : ℕ) (Λ K₂ K₃ R : ℝ) : ℝ :=
  1+8*(n : ℝ)*((n : ℝ)+6)*Λ/R^2+
    2*(n : ℝ)*(variableCalabiLinearError n Λ K₂+variableCalabiConstantError n Λ K₃)

/-- Actual cubic energy bound for a spatially variable logarithmic density.
The true first/second/third forcing derivatives are retained through the
calculus, and the last two enter these explicit lower-order error constants. -/
theorem variable_calabiEnergy_bound_on_ball (hn : 0 < n)
    {u F : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F)
    (c : CoordinateSpace n) {R Λ K₂ K₃ : ℝ} (hR : 0 < R) (hΛ : 0 ≤ Λ)
    (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃)
    (hH : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R →
      (coordinateHessian u y).PosDef)
    (hMA : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R →
      (coordinateHessian u y).det = Real.exp (F y))
    (hEll : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R →
      ∀ v : CoordinateSpace n, v ⬝ᵥ ((coordinateHessian u y)⁻¹ *ᵥ v) ≤ Λ*‖(coordinateEquiv n).symm v‖^2)
    (hF₂ : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R →
      ∀ a b, |coordinateHessian F y a b| ≤ K₂)
    (hF₃ : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R →
      ∀ a b d, |coordinateThirdDerivative F y a b d| ≤ K₃) :
    calabiEnergy u c ≤ variableCalabiBallConstant n Λ K₂ K₃ R := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnearMA {y : CoordinateSpace n}
      (hy : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R) :
      ∀ᶠ z in 𝓝 y, (coordinateHessian u z).det = Real.exp (F z) := by
    have hopen : IsOpen {z : CoordinateSpace n | ‖(coordinateEquiv n).symm z-(coordinateEquiv n).symm c‖ < R} := by
      apply isOpen_lt _ continuous_const
      exact (((coordinateEquiv n).symm.continuous.sub continuous_const).norm)
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact hMA z hz
  have ha : 0 ≤ variableCalabiLinearError n Λ K₂ := by unfold variableCalabiLinearError; positivity
  have hb : 0 ≤ variableCalabiConstantError n Λ K₃ := by unfold variableCalabiConstantError; positivity
  have hh := forced_calabi_ball_center_bound (contDiff_infty.mp (contDiff_variableCalabiEnergy hu hF) 2)
    (A := fun y => (coordinateHessian u y)⁻¹) c hR
    (by positivity : 0 < (1 : ℝ)/(2*n)) hΛ ha hb
    (fun y hy => (hH y hy).inv.posSemidef) hEll (fun y hy => by
      have h := variableCalabiEnergy_differential_inequality hn hu hF y (hH y hy) (hnearMA hy)
        (by positivity : 0 ≤ Λ+1) hK₂ hK₃
        (inverseRoot_entry_bound_of_quadratic_bound (hH y hy) hΛ (hEll y hy)) (hF₂ y hy) (hF₃ y hy)
      simpa only [div_eq_mul_inv, one_mul, mul_comm, variableCalabiLinearError, variableCalabiConstantError] using h)
  have hdet : (coordinateHessian u c).det = Real.exp (F c) := hMA c (by simpa using hR)
  have he : variableCalabiEnergy u F c = calabiEnergy u c := by
    unfold variableCalabiEnergy calabiEnergy cubicMetricEnergy
    rw [variableInverseHessian_eq_inverse hdet]
  rw [he] at hh
  unfold variableCalabiBallConstant
  convert hh using 1
  field_simp
  ring

lemma adjugate_entry_bound_of_entry_bound {H : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
    (hK : ∀ i j, |H i j| ≤ K) (i j : Fin n) :
    |H.adjugate i j| ≤ (n.factorial : ℝ)*(max K 1)^n := by
  rw [Matrix.adjugate_apply]
  have hh := Matrix.det_le (A := H.updateRow j (Pi.single i 1)) (abv := AbsoluteValue.abs)
    (x := max K 1) (by
      intro a b
      change |H.updateRow j (Pi.single i 1) a b| ≤ max K 1
      by_cases ha : a = j
      · subst a
        by_cases hb : b = i
        · simp [Matrix.updateRow_apply, Pi.single_apply, hb]
        · simp [Matrix.updateRow_apply, Pi.single_apply, hb]
      · simp only [Matrix.updateRow_apply, ha, if_false]
        exact (hK a b).trans (le_max_left K 1))
  simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] using hh

lemma inverse_entry_bound_of_log_det {H : Matrix (Fin n) (Fin n) ℝ} {F K K₀ : ℝ}
    (hdet : H.det = Real.exp F) (hF : -K₀ ≤ F) (hK : ∀ i j, |H i j| ≤ K) (i j : Fin n) :
    |H⁻¹ i j| ≤ Real.exp K₀*((n.factorial : ℝ)*(max K 1)^n) := by
  rw [Matrix.inv_def, hdet, Ring.inverse_eq_inv', ← Real.exp_neg]
  change |Real.exp (-F)*H.adjugate i j| ≤ _
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (Real.exp_le_exp.mpr (by linarith))
    (adjugate_entry_bound_of_entry_bound hK i j) (abs_nonneg _) (Real.exp_pos _).le

def variableInverseCoefficientBound (n : ℕ) (K K₀ : ℝ) : ℝ :=
  (n : ℝ)^2*(Real.exp K₀*((n.factorial : ℝ)*(max K 1)^n))

/-- The actual variable-density inverse coefficient bound is derived from
its determinant and the lower-order Hessian bound. -/
theorem variable_calabiEnergy_bound_on_ball_of_hessian_bound (hn : 0 < n)
    {u F : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F)
    (c : CoordinateSpace n) {R K K₀ K₂ K₃ : ℝ} (hR : 0 < R) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃)
    (hH : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R → (coordinateHessian u y).PosDef)
    (hMA : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R →
      (coordinateHessian u y).det = Real.exp (F y))
    (hK : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R →
      ∀ i j, |coordinateHessian u y i j| ≤ K)
    (hF₀ : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R → -K₀ ≤ F y)
    (hF₂ : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R →
      ∀ a b, |coordinateHessian F y a b| ≤ K₂)
    (hF₃ : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R →
      ∀ a b d, |coordinateThirdDerivative F y a b d| ≤ K₃) :
    calabiEnergy u c ≤ variableCalabiBallConstant n (variableInverseCoefficientBound n K K₀) K₂ K₃ R := by
  apply variable_calabiEnergy_bound_on_ball hn hu hF c hR
    (by unfold variableInverseCoefficientBound; positivity) hK₂ hK₃ hH hMA _ hF₂ hF₃
  intro y hy v
  exact quadraticForm_upper_of_entry_bound (by positivity)
    (inverse_entry_bound_of_log_det (hMA y hy) (hF₀ y hy) (hK y hy)) v

def variableThirdDerivativeBound (n : ℕ) (K K₀ K₂ K₃ R : ℝ) : ℝ :=
  Real.sqrt ((max K 1)^3*variableCalabiBallConstant n (variableInverseCoefficientBound n K K₀) K₂ K₃ R)

/-- Genuine individual C³ a priori bound for the variable-density equation.
All inverse, energy and third-derivative estimates are derived. -/
theorem variable_thirdDerivative_bound_on_ball_of_hessian_bound (hn : 0 < n)
    {u F : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F)
    (c : CoordinateSpace n) {R K K₀ K₂ K₃ : ℝ} (hR : 0 < R) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃)
    (hH : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R → (coordinateHessian u y).PosDef)
    (hMA : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R →
      (coordinateHessian u y).det = Real.exp (F y))
    (hK : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R →
      ∀ i j, |coordinateHessian u y i j| ≤ K)
    (hF₀ : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R → -K₀ ≤ F y)
    (hF₂ : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R →
      ∀ a b, |coordinateHessian F y a b| ≤ K₂)
    (hF₃ : ∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < R →
      ∀ a b d, |coordinateThirdDerivative F y a b d| ≤ K₃) (i j k : Fin n) :
    |coordinateThirdDerivative u c i j k| ≤ variableThirdDerivativeBound n K K₀ K₂ K₃ R := by
  have hc : ‖(coordinateEquiv n).symm c-(coordinateEquiv n).symm c‖ < R := by simpa using hR
  have hHc := hH c hc
  have hcoe := cubic_coefficient_square_le_metric_energy (coordinateHessian u c) hHc
    (coordinateThirdDerivative u c) i j k
  change (coordinateThirdDerivative u c i j k)^2 ≤
    (coordinateHessian u c i i*coordinateHessian u c j j*coordinateHessian u c k k)*calabiEnergy u c at hcoe
  have hprod : 0 < coordinateHessian u c i i*coordinateHessian u c j j*coordinateHessian u c k k :=
    mul_pos (mul_pos (coordinateHessian_diagonal_pos hHc i) (coordinateHessian_diagonal_pos hHc j))
      (coordinateHessian_diagonal_pos hHc k)
  have hEn : 0 ≤ calabiEnergy u c :=
    (mul_le_mul_left hprod).mp (by simpa only [mul_zero] using (sq_nonneg _).trans hcoe)
  have hd (a : Fin n) : coordinateHessian u c a a ≤ max K 1 :=
    ((le_abs_self _).trans (hK c hc a a)).trans (le_max_left _ _)
  have hprodBound : coordinateHessian u c i i*coordinateHessian u c j j*coordinateHessian u c k k ≤ (max K 1)^3 := by
    have hh := mul_le_mul (mul_le_mul (hd i) (hd j) (coordinateHessian_diagonal_pos hHc j).le (by positivity))
      (hd k) (coordinateHessian_diagonal_pos hHc k).le (by positivity)
    convert hh using 1 <;> ring
  have henergy := variable_calabiEnergy_bound_on_ball_of_hessian_bound hn hu hF c hR hK₂ hK₃ hH hMA hK hF₀ hF₂ hF₃
  have hsq := hcoe.trans ((mul_le_mul_of_nonneg_right hprodBound hEn).trans
    (mul_le_mul_of_nonneg_left henergy (by positivity)))
  have hB : 0 ≤ variableCalabiBallConstant n (variableInverseCoefficientBound n K K₀) K₂ K₃ R := by
    unfold variableCalabiBallConstant variableCalabiLinearError variableCalabiConstantError variableInverseCoefficientBound
    positivity
  unfold variableThirdDerivativeBound
  apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg (by positivity) hB)).mpr
  simpa only [sq_abs] using hsq

end GaussianTilt.MomentMapRegularity
