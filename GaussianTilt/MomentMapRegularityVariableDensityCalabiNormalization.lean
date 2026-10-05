import GaussianTilt.MomentMapRegularityVariableDensityCalabiEstimate
import GaussianTilt.MomentMapVariableCalabiAffine
import GaussianTilt.MomentMapRegularityConstantDensityNormalized

/-! # Actual affine normalization of the variable-density Calabi estimate -/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma variableCalabiEnergy_eq_forced (u F : CoordinateSpace n → ℝ) :
    variableCalabiEnergy u F = forcedCalabiEnergy F u := by
  funext x
  unfold variableCalabiEnergy variableInverseHessian forcedCalabiEnergy calabiAdjugateEnergy
  rw [cubicMetricEnergy_smul, ← Real.exp_nat_mul]
  congr 2
  ring

lemma congruence_entry_bound {G R : Matrix (Fin n) (Fin n) ℝ} {K L : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hG : ∀ a b, |G a b| ≤ K) (hR : ∀ a b, |R a b| ≤ L)
    (i j : Fin n) : |(Rᵀ*G*R) i j| ≤ (n : ℝ)^2*L^2*K := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  calc
    |∑ a, ∑ b, R b i*G b a*R a j| ≤ ∑ a, ∑ b, |R b i*G b a*R a j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _a : Fin n, ∑ _b : Fin n, L*K*L := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro b _
      simp only [abs_mul]
      exact mul_le_mul (mul_le_mul (hR b i) (hG b a) (abs_nonneg _) hL)
        (hR a j) (abs_nonneg _) (mul_nonneg hL hK)
    _ = _ := by simp; ring

lemma cubicTransform_entry_bound {G : Fin n → Fin n → Fin n → ℝ}
    {R : Matrix (Fin n) (Fin n) ℝ} {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hG : ∀ a b c, |G a b c| ≤ K) (hR : ∀ a b, |R a b| ≤ L) (i j k : Fin n) :
    |cubicTransform R G i j k| ≤ (n : ℝ)^3*L^3*K := by
  unfold cubicTransform
  calc
    _ ≤ ∑ a, ∑ b, ∑ c, |R a i*R b j*R c k*G a b c| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))))
    _ ≤ ∑ _a : Fin n, ∑ _b : Fin n, ∑ _c : Fin n, L*L*L*K := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro b _
      apply Finset.sum_le_sum; intro c _
      simp only [abs_mul]
      exact mul_le_mul (mul_le_mul (mul_le_mul (hR a i) (hR b j) (abs_nonneg _) hL)
        (hR c k) (abs_nonneg _) (mul_nonneg hL hL)) (hG a b c) (abs_nonneg _) (by positivity)
    _ = _ := by simp; ring

lemma coordinateThirdDerivative_add_const (f : CoordinateSpace n → ℝ) (c : ℝ)
    (x : CoordinateSpace n) (i j k : Fin n) :
    coordinateThirdDerivative (fun y => f y+c) x i j k = coordinateThirdDerivative f x i j k := by
  unfold coordinateThirdDerivative
  simp only [coordinateHessian_add_const]

lemma hessian_affineLogDensity {F : CoordinateSpace n → ℝ} (hF : ContDiff ℝ 2 F)
    (R : Matrix (Fin n) (Fin n) ℝ) (y : CoordinateSpace n) :
    coordinateHessian (affineLogDensity F R) y = Rᵀ*coordinateHessian F (R*ᵥy)*R := by
  unfold affineLogDensity
  rw [coordinateHessian_add_const]
  exact coordinateHessian_comp_matrix hF R y

lemma third_affineLogDensity {F : CoordinateSpace n → ℝ} (hF : ContDiff ℝ ∞ F)
    (R : Matrix (Fin n) (Fin n) ℝ) (y : CoordinateSpace n) :
    coordinateThirdDerivative (affineLogDensity F R) y = cubicTransform R (coordinateThirdDerivative F (R*ᵥy)) := by
  funext i j k
  unfold affineLogDensity
  rw [coordinateThirdDerivative_add_const]
  exact congrFun (congrFun (congrFun (coordinateThirdDerivative_comp_matrix hF R y) i) j) k

/-- The genuine variable-density Calabi differential inequality in arbitrary
Hessian coordinates. All forcing derivatives are transformed by the actual
inverse square root; no normalized PDE or energy identity is assumed. -/
theorem variableCalabiEnergy_differential_inequality (hn : 0 < n)
    {u F : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F)
    (x : CoordinateSpace n) (hH : (coordinateHessian u x).PosDef)
    (hMA : ∀ᶠ z in 𝓝 x, (coordinateHessian u z).det = Real.exp (F z))
    {L K₂ K₃ : ℝ} (hL : 0 ≤ L) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃)
    (hRbound : ∀ a b, |Whitening.inverseRoot (coordinateHessian u x) a b| ≤ L)
    (hF₂ : ∀ a b, |coordinateHessian F x a b| ≤ K₂)
    (hF₃ : ∀ a b c, |coordinateThirdDerivative F x a b c| ≤ K₃) :
    variableCalabiEnergy u F x^2/(2*n) ≤
      linearizedMA (coordinateHessian u x)⁻¹ (variableCalabiEnergy u F) x +
        (3*(n : ℝ)*((n : ℝ)^2*L^2*K₂)+1)*variableCalabiEnergy u F x +
        (n : ℝ)^3*((n : ℝ)^3*L^3*K₃)^2 := by
  let R := Whitening.inverseRoot (coordinateHessian u x)
  have hRp : R.PosDef := (Whitening.root_posDef hH).inv
  have hRd : R.det ≠ 0 := hRp.det_pos.ne'
  have hRs : Rᵀ = R := (Whitening.inverseRoot_symm hH).eq
  let y := R⁻¹ *ᵥ x
  have hRy : R *ᵥ y = x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv R (isUnit_iff_ne_zero.mpr hRd), Matrix.one_mulVec]
  let v := u ∘ coordinateMatrixMap R
  let G := affineLogDensity F R
  have hv : ContDiff ℝ ∞ v := hu.comp (coordinateMatrixMap R).contDiff
  have hG : ContDiff ℝ ∞ G := (hF.comp (coordinateMatrixMap R).contDiff).add contDiff_const
  have hHv : coordinateHessian v y = 1 := by
    rw [coordinateHessian_comp_matrix (contDiff_infty.mp hu 2), hRy, hRs]
    have hh := Whitening.inverseRoot_covariance hH
    change R * coordinateHessian u x * Rᵀ = 1 at hh
    simpa only [hRs] using hh
  have hmetric : R*(1 : Matrix (Fin n) (Fin n) ℝ)*Rᵀ = (coordinateHessian u x)⁻¹ := by
    rw [Matrix.mul_one, hRs]
    dsimp [R, Whitening.inverseRoot]
    rw [← Matrix.mul_inv_rev, Whitening.root_mul_root hH.posSemidef]
  have hedet : Real.exp (2*Real.log |R.det|) = R.det^2 := by
    rw [show (2 : ℝ)*Real.log |R.det| = (2 : ℕ)*Real.log |R.det| by norm_num,
      Real.exp_nat_mul, Real.exp_log (abs_pos.mpr hRd), sq_abs]
  have hMAv : ∀ᶠ z in 𝓝 y, (coordinateHessian v z).det = Real.exp (G z) := by
    have ht : Tendsto (coordinateMatrixMap R) (𝓝 y) (𝓝 x) := by
      simpa only [coordinateMatrixMap_apply, hRy] using (coordinateMatrixMap R).continuous.tendsto y
    filter_upwards [ht.eventually hMA] with z hz
    rw [coordinateHessian_comp_matrix (contDiff_infty.mp hu 2), Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    change R.det*(coordinateHessian u (coordinateMatrixMap R z)).det*R.det = _
    rw [hz]
    change R.det*Real.exp (F (R*ᵥz))*R.det = Real.exp (F (R*ᵥz)+2*Real.log |R.det|)
    rw [Real.exp_add, hedet]
    ring
  have hG₂ : ∀ a b, |coordinateHessian G y a b| ≤ (n : ℝ)^2*L^2*K₂ := by
    intro a b
    rw [hessian_affineLogDensity (contDiff_infty.mp hF 2), hRy]
    exact congruence_entry_bound hK₂ hL hF₂ hRbound a b
  have hG₃ : calabiCubicNorm (coordinateThirdDerivative G y) ≤ (n : ℝ)^3*((n : ℝ)^3*L^3*K₃)^2 := by
    rw [third_affineLogDensity hF, hRy]
    apply calabiCubicNorm_le_of_component_bound _ (by positivity)
    exact cubicTransform_entry_bound hK₃ hL hF₃ hRbound
  have hh := variableCalabiEnergy_inequality_at_identity_of_forcing_bounds hn hv hG hMAv hHv
    (by positivity) hG₂ hG₃
  have henergy : variableCalabiEnergy v G y = variableCalabiEnergy u F x := by
    rw [variableCalabiEnergy_eq_forced, variableCalabiEnergy_eq_forced,
      forcedCalabiEnergy_comp_matrix hu R hRd]
    change forcedCalabiEnergy F u (R*ᵥy) = _
    rw [hRy]
  have hlin : linearizedMA 1 (variableCalabiEnergy v G) y =
      linearizedMA (coordinateHessian u x)⁻¹ (variableCalabiEnergy u F) x := by
    rw [variableCalabiEnergy_eq_forced, variableCalabiEnergy_eq_forced]
    have hh := linearized_forcedCalabiEnergy_comp_matrix hF hu (coordinateHessian u x)⁻¹ 1 R hRd hmetric y
    rwa [hRy] at hh
  rwa [henergy, hlin] at hh

end GaussianTilt.MomentMapRegularity
