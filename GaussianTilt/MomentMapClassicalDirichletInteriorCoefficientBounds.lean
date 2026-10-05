import GaussianTilt.MomentMapClassicalDirichletInteriorThirdBounds

/-!
# Genuine scale-uniform first coefficient derivatives

The explicit Calabi estimate has the actual inverse-radius scaling. Combined
with the differentiated inverse identity, it controls r D(Hess(u)⁻¹) without
an assumed coefficient Hölder or Lipschitz estimate.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma variableThirdDerivativeBound_scaled {K K₀ K₂ K₃ r : ℝ}
    (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃) (hr : 0 < r) (hr1 : r ≤ 1) :
    r*variableThirdDerivativeBound n K K₀ K₂ K₃ r ≤ variableThirdDerivativeBound n K K₀ K₂ K₃ 1 := by
  let Λ := variableInverseCoefficientBound n K K₀
  have hΛ : 0 ≤ Λ := by dsimp [Λ,variableInverseCoefficientBound]; positivity
  have hErr : 0 ≤ variableCalabiLinearError n Λ K₂+variableCalabiConstantError n Λ K₃ := by
    unfold variableCalabiLinearError variableCalabiConstantError
    positivity
  have hCr : 0 ≤ variableCalabiBallConstant n Λ K₂ K₃ r := by
    unfold variableCalabiBallConstant
    positivity
  have hC1 : 0 ≤ variableCalabiBallConstant n Λ K₂ K₃ 1 := by
    unfold variableCalabiBallConstant
    positivity
  have hrsq : r^2 ≤ 1 := by nlinarith
  have hscale : r^2*variableCalabiBallConstant n Λ K₂ K₃ r ≤ variableCalabiBallConstant n Λ K₂ K₃ 1 := by
    have he : r^2*variableCalabiBallConstant n Λ K₂ K₃ r =
        r^2+8*(n:ℝ)*((n:ℝ)+6)*Λ+
        r^2*(2*(n:ℝ)*(variableCalabiLinearError n Λ K₂+variableCalabiConstantError n Λ K₃)) := by
      unfold variableCalabiBallConstant
      field_simp
      <;> ring
    rw [he]
    unfold variableCalabiBallConstant
    norm_num only [one_pow,div_one]
    have hmul := mul_le_mul_of_nonneg_right hrsq (mul_nonneg (by positivity : 0 ≤ 2*(n:ℝ)) hErr)
    nlinarith
  have hKcube : 0 ≤ (max K 1)^3 := by positivity
  apply (sq_le_sq₀ (mul_nonneg hr.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp
  rw [mul_pow,Real.sq_sqrt (mul_nonneg hKcube hCr),Real.sq_sqrt (mul_nonneg hKcube hC1)]
  nlinarith [mul_le_mul_of_nonneg_left hscale hKcube]

lemma coordinateDerivative_inverse_hessian {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y)) (k i j : Fin n) :
    coordinateDerivative k (fun y => (coordinateHessian u y)⁻¹ i j) x =
      -((coordinateHessian u x)⁻¹ * matrixCoordinateDerivative (coordinateHessian u) k x *
        (coordinateHessian u x)⁻¹) i j := by
  have he : (fun y => (coordinateHessian u y)⁻¹ i j) =ᶠ[𝓝 x]
      (fun y => variableInverseHessian u F y i j) :=
    hMA.mono (fun y hy => congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
      (variableInverseHessian_eq_inverse hy).symm)
  rw [coordinateDerivative_congr_nhds he]
  change matrixCoordinateDerivative (variableInverseHessian u F) k x i j = _
  rw [variable_inverse_first hu hF hMA,variableInverseHessian_eq_inverse hMA.self_of_nhds]
  rfl

lemma triple_matrix_entry_bound {A B C : Matrix (Fin n) (Fin n) ℝ} {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b) (hC : ∀ i j, |C i j| ≤ c)
    (i j : Fin n) : |(A*B*C) i j| ≤ (n:ℝ)^2*a*b*c := by
  have ht (l m : Fin n) : |A i m*B m l*C l j| ≤ a*b*c := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (hA i m) (hB m l) (abs_nonneg _) ha) (hC l j)
      (abs_nonneg _) (mul_nonneg ha hb)
  simp only [Matrix.mul_apply,Finset.sum_mul]
  calc
    _ ≤ ∑ l, ∑ m, |A i m*B m l*C l j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun l _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _l : Fin n, ∑ _m : Fin n, (a*b*c) :=
      Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun m _ => ht l m))
    _ = _ := by simp; ring

lemma scaled_inverse_hessian_derivative_bound {u F : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y))
    {r I T : ℝ} (hr : 0 ≤ r) (hI : 0 ≤ I) (hT : 0 ≤ T)
    (hInv : ∀ i j, |(coordinateHessian u x)⁻¹ i j| ≤ I)
    (hThird : ∀ i j k, r*|coordinateThirdDerivative u x i j k| ≤ T) (k i j : Fin n) :
    r*|coordinateDerivative k (fun y => (coordinateHessian u y)⁻¹ i j) x| ≤ (n:ℝ)^2*I*T*I := by
  rw [coordinateDerivative_inverse_hessian hu hF hMA,abs_neg]
  have hD : ∀ a b, |(r • matrixCoordinateDerivative (coordinateHessian u) k x) a b| ≤ T := by
    intro a b
    simpa only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg hr] using hThird a b k
  have hh := triple_matrix_entry_bound hI hT hI hInv hD hInv i j
  simpa only [Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg hr] using hh

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- Scale-uniform actual first derivatives of the inverse Hessian on every
interior ball of radius r≤1, uniformly in the forcing homotopy parameter. -/
theorem dirichletContinuation_scaled_inverse_derivative_bound [NeZero n] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ u : CoordinateSpace n → ℝ,
      ContDiff ℝ ∞ u →
      (∀ y ∈ interior {z | d.coordinateDefining z ≤ 0}, (coordinateHessian u y).PosDef) →
      (∀ y ∈ frontier {z | d.coordinateDefining z ≤ 0}, u y = 0) →
      (∀ y ∈ interior {z | d.coordinateDefining z ≤ 0},
        (coordinateHessian u y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ x : CoordinateSpace n, ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r →
        y ∈ interior {z | d.coordinateDefining z ≤ 0}) →
      ∀ k i j, r*|coordinateDerivative k (fun y => (coordinateHessian u y)⁻¹ i j) x| ≤ C := by
  obtain ⟨K,hK,hKH⟩ := d.dirichletContinuation_uniform_hessian
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K₂,hK₂,hF₂⟩ := dirichletContinuationDensity_uniform_log_hessian d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K₃,hK₃,hF₃⟩ := dirichletContinuationDensity_uniform_log_thirdDerivatives d.coordinate_body_compact
    d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  let K₀ := max (-Real.log c) 0
  let T := variableThirdDerivativeBound n K K₀ K₂ K₃ 1
  let I := ((n.factorial:ℝ)*(max K 1)^n)/c
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  have hI : 0 ≤ I := by dsimp [I]; positivity
  refine ⟨(n:ℝ)^2*I*T*I,by positivity,?_⟩
  intro t ht u hu hH hub hMA x r hr hr1 hball k i j
  have hx : x ∈ interior {y | d.coordinateDefining y ≤ 0} := hball x (by simpa using hr)
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.log _ (fun y => (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y)).ne')
    exact (contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp
      (contDiff_const.prodMk contDiff_id)
  have hMAlog (y : CoordinateSpace n) (hy : y ∈ interior {z | d.coordinateDefining z ≤ 0}) :
      (coordinateHessian u y).det = Real.exp (F y) := by
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
    exact hMA y hy
  have hnear : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact hMAlog y hy
  have hInv : ∀ a b, |(coordinateHessian u x)⁻¹ a b| ≤ I :=
    inverse_entry_bound_of_det_lower hc (by rw [hMA x hx]; exact (hdens t ht x (interior_subset hx)).1)
      (hKH t ht u hu hH hub hMA x (interior_subset hx))
  have hThird (a b l : Fin n) : r*|coordinateThirdDerivative u x a b l| ≤ T := by
    have hh := variable_thirdDerivative_bound_on_ball_of_hessian_bound (Nat.pos_of_ne_zero (NeZero.ne n))
      hu hF x hr hK₂ hK₃ (fun y hy => hH y (hball y hy))
      (fun y hy => hMAlog y (hball y hy))
      (fun y hy => hKH t ht u hu hH hub hMA y (interior_subset (hball y hy)))
      (fun y hy => (show -K₀ ≤ Real.log c from by dsimp [K₀]; linarith [le_max_left (-Real.log c) 0]).trans
        (Real.log_le_log hc (hdens t ht y (interior_subset (hball y hy))).1))
      (fun y hy => hF₂ t ht y (interior_subset (hball y hy)))
      (fun y hy => hF₃ t ht y (interior_subset (hball y hy))) a b l
    exact (mul_le_mul_of_nonneg_left hh hr.le).trans (variableThirdDerivativeBound_scaled hK₂ hK₃ hr hr1)
  exact scaled_inverse_hessian_derivative_bound hu hF hnear hr.le hI hT hInv hThird k i j

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
