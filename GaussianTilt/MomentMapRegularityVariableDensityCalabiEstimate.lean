import GaussianTilt.MomentMapRegularityVariableDensityCalabiReduction

/-! # Genuine normalized Calabi inequality with all variable-forcing errors -/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

theorem variableCalabiEnergy_inequality_at_identity (hn : 0 < n)
    {u F : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y))
    (hI : coordinateHessian u x = 1) :
    variableCalabiEnergy u F x ^ 2 / (2 * n) ≤ linearizedMA 1 (variableCalabiEnergy u F) x +
      3 * calabiContraction (coordinateHessian F x) 1 1 (coordinateThirdDerivative u x) (coordinateThirdDerivative u x) -
      2 * (∑ a, ∑ b, ∑ c, coordinateThirdDerivative F x a b c * coordinateThirdDerivative u x a b c) := by
  let T := coordinateThirdDerivative u x
  let Q := coordinateFourthDerivative u x
  let P := fun a b c l => coordinateFifthDerivative u x a b c l l
  have hT : calabiTensorSymm T := calabiTensorSymm_actual hu x
  have hQcycle : ∀ a b c l, Q a b c l = Q l a b c := by
    intro a b c l
    dsimp [Q]
    rw [coordinateFourthDerivative_swap34 hu x a b c l,
      coordinateFourthDerivative_swap23 hu x a b l c,
      coordinateFourthDerivative_swap12 hu x a l b c]
  have hQ : ∀ a b, (∑ l, Q a b l l) = (∑ i, ∑ j, T a i j * T b i j)+coordinateHessian F x a b :=
    fun a b => variable_density_fourth_contraction hu hF hMA hI a b
  have hP : ∀ a b c, (∑ l, P a b c l) =
      (∑ i, ∑ j, (Q a b i j * T c i j + Q a c i j * T b i j + Q b c i j * T a i j)) -
        2 * ∑ i, ∑ j, ∑ k, T a i j * T b j k * T c k i + coordinateThirdDerivative F x a b c :=
    fun a b c => variable_density_fifth_contraction hu hF hMA hI a b c
  have hSlice (l : Fin n) : (show Matrix (Fin n) (Fin n) ℝ from fun a b => coordinateThirdDerivative u x a b l) = calabiSlice T l := by
    ext a b
    exact (calabiTensorSymm_cycle hT l a b).symm
  have hlap := linearized_variableCalabiEnergy_at_identity hu hF hMA hI
  dsimp only at hlap
  simp_rw [hSlice] at hlap
  change linearizedMA 1 (variableCalabiEnergy u F) x =
    (∑ l, (3 * calabiContraction ((2 : ℝ) • (calabiSlice T l * calabiSlice T l) -
        (show Matrix (Fin n) (Fin n) ℝ from fun a b => Q a b l l)) 1 1 T T +
      6 * calabiContraction (-calabiSlice T l) (-calabiSlice T l) 1 T T +
      12 * calabiContraction (-calabiSlice T l) 1 1 (fun a b c => Q a b c l) T +
      2 * calabiContraction 1 1 1 (fun a b c => P a b c l) T +
      2 * calabiContraction 1 1 1 (fun a b c => Q a b c l) (fun a b c => Q a b c l))) at hlap
  rw [calabi_five_term_reduction_forced T Q P (coordinateHessian F x) (coordinateThirdDerivative F x) hT hQcycle hQ hP] at hlap
  have he : variableCalabiEnergy u F x = calabiCubicNorm T := by
    unfold variableCalabiEnergy
    rw [variableInverseHessian_eq_inverse hMA.self_of_nhds, hI, inv_one, cubicMetricEnergy_identity]
  rw [he, hlap]
  have hineq := calabi_normalized_tensor_inequality T Q hT.2
    (coordinateFourthDerivative_swap23 hu x) (coordinateFourthDerivative_swap34 hu x)
    (by simpa using hn)
  simp only [Fintype.card_fin] at hineq
  convert hineq using 1 <;> ring


lemma calabiCubicNorm_nonneg (T : Fin n → Fin n → Fin n → ℝ) : 0 ≤ calabiCubicNorm T :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- A componentwise forcing-Hessian bound controls its contraction with the
positive cubic Gram energy. -/
lemma calabi_forcing_hessian_bound (G : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Fin n → Fin n → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hG : ∀ a b, |G a b| ≤ K) :
    calabiContraction G 1 1 T T ≤ (n : ℝ)*K*calabiCubicNorm T := by
  have hterm (a i b c : Fin n) : G a i*T a b c*T i b c ≤ (K/2)*((T a b c)^2+(T i b c)^2) := by
    have hs : 2*|T a b c*T i b c| ≤ (T a b c)^2+(T i b c)^2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|T a b c|-|T i b c|), sq_abs (T a b c), sq_abs (T i b c)]
    calc
      G a i*T a b c*T i b c ≤ |G a i*T a b c*T i b c| := le_abs_self _
      _ = |G a i| * |T a b c*T i b c| := by rw [abs_mul, abs_mul, abs_mul]; ring
      _ ≤ K*|T a b c*T i b c| := mul_le_mul_of_nonneg_right (hG a i) (abs_nonneg _)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hs hK]
  have hsA : (∑ a : Fin n, ∑ i : Fin n, ∑ b : Fin n, ∑ c : Fin n, (T a b c)^2) =
      (n : ℝ)*calabiCubicNorm T := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    rfl
  have hsI : (∑ a : Fin n, ∑ i : Fin n, ∑ b : Fin n, ∑ c : Fin n, (T i b c)^2) =
      (n : ℝ)*calabiCubicNorm T := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rfl
  rw [calabiContraction_one_one]
  calc
    (∑ a, ∑ i, ∑ b, ∑ c, G a i*T a b c*T i b c) ≤
        ∑ a, ∑ i, ∑ b, ∑ c, (K/2)*((T a b c)^2+(T i b c)^2) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun i _ =>
        Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun c _ => hterm a i b c))))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hsA, hsI]
      ring

/-- Young's inequality controls the actual prescribed cubic forcing term. -/
lemma calabi_forcing_cubic_bound (G T : Fin n → Fin n → Fin n → ℝ) :
    -2*(∑ a, ∑ b, ∑ c, G a b c*T a b c) ≤ calabiCubicNorm G+calabiCubicNorm T := by
  have hp : 0 ≤ ∑ a, ∑ b, ∑ c, (G a b c+T a b c)^2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have he : (∑ a, ∑ b, ∑ c, (G a b c+T a b c)^2) =
      calabiCubicNorm G+2*(∑ a, ∑ b, ∑ c, G a b c*T a b c)+calabiCubicNorm T := by
    simp only [calabiCubicNorm, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    ring
  rw [he] at hp
  linarith

lemma calabiCubicNorm_le_of_component_bound (G : Fin n → Fin n → Fin n → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hG : ∀ a b c, |G a b c| ≤ K) :
    calabiCubicNorm G ≤ (n : ℝ)^3*K^2 := by
  calc
    calabiCubicNorm G ≤ ∑ _a : Fin n, ∑ _b : Fin n, ∑ _c : Fin n, K^2 := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro b _
      apply Finset.sum_le_sum; intro c _
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (G a b c)) (hG a b c) 2
    _ = _ := by simp; ring

/-- The actual normalized variable-density Calabi estimate after bounding
all forcing errors. The cubic forcing enters through its full squared norm. -/
theorem variableCalabiEnergy_inequality_at_identity_of_forcing_bounds (hn : 0 < n)
    {u F : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F)
    {x : CoordinateSpace n} (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y))
    (hI : coordinateHessian u x = 1) {K₂ B₃ : ℝ} (hK₂ : 0 ≤ K₂)
    (hF₂ : ∀ a b, |coordinateHessian F x a b| ≤ K₂)
    (hF₃ : calabiCubicNorm (coordinateThirdDerivative F x) ≤ B₃) :
    variableCalabiEnergy u F x^2/(2*n) ≤ linearizedMA 1 (variableCalabiEnergy u F) x +
      (3*(n : ℝ)*K₂+1)*variableCalabiEnergy u F x+B₃ := by
  have he : variableCalabiEnergy u F x = calabiCubicNorm (coordinateThirdDerivative u x) := by
    unfold variableCalabiEnergy
    rw [variableInverseHessian_eq_inverse hMA.self_of_nhds, hI, inv_one, cubicMetricEnergy_identity]
  have hbase := variableCalabiEnergy_inequality_at_identity hn hu hF hMA hI
  have htwo := calabi_forcing_hessian_bound (coordinateHessian F x) (coordinateThirdDerivative u x) hK₂ hF₂
  have hthree := calabi_forcing_cubic_bound (coordinateThirdDerivative F x) (coordinateThirdDerivative u x)
  rw [← he] at htwo hthree
  nlinarith

end GaussianTilt.MomentMapRegularity
