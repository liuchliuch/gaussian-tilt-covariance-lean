import GaussianTilt.MomentMapLinearDirichletQuantitativeChartRaw

/-! # Quantitative finite congruence estimates for the actual chart -/
noncomputable section
set_option maxHeartbeats 2000000
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

lemma matrix_mulVec_square_bound (J : Matrix (Fin n) (Fin n) ℝ)
    {C : ℝ} (hJ : ∀ i k, |J i k| ≤ C) (v : Fin n → ℝ) :
    (∑ i, (J *ᵥ v) i ^ 2) ≤ (n:ℝ)^2*C^2*(∑ i, v i^2) := by
  have hb (i : Fin n) : (J *ᵥ v) i ^2 ≤ (n:ℝ)*C^2*(∑ k, v k^2) := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (f := fun k => J i k) (g := v)
    have hr : (∑ k, J i k^2) ≤ (n:ℝ)*C^2 := by
      calc
        _ ≤ ∑ _k : Fin n, C^2 := Finset.sum_le_sum (fun k _ => by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (J i k)) (hJ i k) 2)
        _ = _ := by simp
    exact hc.trans (mul_le_mul_of_nonneg_right hr (by positivity))
  calc
    _ ≤ ∑ _i : Fin n, (n:ℝ)*C^2*(∑ k, v k^2) := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp; ring

lemma matrix_congruence_quadratic (J A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    dotProduct v ((J*A*Jᵀ)*ᵥv) = dotProduct (Jᵀ*ᵥv) (A*ᵥ(Jᵀ*ᵥv)) := by
  rw [Matrix.mul_assoc,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec]
  rw [Matrix.mulVec_transpose J v]

/-- A bounded actual right inverse produces quantitative lower ellipticity. -/
theorem matrix_congruence_ellipticity (A J G : Matrix (Fin n) (Fin n) ℝ)
    {lam Λ C : ℝ} (hC : 0 < C) (hn : 0 < n) (hlam : 0 ≤ lam) (hΛ : 0 ≤ Λ)
    (hJG : J*G=1) (hJ : ∀ i k, |J i k| ≤ C) (hG : ∀ i k, |G i k| ≤ C)
    (hlo : ∀ v, lam*(∑ i, v i^2) ≤ dotProduct v (A*ᵥv))
    (hhi : ∀ v, dotProduct v (A*ᵥv) ≤ Λ*(∑ i, v i^2)) :
    ∀ v, lam/((n:ℝ)^2*C^2)*(∑ i, v i^2) ≤ dotProduct v ((J*A*Jᵀ)*ᵥv) ∧
      dotProduct v ((J*A*Jᵀ)*ᵥv) ≤ (Λ*((n:ℝ)^2*C^2))*(∑ i, v i^2) := by
  intro v
  have hN : 0 < (n:ℝ)^2*C^2 := mul_pos (sq_pos_of_pos (by exact_mod_cast hn)) (sq_pos_of_pos hC)
  have hback : Gᵀ *ᵥ (Jᵀ*ᵥv)=v := by
    rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul,hJG,Matrix.transpose_one,Matrix.one_mulVec]
  have hg := matrix_mulVec_square_bound Gᵀ (fun i k => hG k i) (Jᵀ*ᵥv)
  rw [hback] at hg
  have hj := matrix_mulVec_square_bound Jᵀ (fun i k => hJ k i) v
  rw [matrix_congruence_quadratic]
  constructor
  · have hgl := mul_le_mul_of_nonneg_left hg hlam
    have hal := mul_le_mul_of_nonneg_left (hlo (Jᵀ*ᵥv)) hN.le
    apply (mul_le_mul_right hN).mp
    have he : (lam/((n:ℝ)^2*C^2)*(∑ i, v i^2))*((n:ℝ)^2*C^2)=lam*(∑ i, v i^2) := by field_simp
    rw [he]
    nlinarith
  · exact (hhi _).trans (by nlinarith [mul_le_mul_of_nonneg_left hj hΛ])

lemma matrix_congruence_posDef {A J G : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hJG : J*G=1) : (J*A*Jᵀ).PosDef := by
  have hi : Function.Injective J.vecMul := by
    intro v z hvz
    have hh := congrArg (fun y => y ᵥ* G) hvz
    simpa only [Matrix.vecMul_vecMul,hJG,Matrix.vecMul_one] using hh
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.mul_mul_conjTranspose_same hi

lemma matrix_triple_entry_bound (P Q R : Matrix (Fin n) (Fin n) ℝ)
    {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hP : ∀ i k, |P i k| ≤ p) (hQ : ∀ i k, |Q i k| ≤ q) (hR : ∀ i k, |R i k| ≤ r)
    (i j : Fin n) : |(P*Q*R) i j| ≤ (n:ℝ)^2*p*q*r := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply,Finset.mul_sum]
  calc
    _ ≤ ∑ k, ∑ l, |P i k * (Q k l * R l j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _k : Fin n, ∑ _l : Fin n, p*(q*r) := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul,abs_mul]
      exact mul_le_mul (hP i k) (mul_le_mul (hQ k l) (hR l j) (abs_nonneg _) hq) (by positivity) hp
    _ = _ := by simp; ring

end GaussianTilt.MomentMapLinearDirichlet
