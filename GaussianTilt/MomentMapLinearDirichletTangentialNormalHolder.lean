import GaussianTilt.MomentMapLinearDirichletTangentialNormalClosed
import GaussianTilt.MomentMapClassicalDirichletFullHessianHolder

/-! # Actual Hölder transfer through normal weak-flux recovery -/
noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma recoveredWeakHessian_tangent (q k i : Fin n) (hk : k≠q)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (G : CoordinateSpace n → CoordinateSpace n)
    (J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (f : CoordinateSpace n→ℝ) (x : CoordinateSpace n) :
    recoveredWeakHessian q A G J f x k i=J x k i := by simp only [recoveredWeakHessian,if_neg hk]

lemma recoveredWeakHessian_normal_off (q i : Fin n) (hi : i≠q)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (G : CoordinateSpace n → CoordinateSpace n)
    (J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (f : CoordinateSpace n→ℝ) (x : CoordinateSpace n)
    (ha : A x q q≠0) : recoveredWeakHessian q A G J f x q i=J x i q := by
  simp only [recoveredWeakHessian,recoveredNormalRow,normalFluxGradient,nonNormalHessian,ite_true,if_neg hi]
  field_simp
  ring

lemma recoveredWeakHessian_normal (q : Fin n)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (G : CoordinateSpace n → CoordinateSpace n)
    (J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (f : CoordinateSpace n→ℝ) (x : CoordinateSpace n) :
    recoveredWeakHessian q A G J f x q q=
      (-f x-nonNormalDivergence q A G (nonNormalHessian q J) x-
        coordinateDerivative q (fun y=>A y q q) x*G x q)/A x q q := by
  simp only [recoveredWeakHessian,recoveredNormalRow,normalFluxGradient,ite_true]

lemma nonNormalDivergence_abs_bound (q : Fin n)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {G : CoordinateSpace n → CoordinateSpace n}
    {J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {x : CoordinateSpace n} {B : ℝ} (hB : 0≤B)
    (hA : ∀ i k,|A x i k|≤B) (hD : ∀ i k l,|coordinateDerivative l (fun y=>A y i k) x|≤B)
    (hG : ∀ k,|G x k|≤B) (hJ : ∀ k i,|J x k i|≤B) :
    |nonNormalDivergence q A G (nonNormalHessian q J) x|≤
      ((Finset.univ.erase (q,q)).card:ℝ)*(2*B^2) := by
  unfold nonNormalDivergence
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _p∈Finset.univ.erase (q,q),2*B^2 := Finset.sum_le_sum (fun p _=>by
      have hH : |nonNormalHessian q J x p.2 p.1|≤B := by
        unfold nonNormalHessian
        split_ifs <;> exact hJ _ _
      exact (abs_add_le _ _).trans (by
        rw [abs_mul,abs_mul]
        nlinarith [mul_le_mul (hD p.1 p.2 p.1) (hG p.2) (abs_nonneg _) hB,
          mul_le_mul (hA p.1 p.2) hH (abs_nonneg _) hB]))
    _ = _ := by simp

lemma nonNormalDivergence_difference_bound (q : Fin n)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {G : CoordinateSpace n → CoordinateSpace n}
    {J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {x y : CoordinateSpace n} {B ε : ℝ}
    (hB : 0≤B) (_hε : 0≤ε)
    (hAx : ∀ i k,|A x i k|≤B) (_hDy : ∀ i k l,|coordinateDerivative l (fun z=>A z i k) y|≤B)
    (hDx : ∀ i k l,|coordinateDerivative l (fun z=>A z i k) x|≤B)
    (hGy : ∀ k,|G y k|≤B) (hJy : ∀ k i,|J y k i|≤B)
    (hA : ∀ i k,|A x i k-A y i k|≤ε)
    (hD : ∀ i k l,|coordinateDerivative l (fun z=>A z i k) x-coordinateDerivative l (fun z=>A z i k) y|≤ε)
    (hG : ∀ k,|G x k-G y k|≤ε) (hJ : ∀ k i,|J x k i-J y k i|≤ε) :
    |nonNormalDivergence q A G (nonNormalHessian q J) x-nonNormalDivergence q A G (nonNormalHessian q J) y|≤
      ((Finset.univ.erase (q,q)).card:ℝ)*(4*B*ε) := by
  unfold nonNormalDivergence
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _p∈Finset.univ.erase (q,q),4*B*ε := Finset.sum_le_sum (fun p _=>by
      have hH : |nonNormalHessian q J y p.2 p.1|≤B := by
        unfold nonNormalHessian
        split_ifs <;> exact hJy _ _
      have hHd : |nonNormalHessian q J x p.2 p.1-nonNormalHessian q J y p.2 p.1|≤ε := by
        unfold nonNormalHessian
        split_ifs <;> exact hJ _ _
      have h₁ := scalar_mul_difference_bound hB hB (hDx p.1 p.2 p.1) (hGy p.2) (hD p.1 p.2 p.1) (hG p.2)
      have h₂ := scalar_mul_difference_bound hB hB (hAx p.1 p.2) hH (hA p.1 p.2) hHd
      have he : (coordinateDerivative p.1 (fun z=>A z p.1 p.2) x*G x p.2+A x p.1 p.2*nonNormalHessian q J x p.2 p.1)-
          (coordinateDerivative p.1 (fun z=>A z p.1 p.2) y*G y p.2+A y p.1 p.2*nonNormalHessian q J y p.2 p.1)=
        (coordinateDerivative p.1 (fun z=>A z p.1 p.2) x*G x p.2-coordinateDerivative p.1 (fun z=>A z p.1 p.2) y*G y p.2)+
        (A x p.1 p.2*nonNormalHessian q J x p.2 p.1-A y p.1 p.2*nonNormalHessian q J y p.2 p.1) := by ring
      rw [he]
      exact (abs_add_le _ _).trans (by linarith))
    _ = _ := by simp

/-- A uniform quantitative normal recovery constant. -/
def normalRecoveryConstant (q : Fin n) (lam B : ℝ) : ℝ :=
  1+(1+(4*((Finset.univ.erase (q,q)).card:ℝ)+2)*B)/lam+
    (B+(2*((Finset.univ.erase (q,q)).card:ℝ)+1)*B^2)/lam^2

lemma normalRecoveryConstant_nonneg (q : Fin n) {lam B : ℝ} (hlam : 0<lam) (hB : 0≤B) :
    0≤normalRecoveryConstant q lam B := by unfold normalRecoveryConstant; positivity

/-- The recovered full Hessian has a quantitative pairwise modulus in all
of the actual coefficient, first-gradient and tangential-gradient data. -/
theorem recoveredWeakHessian_difference_bound (q : Fin n)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {G : CoordinateSpace n → CoordinateSpace n}
    {J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {f : CoordinateSpace n→ℝ}
    {x y : CoordinateSpace n} {lam B ε : ℝ} (hlam : 0<lam) (hB : 0≤B) (hε : 0≤ε)
    (hlx : lam≤A x q q) (hly : lam≤A y q q)
    (hAx : ∀ i k,|A x i k|≤B) (hAy : ∀ i k,|A y i k|≤B)
    (hDx : ∀ i k l,|coordinateDerivative l (fun z=>A z i k) x|≤B)
    (hDy : ∀ i k l,|coordinateDerivative l (fun z=>A z i k) y|≤B)
    (hGy : ∀ k,|G y k|≤B) (hJy : ∀ k i,|J y k i|≤B) (hfy : |f y|≤B)
    (hA : ∀ i k,|A x i k-A y i k|≤ε)
    (hD : ∀ i k l,|coordinateDerivative l (fun z=>A z i k) x-coordinateDerivative l (fun z=>A z i k) y|≤ε)
    (hG : ∀ k,|G x k-G y k|≤ε) (hJ : ∀ k i,|J x k i-J y k i|≤ε) (hf : |f x-f y|≤ε) :
    ∀ k i,|recoveredWeakHessian q A G J f x k i-recoveredWeakHessian q A G J f y k i|≤
      normalRecoveryConstant q lam B*ε := by
  let m : ℝ := ((Finset.univ.erase (q,q)).card:ℝ)
  let P := 1+(4*m+2)*B
  let M := B+(2*m+1)*B^2
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hP : 0≤P := by dsimp [P]; positivity
  have hM : 0≤M := by dsimp [M]; positivity
  have hC : 1≤normalRecoveryConstant q lam B := by
    change 1≤1+P/lam+M/lam^2
    have hp := div_nonneg hP hlam.le
    have hmp := div_nonneg hM (sq_nonneg lam)
    linarith
  have hsimple : ε≤normalRecoveryConstant q lam B*ε := by nlinarith
  intro k i
  by_cases hk : k=q
  · subst k
    by_cases hi : i=q
    · subst i
      let N := fun z=> -f z-nonNormalDivergence q A G (nonNormalHessian q J) z-
        coordinateDerivative q (fun w=>A w q q) z*G z q
      have hNy : |N y|≤M := by
        have hn := nonNormalDivergence_abs_bound q hB hAy hDy hGy hJy
        have hd : |coordinateDerivative q (fun z=>A z q q) y*G y q|≤B^2 := by
          rw [abs_mul]
          simpa only [pow_two] using mul_le_mul (hDy q q q) (hGy q) (abs_nonneg _) hB
        have ha : |N y|≤|(-f y)|+|nonNormalDivergence q A G (nonNormalHessian q J) y|+
            |coordinateDerivative q (fun z=>A z q q) y*G y q| :=
          (abs_sub _ _).trans (add_le_add_right (abs_sub (-f y)
            (nonNormalDivergence q A G (nonNormalHessian q J) y)) _)
        rw [abs_neg] at ha
        change |N y|≤_
        dsimp only [M]
        linarith
      have hNd : |N x-N y|≤P*ε := by
        have hn := nonNormalDivergence_difference_bound q hB hε hAx hDy hDx hGy hJy hA hD hG hJ
        have hd := scalar_mul_difference_bound hB hB (hDx q q q) (hGy q) (hD q q q) (hG q)
        have he : N x-N y= -(f x-f y)-
          (nonNormalDivergence q A G (nonNormalHessian q J) x-nonNormalDivergence q A G (nonNormalHessian q J) y)-
          (coordinateDerivative q (fun z=>A z q q) x*G x q-coordinateDerivative q (fun z=>A z q q) y*G y q) := by
          dsimp [N]
          ring
        rw [he]
        have ha : |-(f x-f y)-(nonNormalDivergence q A G (nonNormalHessian q J) x-
            nonNormalDivergence q A G (nonNormalHessian q J) y)-
            (coordinateDerivative q (fun z=>A z q q) x*G x q-coordinateDerivative q (fun z=>A z q q) y*G y q)|≤
          |-(f x-f y)|+|nonNormalDivergence q A G (nonNormalHessian q J) x-
            nonNormalDivergence q A G (nonNormalHessian q J) y|+
          |coordinateDerivative q (fun z=>A z q q) x*G x q-coordinateDerivative q (fun z=>A z q q) y*G y q| :=
          (abs_sub _ _).trans (add_le_add_right (abs_sub (-(f x-f y))
            (nonNormalDivergence q A G (nonNormalHessian q J) x-nonNormalDivergence q A G (nonNormalHessian q J) y)) _)
        rw [abs_neg] at ha
        dsimp only [P]
        nlinarith
      have hh := quotient_difference_bound hlam hlx hly hε (mul_nonneg hP hε) hM hNd hNy (hA q q)
      rw [recoveredWeakHessian_normal,recoveredWeakHessian_normal]
      change |N x/A x q q-N y/A y q q|≤_
      apply hh.trans
      change (P*ε)/lam+M*ε/lam^2≤(1+P/lam+M/lam^2)*ε
      have he : (1+P/lam+M/lam^2)*ε=(P*ε)/lam+M*ε/lam^2+ε := by ring
      rw [he]
      exact le_add_of_nonneg_right hε
    · rw [recoveredWeakHessian_normal_off q i hi A G J f x (ne_of_gt (hlam.trans_le hlx)),
        recoveredWeakHessian_normal_off q i hi A G J f y (ne_of_gt (hlam.trans_le hly))]
      exact (hJ i q).trans hsimple
  · rw [recoveredWeakHessian_tangent q k i hk,recoveredWeakHessian_tangent q k i hk]
    exact (hJ k i).trans hsimple

/-- The recovered normal entry preserves the input Hölder exponent.
This is used in both genuine weak-boundary regularity passes. -/
theorem recoveredWeakHessian_holder (q : Fin n) {S : Set (CoordinateSpace n)}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {G : CoordinateSpace n → CoordinateSpace n}
    {J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {f : CoordinateSpace n→ℝ}
    {lam B L α : ℝ} (hlam : 0<lam) (hB : 0≤B) (hL : 0≤L)
    (hell : ∀ x∈S,lam≤A x q q)
    (hAb : ∀ x∈S,∀ i k,|A x i k|≤B)
    (hDb : ∀ x∈S,∀ i k l,|coordinateDerivative l (fun z=>A z i k) x|≤B)
    (hGb : ∀ x∈S,∀ k,|G x k|≤B) (hJb : ∀ x∈S,∀ k i,|J x k i|≤B) (hfb : ∀ x∈S,|f x|≤B)
    (hA : ∀ x∈S,∀ y∈S,∀ i k,|A x i k-A y i k|≤L*dist x y^α)
    (hD : ∀ x∈S,∀ y∈S,∀ i k l,
      |coordinateDerivative l (fun z=>A z i k) x-coordinateDerivative l (fun z=>A z i k) y|≤L*dist x y^α)
    (hG : ∀ x∈S,∀ y∈S,∀ k,|G x k-G y k|≤L*dist x y^α)
    (hJ : ∀ x∈S,∀ y∈S,∀ k i,|J x k i-J y k i|≤L*dist x y^α)
    (hf : ∀ x∈S,∀ y∈S,|f x-f y|≤L*dist x y^α) :
    ∀ x∈S,∀ y∈S,∀ k i,
      |recoveredWeakHessian q A G J f x k i-recoveredWeakHessian q A G J f y k i|≤
        (normalRecoveryConstant q lam B*L)*dist x y^α := by
  intro x hx y hy k i
  have hh := recoveredWeakHessian_difference_bound q hlam hB
    (mul_nonneg hL (Real.rpow_nonneg (dist_nonneg) _)) (hell x hx) (hell y hy)
    (hAb x hx) (hAb y hy) (hDb x hx) (hDb y hy) (hGb y hy) (hJb y hy) (hfb y hy)
    (hA x hx y hy) (hD x hx y hy) (hG x hx y hy) (hJ x hx y hy) (hf x hx y hy) k i
  exact hh.trans_eq (by ring)

end GaussianTilt.MomentMapLinearDirichlet
