import GaussianTilt.MomentMapClassicalDirichletNormalAlgebra
import GaussianTilt.MomentMapHolderDeterminant

/-!
# Genuine quantitative continuity of normal Hessian recovery

Determinant continuity is obtained from its actual smooth polynomial on a
compact matrix ball. Inverse and Schur quadratic differences are explicit
finite algebraic identities, rather than assumed Hölder estimates.
-/
noncomputable section
open Matrix Set
open scoped Topology BigOperators ContDiff NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma exists_determinant_lipschitz_on_entry_bound {M : ℝ} (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ A B : Matrix ι ι ℝ,
      (∀ i j, |A i j| ≤ M) → (∀ i j, |B i j| ≤ M) →
      ∀ ε : ℝ, 0 ≤ ε → (∀ i j, |A i j-B i j| ≤ ε) → |A.det-B.det| ≤ L*ε := by
  have hd : ContDiff ℝ ∞ (Matrix.det : Matrix ι ι ℝ → ℝ) := (determinantMultilinear (ι := ι)).contDiff
  have hdc := hd.continuous_fderiv (by simp)
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Matrix ι ι ℝ) M).exists_bound_of_continuousOn hdc.continuousOn
  let L : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  have hLip : LipschitzOnWith L Matrix.det (Metric.closedBall (0 : Matrix ι ι ℝ) M) := by
    apply (convex_closedBall (0 : Matrix ι ι ℝ) M).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hd.differentiable (by simp) x)
    intro x hx
    exact (hC x hx).trans (le_max_left _ _)
  refine ⟨L,L.coe_nonneg,?_⟩
  intro A B hA hB ε hε hdiff
  have hAn : A ∈ Metric.closedBall (0 : Matrix ι ι ℝ) M := by
    rw [Metric.mem_closedBall,dist_zero_right,Matrix.norm_le_iff hM]
    exact hA
  have hBn : B ∈ Metric.closedBall (0 : Matrix ι ι ℝ) M := by
    rw [Metric.mem_closedBall,dist_zero_right,Matrix.norm_le_iff hM]
    exact hB
  have hdiffn : dist A B ≤ ε := by
    rw [dist_eq_norm,Matrix.norm_le_iff hε]
    exact hdiff
  have hh := hLip.dist_le_mul A hAn B hBn
  exact hh.trans (mul_le_mul_of_nonneg_left hdiffn L.coe_nonneg)

lemma triple_matrix_entry_bound_card {A B C : Matrix ι ι ℝ} {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b) (hC : ∀ i j, |C i j| ≤ c)
    (i j : ι) : |(A*B*C) i j| ≤ (Fintype.card ι:ℝ)^2*a*b*c := by
  simp only [Matrix.mul_apply,Finset.sum_mul]
  calc
    _ ≤ ∑ l, ∑ m, |A i m*B m l*C l j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun l _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _l : ι, ∑ _m : ι, (a*b*c) := by
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro m _
      rw [abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (hA i m) (hB m l) (abs_nonneg _) ha) (hC l j)
        (abs_nonneg _) (mul_nonneg ha hb)
    _ = _ := by simp; ring

lemma inverse_entry_difference_bound {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {I ε : ℝ} (hI : 0 ≤ I) (hε : 0 ≤ ε)
    (hAi : ∀ i j, |A⁻¹ i j| ≤ I) (hBi : ∀ i j, |B⁻¹ i j| ≤ I)
    (hAB : ∀ i j, |A i j-B i j| ≤ ε) (i j : ι) :
    |A⁻¹ i j-B⁻¹ i j| ≤ (Fintype.card ι:ℝ)^2*I*ε*I := by
  have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hBu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hB.det_pos.ne')
  rw [← Matrix.sub_apply,Matrix.inv_sub_inv ⟨fun _ => hBu,fun _ => hAu⟩]
  exact triple_matrix_entry_bound_card hI hε hAi
    (fun i j => by simpa only [Matrix.sub_apply,abs_sub_comm] using hAB i j) hBi i j

lemma schur_quadratic_difference_bound {A B : Matrix ι ι ℝ} {b c : ι → ℝ}
    {I K D ε : ℝ} (hI : 0 ≤ I) (hK : 0 ≤ K) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hA : ∀ i j, |A i j| ≤ I) (hB : ∀ i j, |B i j| ≤ I)
    (hb : ∀ i, |b i| ≤ K) (hc : ∀ i, |c i| ≤ K)
    (hAB : ∀ i j, |A i j-B i j| ≤ D) (hbc : ∀ i, |b i-c i| ≤ ε) :
    |b ⬝ᵥ (A *ᵥ b)-c ⬝ᵥ (B *ᵥ c)| ≤ (Fintype.card ι:ℝ)^2*(2*I*K*ε+K^2*D) := by
  have ht (i j : ι) : |b i*(A i j*b j)-c i*(B i j*c j)| ≤ 2*I*K*ε+K^2*D := by
    have he : b i*(A i j*b j)-c i*(B i j*c j) =
        (b i-c i)*A i j*b j+c i*(A i j-B i j)*b j+c i*B i j*(b j-c j) := by ring
    have h1 : |(b i-c i)*A i j*b j| ≤ ε*I*K := by
      rw [abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (hbc i) (hA i j) (abs_nonneg _) hε) (hb j)
        (abs_nonneg _) (mul_nonneg hε hI)
    have h2 : |c i*(A i j-B i j)*b j| ≤ K*D*K := by
      rw [abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (hc i) (hAB i j) (abs_nonneg _) hK) (hb j)
        (abs_nonneg _) (mul_nonneg hK hD)
    have h3 : |c i*B i j*(b j-c j)| ≤ K*I*ε := by
      rw [abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (hc i) (hB i j) (abs_nonneg _) hK) (hbc j)
        (abs_nonneg _) (mul_nonneg hK hI)
    rw [he]
    have hh1 := abs_add_le ((b i-c i)*A i j*b j) (c i*(A i j-B i j)*b j)
    have hh2 := abs_add_le ((b i-c i)*A i j*b j+c i*(A i j-B i j)*b j) (c i*B i j*(b j-c j))
    nlinarith
  have he : b ⬝ᵥ (A *ᵥ b)-c ⬝ᵥ (B *ᵥ c) =
      ∑ i, ∑ j, (b i*(A i j*b j)-c i*(B i j*c j)) := by
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i, ∑ j, |b i*(A i j*b j)-c i*(B i j*c j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : ι, ∑ _j : ι, (2*I*K*ε+K^2*D) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ht i j))
    _ = _ := by simp; ring

lemma quotient_difference_bound {a b f g δ D ε F : ℝ}
    (hδ : 0 < δ) (ha : δ ≤ a) (hb : δ ≤ b) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hF : 0 ≤ F)
    (hfg : |f-g| ≤ ε) (hg : |g| ≤ F) (hab : |a-b| ≤ D) :
    |f/a-g/b| ≤ ε/δ+F*D/δ^2 := by
  have hap : 0 < a := hδ.trans_le ha
  have hbp : 0 < b := hδ.trans_le hb
  have he : f/a-g/b = (f-g)/a+g*(b-a)/(a*b) := by field_simp; ring
  have h1 : |(f-g)/a| ≤ ε/δ := by
    rw [abs_div,abs_of_pos hap]
    exact (div_le_div_of_nonneg_right hfg hap.le).trans (div_le_div_of_nonneg_left hε hδ ha)
  have h2 : |g*(b-a)/(a*b)| ≤ F*D/δ^2 := by
    rw [abs_div,abs_mul,abs_of_pos (mul_pos hap hbp),abs_sub_comm b a]
    have hnum := mul_le_mul hg hab (abs_nonneg _) hF
    have hden : δ^2 ≤ a*b := by simpa only [pow_two] using mul_le_mul ha hb hδ.le hap.le
    exact (div_le_div_of_nonneg_right hnum (mul_pos hap hbp).le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hF hD) (sq_pos_of_pos hδ) hden)
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- The actual scalar normal entry is Lipschitz in the tangent block,
adapted mixed row and determinant, uniformly under the derived bounds. -/
theorem exists_normalBlockMatrix_normal_lipschitz {δ I K M F : ℝ}
    (hδ : 0 < δ) (hI : 0 ≤ I) (hK : 0 ≤ K) (hM : 0 ≤ M) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A B : Matrix ι ι ℝ) (b c : ι → ℝ) (u v ε : ℝ),
      A.PosDef → B.PosDef → δ ≤ A.det → δ ≤ B.det →
      (∀ i j, |A i j| ≤ M) → (∀ i j, |B i j| ≤ M) →
      (∀ i j, |A⁻¹ i j| ≤ I) → (∀ i j, |B⁻¹ i j| ≤ I) →
      (∀ i, |b i| ≤ K) → (∀ i, |c i| ≤ K) →
      |(normalBlockMatrix B c v).det| ≤ F → 0 ≤ ε →
      (∀ i j, |A i j-B i j| ≤ ε) → (∀ i, |b i-c i| ≤ ε) →
      |(normalBlockMatrix A b u).det-(normalBlockMatrix B c v).det| ≤ ε → |u-v| ≤ C*ε := by
  obtain ⟨L,hL,hdet⟩ := exists_determinant_lipschitz_on_entry_bound (ι := ι) hM
  let C := 1/δ+F*L/δ^2+(Fintype.card ι:ℝ)^2*(2*I*K+K^2*(Fintype.card ι:ℝ)^2*I*I)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro A B b c u v ε hA hB hδA hδB hAb hBb hAi hBi hb hc hFv hε hAB hbc hfull
  have hAdet := hdet A B hAb hBb ε hε hAB
  have hInv := inverse_entry_difference_bound hA hB hI hε hAi hBi hAB
  have hquad := schur_quadratic_difference_bound hI hK
    (show 0 ≤ (Fintype.card ι:ℝ)^2*I*ε*I by positivity) hε hAi hBi hb hc hInv hbc
  have hratio := quotient_difference_bound hδ hδA hδB (mul_nonneg hL hε) hε hF hfull hFv hAdet
  rw [normalBlockMatrix_normal_entry hA.det_pos.ne' b u,normalBlockMatrix_normal_entry hB.det_pos.ne' c v]
  calc
    _ = |((normalBlockMatrix A b u).det/A.det-(normalBlockMatrix B c v).det/B.det)+
        (b ⬝ᵥ (A⁻¹ *ᵥ b)-c ⬝ᵥ (B⁻¹ *ᵥ c))| := by congr 1; ring
    _ ≤ |(normalBlockMatrix A b u).det/A.det-(normalBlockMatrix B c v).det/B.det|+
        |b ⬝ᵥ (A⁻¹ *ᵥ b)-c ⬝ᵥ (B⁻¹ *ᵥ c)| := abs_add_le _ _
    _ ≤ ε/δ+F*(L*ε)/δ^2+(Fintype.card ι:ℝ)^2*(2*I*K*ε+K^2*((Fintype.card ι:ℝ)^2*I*ε*I)) :=
      add_le_add hratio hquad
    _ = C*ε := by dsimp [C]; ring

/-- Genuine Hölder normal-normal recovery from the actual tangent block,
adapted mixed row and determinant. The inverse and determinant moduli are
proved internally from the uniform bounds. -/
theorem normalBlockMatrix_normal_holder
    {X : Type*} [PseudoMetricSpace X] {S : Set X}
    {A : X → Matrix ι ι ℝ} {b : X → ι → ℝ} {c : X → ℝ}
    {δ I K M F L α : ℝ}
    (hδ : 0 < δ) (hI : 0 ≤ I) (hK : 0 ≤ K) (hM : 0 ≤ M) (hF : 0 ≤ F) (hL : 0 ≤ L)
    (hp : ∀ x ∈ S, (A x).PosDef) (hd : ∀ x ∈ S, δ ≤ (A x).det)
    (hA : ∀ x ∈ S, ∀ i j, |A x i j| ≤ M) (hInv : ∀ x ∈ S, ∀ i j, |(A x)⁻¹ i j| ≤ I)
    (hb : ∀ x ∈ S, ∀ i, |b x i| ≤ K)
    (hdet : ∀ x ∈ S, |(normalBlockMatrix (A x) (b x) (c x)).det| ≤ F)
    (hAH : ∀ x ∈ S, ∀ y ∈ S, ∀ i j, |A x i j-A y i j| ≤ L*dist x y^α)
    (hbH : ∀ x ∈ S, ∀ y ∈ S, ∀ i, |b x i-b y i| ≤ L*dist x y^α)
    (hfH : ∀ x ∈ S, ∀ y ∈ S,
      |(normalBlockMatrix (A x) (b x) (c x)).det-(normalBlockMatrix (A y) (b y) (c y)).det| ≤ L*dist x y^α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ y ∈ S, |c x-c y| ≤ C*dist x y^α := by
  obtain ⟨C,hC,hbound⟩ := exists_normalBlockMatrix_normal_lipschitz (ι := ι) hδ hI hK hM hF
  refine ⟨C*L,mul_nonneg hC hL,?_⟩
  intro x hx y hy
  have hh := hbound (A x) (A y) (b x) (b y) (c x) (c y) (L*dist x y^α)
    (hp x hx) (hp y hy) (hd x hx) (hd y hy) (hA x hx) (hA y hy) (hInv x hx) (hInv y hy)
    (hb x hx) (hb y hy) (hdet y hy) (mul_nonneg hL (Real.rpow_nonneg dist_nonneg _))
    (hAH x hx y hy) (hbH x hx y hy) (hfH x hx y hy)
  simpa only [mul_assoc] using hh

end GaussianTilt.MomentMapRegularity
