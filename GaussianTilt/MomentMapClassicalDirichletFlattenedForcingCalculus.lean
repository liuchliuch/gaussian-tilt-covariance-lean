import GaussianTilt.MomentMapClassicalDirichletCurvatureBounds
import GaussianTilt.MomentMapClassicalDirichletIntrinsicLipschitz
import GaussianTilt.MomentMapLinearDirichletFlatteningChainRule

/-! # Exact differentiation of the full flattened forcing, including curvature -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

lemma norm_clm_le_of_coordinate_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : CoordinateSpace n →L[ℝ] F) {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ i, ‖D (Pi.single i 1)‖ ≤ K) : ‖D‖ ≤ (n:ℝ)*K := by
  apply D.opNorm_le_bound (mul_nonneg (Nat.cast_nonneg _) hK)
  intro v
  have hv : (∑ i, v i • (Pi.single i 1 : CoordinateSpace n)) = v := by ext i; simp [Pi.single_apply]
  calc
    ‖D v‖ = ‖∑ i, v i • D (Pi.single i 1)‖ := by
      conv_lhs => rw [← hv]
      simp only [map_sum,map_smul]
    _ ≤ ∑ i, ‖v i • D (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (‖v‖*K) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm v i) (hD i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

lemma norm_bilinear_le_of_coordinate_bound
    (D : CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hD : ∀ i l, |D (Pi.single i 1) (Pi.single l 1)| ≤ K) :
    ‖D‖ ≤ (n:ℝ)^2*K := by
  have hh := norm_clm_le_of_coordinate_bound D (mul_nonneg (Nat.cast_nonneg _) hK)
    (fun i => norm_covector_le_of_coordinate_bound (D (Pi.single i 1)) hK (hD i))
  exact hh.trans_eq (by ring)

lemma abs_coordinateDerivative_le_norm_fderiv (f : CoordinateSpace n → ℝ) (x : CoordinateSpace n) (k : Fin n) :
    |coordinateDerivative k f x| ≤ ‖fderiv ℝ f x‖ := by
  simpa only [coordinateDerivative,Real.norm_eq_abs,Pi.norm_single,norm_one,mul_one] using
    (fderiv ℝ f x).le_opNorm (Pi.single k 1)

lemma coordinateDerivative_comp_norm_bound
    {f : CoordinateSpace n → ℝ} {X : CoordinateSpace n → CoordinateSpace n}
    {y : CoordinateSpace n} (hf : DifferentiableAt ℝ f (X y)) (hX : DifferentiableAt ℝ X y)
    {G C : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C)
    (hDf : ∀ k, |coordinateDerivative k f (X y)| ≤ G)
    (hDX : ‖fderiv ℝ X y‖ ≤ C) (k : Fin n) :
    |coordinateDerivative k (f ∘ X) y| ≤ (n:ℝ)*G*C := by
  apply (abs_coordinateDerivative_le_norm_fderiv _ _ _).trans
  rw [fderiv_comp _ hf hX]
  exact ((fderiv ℝ f (X y)).opNorm_comp_le _).trans
    (mul_le_mul (norm_fderiv_le_of_coordinate_bound hG hDf) hDX (norm_nonneg _) (by positivity))

lemma scaled_coordinateHessian_comp_bound
    {T : CoordinateSpace n → ℝ} {X : CoordinateSpace n → CoordinateSpace n}
    {y : CoordinateSpace n} (hT : ContDiffAt ℝ 2 T (X y)) (hX : ContDiffAt ℝ 2 X y)
    {r G Q C : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hG : 0 ≤ G) (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (hDT : ∀ k, |coordinateDerivative k T (X y)| ≤ G)
    (hHT : ∀ i k, r*|coordinateHessian T (X y) i k| ≤ Q)
    (hDX : ‖fderiv ℝ X y‖ ≤ C) (hDDX : ‖fderiv ℝ (fderiv ℝ X) y‖ ≤ C) (i k : Fin n) :
    r*|coordinateHessian (T ∘ X) y i k| ≤ (n:ℝ)^2*Q*C^2+(n:ℝ)*G*C := by
  have hD : ‖fderiv ℝ T (X y)‖ ≤ (n:ℝ)*G := norm_fderiv_le_of_coordinate_bound hG hDT
  have hH : ‖fderiv ℝ (fderiv ℝ T) (X y)‖ ≤ (n:ℝ)^2*(Q/r) := by
    apply norm_bilinear_le_of_coordinate_bound _ (div_nonneg hQ hr.le)
    intro a b
    rw [← coordinateHessian_eq_secondFDerivAt hT b a]
    apply (le_div_iff₀ hr).mpr
    simpa only [mul_comm] using hHT b a
  have hX1 (a : Fin n) : ‖fderiv ℝ X y (Pi.single a 1)‖ ≤ C := by
    have hh : ‖fderiv ℝ X y (Pi.single a 1)‖ ≤ ‖fderiv ℝ X y‖ := by
      simpa only [Pi.norm_single,norm_one,mul_one] using (fderiv ℝ X y).le_opNorm (Pi.single a 1)
    exact hh.trans hDX
  have hX2 : ‖fderiv ℝ (fderiv ℝ X) y (Pi.single k 1) (Pi.single i 1)‖ ≤ C := by
    have hh := (fderiv ℝ (fderiv ℝ X) y (Pi.single k 1)).le_opNorm (Pi.single i 1)
    have hh' := (fderiv ℝ (fderiv ℝ X) y).le_opNorm (Pi.single k 1)
    simp only [Pi.norm_single,norm_one,mul_one] at hh hh'
    exact hh.trans (hh'.trans hDDX)
  have hterm1 : |fderiv ℝ (fderiv ℝ T) (X y) (fderiv ℝ X y (Pi.single k 1))
      (fderiv ℝ X y (Pi.single i 1))| ≤ (n:ℝ)^2*(Q/r)*C*C := by
    have hh := (fderiv ℝ (fderiv ℝ T) (X y) (fderiv ℝ X y (Pi.single k 1))).le_opNorm
      (fderiv ℝ X y (Pi.single i 1))
    have hh' := (fderiv ℝ (fderiv ℝ T) (X y)).le_opNorm (fderiv ℝ X y (Pi.single k 1))
    apply (show |fderiv ℝ (fderiv ℝ T) (X y) (fderiv ℝ X y (Pi.single k 1))
      (fderiv ℝ X y (Pi.single i 1))| ≤ _ from hh).trans
    exact mul_le_mul (hh'.trans (mul_le_mul hH (hX1 k) (norm_nonneg _) (by positivity)))
      (hX1 i) (norm_nonneg _) (by positivity)
  have hterm2 : |fderiv ℝ T (X y) (fderiv ℝ (fderiv ℝ X) y (Pi.single k 1) (Pi.single i 1))| ≤ (n:ℝ)*G*C :=
    ((fderiv ℝ T (X y)).le_opNorm _).trans (mul_le_mul hD hX2 (norm_nonneg _) (by positivity))
  rw [coordinateHessian_eq_secondFDerivAt (hT.comp y hX) i k,secondFrechet_comp_at hT hX]
  have habs := abs_add_le (fderiv ℝ (fderiv ℝ T) (X y) (fderiv ℝ X y (Pi.single k 1))
    (fderiv ℝ X y (Pi.single i 1)))
    (fderiv ℝ T (X y) (fderiv ℝ (fderiv ℝ X) y (Pi.single k 1) (Pi.single i 1)))
  have hmul := mul_le_mul_of_nonneg_left (habs.trans (add_le_add hterm1 hterm2)) hr.le
  have he : r*((n:ℝ)^2*(Q/r)*C*C) = (n:ℝ)^2*Q*C^2 := by field_simp <;> ring
  have hlast := mul_le_mul_of_nonneg_right hr1 (show 0 ≤ (n:ℝ)*G*C by positivity)
  nlinarith

lemma scaled_coordinateDerivative_comp_bound
    {f : CoordinateSpace n → ℝ} {X : CoordinateSpace n → CoordinateSpace n}
    {y : CoordinateSpace n} (hf : DifferentiableAt ℝ f (X y)) (hX : DifferentiableAt ℝ X y)
    {r G C : ℝ} (hr : 0 < r) (hG : 0 ≤ G) (hC : 0 ≤ C)
    (hDf : ∀ k, r*|coordinateDerivative k f (X y)| ≤ G)
    (hDX : ‖fderiv ℝ X y‖ ≤ C) (k : Fin n) :
    r*|coordinateDerivative k (f ∘ X) y| ≤ (n:ℝ)*G*C := by
  have hh := coordinateDerivative_comp_norm_bound hf hX (div_nonneg hG hr.le) hC
    (fun a => (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hDf a)) hDX k
  apply (mul_le_mul_of_nonneg_left hh hr.le).trans_eq
  field_simp

/-- Literal forcing after rescaling the flattened coordinates by `s`.
The second summand is the real defining-function curvature drift. -/
def flattenedTangentForcing (s : ℝ) (g b T : CoordinateSpace n → ℝ)
    (X : CoordinateSpace n → CoordinateSpace n) (q : Fin n) : CoordinateSpace n → ℝ :=
  fun y => s^2*g (X y)+s*b (X y)*coordinateDerivative q (T ∘ X) y

lemma coordinateDerivative_flattenedTangentForcing
    (s : ℝ) {g b T : CoordinateSpace n → ℝ} {X : CoordinateSpace n → CoordinateSpace n}
    {y : CoordinateSpace n} (hg : DifferentiableAt ℝ g (X y)) (hb : DifferentiableAt ℝ b (X y))
    (hT : ContDiffAt ℝ 2 T (X y)) (hX : ContDiffAt ℝ 2 X y) (q k : Fin n) :
    coordinateDerivative k (flattenedTangentForcing s g b T X q) y =
      s^2*coordinateDerivative k (g ∘ X) y+
      s*coordinateDerivative k (b ∘ X) y*coordinateDerivative q (T ∘ X) y+
      s*b (X y)*coordinateHessian (T ∘ X) y q k := by
  have hXd := hX.differentiableAt (by norm_num)
  have hTc := hT.comp y hX
  have hDT := (contDiffAt_coordinateDerivative hTc (m:=1) (by norm_num) q).differentiableAt le_rfl
  have hd := ((hg.hasFDerivAt.comp y hXd.hasFDerivAt).const_mul (s^2)).add
    (((hb.hasFDerivAt.comp y hXd.hasFDerivAt).const_mul s).mul hDT.hasFDerivAt)
  change HasFDerivAt (flattenedTangentForcing s g b T X q) _ y at hd
  unfold coordinateDerivative
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [fderiv_comp _ hg hXd,fderiv_comp _ hb hXd]
  simp only [coordinateHessian,coordinateDerivative,Function.comp_apply]
  ring

/-- All terms in the true flattened forcing, including the differentiated
curvature drift, obey uniform bounds derived from the original coefficient,
forcing and tangential-field estimates. -/
theorem flattenedTangentForcing_bounds
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    {g b T : CoordinateSpace n → ℝ} {X : CoordinateSpace n → CoordinateSpace n}
    {y : CoordinateSpace n} (hg : DifferentiableAt ℝ g (X y)) (hb : DifferentiableAt ℝ b (X y))
    (hT : ContDiffAt ℝ 2 T (X y)) (hX : ContDiffAt ℝ 2 X y)
    {r M B G Q C : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hG : 0 ≤ G) (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (hg0 : |g (X y)| ≤ M) (hb0 : |b (X y)| ≤ B)
    (hg1 : ∀ k, r*|coordinateDerivative k g (X y)| ≤ M)
    (hb1 : ∀ k, r*|coordinateDerivative k b (X y)| ≤ B)
    (hDT : ∀ k, |coordinateDerivative k T (X y)| ≤ G)
    (hHT : ∀ i k, r*|coordinateHessian T (X y) i k| ≤ Q)
    (hDX : ‖fderiv ℝ X y‖ ≤ C) (hDDX : ‖fderiv ℝ (fderiv ℝ X) y‖ ≤ C) (q : Fin n) :
    |flattenedTangentForcing s g b T X q y| ≤ M+B*((n:ℝ)*G*C) ∧
      ∀ k, r*|coordinateDerivative k (flattenedTangentForcing s g b T X q) y| ≤
        (n:ℝ)*M*C+((n:ℝ)*B*C)*((n:ℝ)*G*C)+B*((n:ℝ)^2*Q*C^2+(n:ℝ)*G*C) := by
  have hs2 : s^2 ≤ 1 := by nlinarith
  have hX1 := hX.differentiableAt (by norm_num)
  have hTG := coordinateDerivative_comp_norm_bound (hT.differentiableAt (by norm_num)) hX1 hG hC hDT hDX q
  have hgC := scaled_coordinateDerivative_comp_bound hg hX1 hr hM hC hg1 hDX
  have hbC := scaled_coordinateDerivative_comp_bound hb hX1 hr hB hC hb1 hDX
  have hTH := scaled_coordinateHessian_comp_bound hT hX hr hr1 hG hQ hC hDT hHT hDX hDDX q
  constructor
  · unfold flattenedTangentForcing
    calc
      _ ≤ |s^2*g (X y)|+|s*b (X y)*coordinateDerivative q (T ∘ X) y| := abs_add_le _ _
      _ = s^2*|g (X y)|+s*|b (X y)| * |coordinateDerivative q (T ∘ X) y| := by
        simp only [abs_mul,abs_of_nonneg (sq_nonneg s),abs_of_nonneg hs]
      _ ≤ 1*M+1*B*((n:ℝ)*G*C) := by gcongr
      _ = _ := by ring
  · intro k
    rw [coordinateDerivative_flattenedTangentForcing s hg hb hT hX]
    have h1 : r*|s^2*coordinateDerivative k (g ∘ X) y| ≤ (n:ℝ)*M*C := by
      rw [abs_mul,abs_of_nonneg (sq_nonneg s)]
      have hh := mul_le_mul hs2 (hgC k) (mul_nonneg hr.le (abs_nonneg _)) (by norm_num : (0:ℝ) ≤ 1)
      nlinarith
    have h2 : r*|s*coordinateDerivative k (b ∘ X) y*coordinateDerivative q (T ∘ X) y| ≤
        ((n:ℝ)*B*C)*((n:ℝ)*G*C) := by
      rw [abs_mul,abs_mul,abs_of_nonneg hs]
      have hh := mul_le_mul (hbC k) hTG (abs_nonneg _) (by positivity : 0 ≤ (n:ℝ)*B*C)
      have hs' := mul_le_mul_of_nonneg_left hs1
        (mul_nonneg (mul_nonneg hr.le (abs_nonneg (coordinateDerivative k (b ∘ X) y)))
          (abs_nonneg (coordinateDerivative q (T ∘ X) y)))
      nlinarith
    have h3 : r*|s*b (X y)*coordinateHessian (T ∘ X) y q k| ≤ B*((n:ℝ)^2*Q*C^2+(n:ℝ)*G*C) := by
      rw [abs_mul,abs_mul,abs_of_nonneg hs]
      have hh := mul_le_mul hb0 (hTH k) (mul_nonneg hr.le (abs_nonneg _)) hB
      have hs' := mul_le_mul_of_nonneg_left hs1
        (mul_nonneg (mul_nonneg hr.le (abs_nonneg (b (X y))))
          (abs_nonneg (coordinateHessian (T ∘ X) y q k)))
      nlinarith
    have hh : r*|s^2*coordinateDerivative k (g ∘ X) y+
        s*coordinateDerivative k (b ∘ X) y*coordinateDerivative q (T ∘ X) y+
        s*b (X y)*coordinateHessian (T ∘ X) y q k| ≤
        r*(|s^2*coordinateDerivative k (g ∘ X) y|+
        |s*coordinateDerivative k (b ∘ X) y*coordinateDerivative q (T ∘ X) y|+
        |s*b (X y)*coordinateHessian (T ∘ X) y q k|) :=
      mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)) hr.le
    nlinarith

lemma contDiffAt_flattenedTangentForcing
    (s : ℝ) {g b T : CoordinateSpace n → ℝ} {X : CoordinateSpace n → CoordinateSpace n}
    {y : CoordinateSpace n} (hg : ContDiffAt ℝ ∞ g (X y)) (hb : ContDiffAt ℝ ∞ b (X y))
    (hT : ContDiffAt ℝ ∞ T (X y)) (hX : ContDiffAt ℝ ∞ X y) (q : Fin n) :
    ContDiffAt ℝ ∞ (flattenedTangentForcing s g b T X q) y := by
  have hv := hT.comp y hX
  have hd := contDiffAt_coordinateDerivative hv (m:=∞) (by simp) q
  exact ((contDiffAt_const.mul (hg.comp y hX)).add
    ((contDiffAt_const.mul (hb.comp y hX)).mul hd))

end GaussianTilt.MomentMapRegularity
