import GaussianTilt.MomentMapRegularityImprovementReferenceNormalization

/-! # Actual rescaling of a rough convex source by its smooth reference

The source remains only convex. The new near-quadratic value error is
proved from the actual comparison error, reference Taylor remainder and
exact Hessian normalization; no source Hessian is used.
-/
noncomputable section
open Set
open scoped Topology
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def improvementRescale (u : E n → ℝ) (p : E n) (L : E n →L[ℝ] E n)
    (ρ : ℝ) (x : E n) : ℝ := (u (ρ • L x)-u 0-inner ℝ p (ρ • L x))/ρ^2

@[simp] lemma improvementRescale_zero (u : E n → ℝ) (p : E n)
    (L : E n →L[ℝ] E n) (ρ : ℝ) : improvementRescale u p L ρ 0 = 0 := by
  simp [improvementRescale]

lemma improvementRescale_continuous {u : E n → ℝ} (hu : Continuous u) (p : E n)
    (L : E n →L[ℝ] E n) (ρ : ℝ) : Continuous (improvementRescale u p L ρ) := by
  unfold improvementRescale
  fun_prop

lemma improvementRescale_convex {u : E n → ℝ} (hu : ConvexOn ℝ univ u) (p : E n)
    (L : E n →L[ℝ] E n) (ρ : ℝ) : ConvexOn ℝ univ (improvementRescale u p L ρ) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  have hh := hu.2 (mem_univ (ρ • L x)) (mem_univ (ρ • L y)) ha hb hab
  have hpoint : ρ • L (a • x+b • y) = a • (ρ • L x)+b • (ρ • L y) := by
    simp only [map_add,map_smul]
    module
  simp only [improvementRescale,hpoint,smul_eq_mul,inner_add_right,inner_smul_right] at *
  have hconst : a*u 0+b*u 0=u 0 := by rw [← add_mul,hab,one_mul]
  have hnum : u (a • (ρ • L x)+b • (ρ • L y))-u 0-
      (a*inner ℝ p (ρ • L x)+b*inner ℝ p (ρ • L y)) ≤
      a*(u (ρ • L x)-u 0-inner ℝ p (ρ • L x))+
      b*(u (ρ • L y)-u 0-inner ℝ p (ρ • L y)) := by nlinarith
  have hd := div_le_div_of_nonneg_right hnum (sq_nonneg ρ)
  convert hd using 1 <;> simp only [inner_smul_right] <;> ring

/-- Exact one-step error for the rough rescaled source. -/
theorem improvementRescale_error {u v : E n → ℝ} {a : ℝ} {p : E n}
    {H L : E n →L[ℝ] E n} {ρ R S N ε C : ℝ}
    (hρ : 0 < ρ) (hR : 0 ≤ R) (hS : 0 ≤ S) (hN : 0 ≤ N) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hL : ‖L‖ ≤ N) (hregion : ρ*N*S ≤ R)
    (hquad : ∀ x : E n, inner ℝ (H (L x)) (L x) = ‖x‖^2)
    (hcompare : ∀ y : E n, ‖y‖ ≤ R → |u y-v y| ≤ ε)
    (hTaylor : ∀ y : E n, ‖y‖ ≤ R → |v y-quadraticJet a p 0 H y| ≤ C*‖y‖^3) :
    ∀ x : E n, ‖x‖ ≤ S →
      |improvementRescale u p L ρ x-‖x‖^2/2| ≤ 2*ε/ρ^2+C*ρ*N^3*S^3 := by
  have hTaylor0 := hTaylor 0 (by simpa using hR)
  have ha : v 0=a := by
    have hh : |v 0-a| ≤ 0 := by simpa [quadraticJet] using hTaylor0
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
  have hconstant : |a-u 0| ≤ ε := by simpa only [ha,abs_sub_comm] using hcompare 0 (by simpa using hR)
  intro x hx
  let y := ρ • L x
  have hyN : ‖y‖ ≤ ρ*N*S := by
    rw [show y=ρ • L x from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
    exact (mul_le_mul_of_nonneg_left ((L.le_opNorm x).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg x))) hρ.le).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hx (mul_nonneg hρ.le hN))
  have hy : ‖y‖ ≤ R := hyN.trans hregion
  have hq : inner ℝ (H y) y = ρ^2*‖x‖^2 := by
    simp only [y,map_smul,inner_smul_left,inner_smul_right,conj_trivial,hquad]
    ring
  have hnum : |u y-u 0-inner ℝ p y-ρ^2*‖x‖^2/2| ≤ 2*ε+C*(ρ*N*S)^3 := by
    have he : u y-u 0-inner ℝ p y-ρ^2*‖x‖^2/2 =
        (u y-v y)+(v y-quadraticJet a p 0 H y)+(a-u 0) := by
      simp only [quadraticJet,sub_zero,hq]
      ring
    rw [he]
    have ht := hTaylor y hy
    have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y) hyN 3) hC
    exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (by linarith [hcompare y hy,hconstant])
  have he : improvementRescale u p L ρ x-‖x‖^2/2 =
      (u y-u 0-inner ℝ p y-ρ^2*‖x‖^2/2)/ρ^2 := by
    dsimp [improvementRescale,y]
    field_simp
  rw [he,abs_div,abs_of_nonneg (sq_nonneg ρ)]
  have hh := div_le_div_of_nonneg_right hnum (sq_nonneg ρ)
  convert hh using 1 <;> field_simp <;> ring

end GaussianTilt.MomentMapRegularity
