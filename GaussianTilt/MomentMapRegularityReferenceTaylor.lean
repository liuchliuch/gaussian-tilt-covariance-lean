import GaussianTilt.MomentMapClassicalDirichletBoundaryJets
import GaussianTilt.MomentMapSchauderInterpolation
import GaussianTilt.MomentMapCampanatoDifferentiation

/-! # Genuine local Taylor control for constant-density references

Only smoothness on the actual segment is used. These estimates therefore
apply to classical Dirichlet solutions without a globally smooth extension.
-/
noncomputable section
open Set Filter
open scoped Topology ContDiff Gradient
namespace GaussianTilt.MomentMapRegularity
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxSize 1000

section LocalCalculus
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma second_deriv_comp_curve_at {u : X → ℝ} {γ : ℝ → X} {s : ℝ}
    (hu : ContDiffAt ℝ 2 u (γ s)) (hγ : ContDiffAt ℝ 2 γ s) :
    deriv (deriv (fun t => u (γ t))) s =
      fderiv ℝ (fderiv ℝ u) (γ s) (deriv γ s) (deriv γ s) +
        fderiv ℝ u (γ s) (deriv (deriv γ) s) := by
  have hγd : DifferentiableAt ℝ γ s := hγ.differentiableAt (by norm_num)
  have hDγ : DifferentiableAt ℝ (deriv γ) s := by
    change DifferentiableAt ℝ (fun t => fderiv ℝ γ t 1) s
    exact ((hγ.fderiv_right (m:=1) (by norm_num)).differentiableAt le_rfl).clm_apply
      (differentiableAt_const 1)
  have hDu := ((hu.fderiv_right (m:=1) (by norm_num)).differentiableAt le_rfl).hasFDerivAt
  have hcompose := hDu.comp_hasDerivAt s hγd.hasDerivAt
  have hproduct := hcompose.clm_apply hDγ.hasDerivAt
  have heq : deriv (fun t => u (γ t)) =ᶠ[𝓝 s] (fun t => fderiv ℝ u (γ t) (deriv γ t)) := by
    filter_upwards [hγ.eventually (by norm_num),
      hγd.continuousAt.eventually (hu.eventually (by norm_num))] with t hgt hut
    exact ((hut.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (hgt.differentiableAt (by norm_num)).hasDerivAt).deriv
  exact (hproduct.congr_of_eventuallyEq heq).deriv

lemma second_deriv_affine_line_local {u : X → ℝ} {x v : X} {t : ℝ}
    (hu : ContDiffAt ℝ 2 u (x+t • v)) :
    deriv (deriv (fun s : ℝ => u (x+s • v))) t =
      fderiv ℝ (fderiv ℝ u) (x+t • v) v v := by
  have hl (s : ℝ) : HasDerivAt (fun s : ℝ => x+s • v) v s := by
    simpa using (hasDerivAt_const s x).fun_add ((hasDerivAt_id s).smul_const v)
  have he : deriv (fun s : ℝ => x+s • v) = fun _ => v := funext (fun s => (hl s).deriv)
  have hg : ContDiffAt ℝ 2 (fun s : ℝ => x+s • v) t := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hh := second_deriv_comp_curve_at hu hg
  simpa only [he,deriv_const,map_zero,add_zero] using hh

lemma hessian_lipschitz_of_thirdFrechet_bound {u : X → ℝ} {S : Set X}
    (hS : Convex ℝ S) (hu : ∀ x ∈ S, ContDiffAt ℝ 3 u x) {C : ℝ}
    (hC : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ C)
    {x y : X} (hx : x ∈ S) (hy : y ∈ S) :
    ‖fderiv ℝ (fderiv ℝ u) y - fderiv ℝ (fderiv ℝ u) x‖ ≤ C*‖y-x‖ := by
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (f:=fderiv ℝ (fderiv ℝ u)) _ hC hS hx hy
  intro z hz
  exact (((hu z hz).fderiv_right (m:=2) (by norm_num)).fderiv_right
    (m:=1) (by norm_num)).differentiableAt le_rfl

end LocalCalculus

lemma exists_second_order_taylor_point_local {f : ℝ → ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f t) :
    ∃ t ∈ Ioo (0 : ℝ) 1, f 1-f 0-deriv f 0 = deriv (deriv f) t/2 := by
  obtain ⟨t,ht,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=1)
    (show (0 : ℝ)<1 by norm_num) (fun t ht => (hf t ht).contDiffWithinAt)
  have hd0 : derivWithin f (Icc (0 : ℝ) 1) 0 = deriv f 0 :=
    ((hf 0 (by simp)).differentiableAt (by norm_num)).derivWithin
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ)<1) 0 (by simp))
  refine ⟨t,ht,?_⟩
  simp only [taylorWithinEval_succ,taylor_within_zero_eval,iteratedDerivWithin_one,hd0,
    Nat.cast_one,Nat.factorial_zero,Nat.cast_zero,Nat.cast_succ,one_mul,zero_add,
    one_add_one_eq_two,inv_one,pow_one,smul_eq_mul,iteratedDeriv_succ,
    iteratedDeriv_zero,Nat.factorial_succ] at he
  norm_num only [Nat.factorial,Nat.reduceMul,Nat.cast_ofNat,sub_zero,one_pow,mul_one] at he
  have hi : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2 : ℕ) = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]
  rw [hi] at he
  convert he using 1 <;> ring


section Remainder
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Cubic Taylor remainder from a true local third-derivative bound. -/
theorem local_taylor_quadratic_remainder_of_third_bound {u : X → ℝ} {S : Set X}
    (hS : Convex ℝ S) (hu : ∀ x ∈ S, ContDiffAt ℝ 3 u x) {C : ℝ} (hC : 0 ≤ C)
    (hthird : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ C)
    {x v : X} (hx : x ∈ S) (hxv : x+v ∈ S) :
    |u (x+v)-u x-fderiv ℝ u x v-(1/2 : ℝ)*fderiv ℝ (fderiv ℝ u) x v v| ≤
      (C/2)*‖v‖^3 := by
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x+t • v ∈ S := by
    have hh := hS hx hxv (show 0 ≤ 1-t by linarith [ht.2]) ht.1 (by ring : (1-t)+t=1)
    convert hh using 1 <;> module
  have hline : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 (fun t => u (x+t • v)) t := by
    intro t ht
    exact ((hu _ (hseg t ht)).of_le (by norm_num)).comp t
      (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  obtain ⟨t,ht,he⟩ := exists_second_order_taylor_point_local hline
  have hl : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) x).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hd : HasFDerivAt u (fderiv ℝ u x) (x+(0:ℝ) • v) := by
    simpa using ((hu x hx).differentiableAt (by norm_num)).hasFDerivAt
  have hderiv : deriv (fun t : ℝ => u (x+t • v)) 0 = fderiv ℝ u x v := (hd.comp_hasDerivAt 0 hl).deriv
  rw [hderiv,second_deriv_affine_line_local
    ((hu _ (hseg t (Ioo_subset_Icc_self ht))).of_le (by norm_num))] at he
  simp only [one_smul,zero_smul,add_zero] at he
  let H := fderiv ℝ (fderiv ℝ u) (x+t • v)-fderiv ℝ (fderiv ℝ u) x
  have hH : ‖H‖ ≤ C*‖v‖ := by
    have hh := hessian_lipschitz_of_thirdFrechet_bound hS hu hthird hx (hseg t (Ioo_subset_Icc_self ht))
    simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht.1] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg v) ht.2.le) hC)
  have hHv : |H v v| ≤ C*‖v‖^3 := by
    have h1 := (H v).le_opNorm v
    have h2 := H.le_opNorm v
    rw [Real.norm_eq_abs] at h1
    have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg v)
    have h4 := mul_le_mul_of_nonneg_right hH (sq_nonneg ‖v‖)
    nlinarith
  have herr : u (x+v)-u x-fderiv ℝ u x v-(1/2 : ℝ)*fderiv ℝ (fderiv ℝ u) x v v = (1/2 : ℝ)*H v v := by
    dsimp [H]
    linarith
  rw [herr,abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
  nlinarith

end Remainder
end GaussianTilt.MomentMapRegularity
