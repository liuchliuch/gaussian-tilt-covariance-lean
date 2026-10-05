import GaussianTilt.MomentMapClassicalDirichletGlobalHessian
import GaussianTilt.MomentMapRegularityVariableDensityCalabiBounds
import GaussianTilt.LetwinMomentJacobianInjective

/-!
# Uniform ellipticity derived from the actual global Hessian estimate

The determinant lower bound controls the true adjugate inverse. A positive
quadratic square gives the inverse lower bound from the Hessian upper bound.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma inverse_entry_bound_of_det_lower {H : Matrix (Fin n) (Fin n) ℝ} {c K : ℝ}
    (hc : 0 < c) (hdet : c ≤ H.det) (hK : ∀ i j, |H i j| ≤ K) (i j : Fin n) :
    |H⁻¹ i j| ≤ ((n.factorial:ℝ)*(max K 1)^n)/c := by
  have hd := hc.trans_le hdet
  rw [Matrix.inv_def,Matrix.smul_apply,smul_eq_mul,Ring.inverse_eq_inv',abs_mul,abs_inv,abs_of_pos hd]
  rw [mul_comm,← div_eq_mul_inv]
  exact (div_le_div_of_nonneg_right (adjugate_entry_bound_of_entry_bound hK i j) hd.le).trans
    (div_le_div_of_nonneg_left (by positivity) hc hdet)

/-- A positive square proves the inverse quadratic lower bound directly;
no eigenbasis or separate inverse-ellipticity hypothesis is used. -/
lemma inverse_quadratic_lower_of_quadratic_upper {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) {U : ℝ} (hU : 0 < U)
    (hupper : ∀ v, v ⬝ᵥ (H *ᵥ v) ≤ U*(v ⬝ᵥ v)) (v : CoordinateSpace n) :
    U⁻¹*(v ⬝ᵥ v) ≤ v ⬝ᵥ (H⁻¹ *ᵥ v) := by
  have hs : H.IsSymm := by
    simpa only [Matrix.IsHermitian,Matrix.IsSymm,Matrix.conjTranspose_eq_transpose_of_trivial] using hH.isHermitian
  have hcancel : H⁻¹ *ᵥ (H *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),Matrix.one_mulVec]
  have hcancel' : H *ᵥ (H⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),Matrix.one_mulVec]
  have hcross : (H *ᵥ v) ⬝ᵥ (H⁻¹ *ᵥ v) = v ⬝ᵥ v := by
    rw [← symmetric_dot_mulVec H hs,hcancel']
  have hsq := hH.inv.posSemidef.2 (v-U⁻¹ • (H *ᵥ v))
  simp only [star_trivial,Matrix.mulVec_sub,Matrix.mulVec_smul,sub_dotProduct,
    dotProduct_sub,smul_dotProduct,dotProduct_smul,smul_eq_mul,hcancel,hcross] at hsq
  rw [dotProduct_comm (H *ᵥ v) v] at hsq
  have hb := mul_le_mul_of_nonneg_left (hupper v) (sq_nonneg U⁻¹)
  have hid : U⁻¹^2*U = U⁻¹ := by field_simp
  nlinarith [congrArg (fun a => a*(v ⬝ᵥ v)) hid]

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- The actual inverse-Hessian coefficient is uniformly elliptic on the
entire body for every smooth solution in the forcing homotopy. -/
theorem dirichletContinuation_uniform_inverse_ellipticity [NeZero n] :
    ∃ lam Λ : ℝ, 0 < lam ∧ 0 < Λ ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ u : CoordinateSpace n → ℝ,
      ContDiff ℝ ∞ u →
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0}, (coordinateHessian u x).PosDef) →
      (∀ x ∈ frontier {y | d.coordinateDefining y ≤ 0}, u x = 0) →
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
        (coordinateHessian u x).det = dirichletContinuationDensity d.coordinateDefining t x) →
      ∀ x ∈ {y | d.coordinateDefining y ≤ 0},
        (coordinateHessian u x).PosDef ∧ ∀ v : CoordinateSpace n,
          lam*(v ⬝ᵥ v) ≤ v ⬝ᵥ ((coordinateHessian u x)⁻¹ *ᵥ v) ∧
          v ⬝ᵥ ((coordinateHessian u x)⁻¹ *ᵥ v) ≤ Λ*(v ⬝ᵥ v) := by
  obtain ⟨K,hK,hKH⟩ := d.dirichletContinuation_uniform_hessian
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  let U := (n:ℝ)^2*max K 1
  let I := ((n.factorial:ℝ)*(max K 1)^n)/c
  let Λ := (n:ℝ)^2*max I 1
  have hn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hU : 0 < U := mul_pos (sq_pos_of_pos hn) (zero_lt_one.trans_le (le_max_right _ _))
  have hΛ : 0 < Λ := mul_pos (sq_pos_of_pos hn) (zero_lt_one.trans_le (le_max_right _ _))
  refine ⟨U⁻¹,Λ,inv_pos.mpr hU,hΛ,?_⟩
  intro t ht u hu hH hub hMA x hx
  have hEq := d.coordinate_equation_on_body hu hMA x hx
  have hdet : c ≤ (coordinateHessian u x).det := by rw [hEq]; exact (hdens t ht x hx).1
  have hp : (coordinateHessian u x).PosDef := posDef_of_posSemidef_det_ne_zero
    (d.coordinate_hessian_posSemidef_on_body hu hH x hx) (hc.trans_le hdet).ne'
  have hentry := hKH t ht u hu hH hub hMA x hx
  have hupper (v : CoordinateSpace n) : v ⬝ᵥ (coordinateHessian u x *ᵥ v) ≤ U*(v ⬝ᵥ v) := by
    have hh := quadraticForm_upper_of_entry_bound (zero_le_one.trans (le_max_right K 1))
      (fun i j => (hentry i j).trans (le_max_left K 1)) v
    rwa [coordinateEuclidean_norm_sq] at hh
  refine ⟨hp,fun v => ⟨inverse_quadratic_lower_of_quadratic_upper hp hU hupper v,?_⟩⟩
  have hInv (i j : Fin n) : |(coordinateHessian u x)⁻¹ i j| ≤ max I 1 :=
    (inverse_entry_bound_of_det_lower hc hdet hentry i j).trans (le_max_left _ _)
  have hh := quadraticForm_upper_of_entry_bound (zero_le_one.trans (le_max_right I 1)) hInv v
  rwa [coordinateEuclidean_norm_sq] at hh

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
