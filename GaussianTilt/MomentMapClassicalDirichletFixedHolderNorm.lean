import GaussianTilt.MomentMapClassicalDirichletUniformExponentGlobal
import GaussianTilt.MomentMapHolderFixedExponentBounds

/-! # A genuine fixed-exponent Banach a priori bound for nonlinear continuation

The boundary exponent and all analytic constants are chosen before the
Banach exponent. Lower-order Hölder moduli follow from actual derivatives.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Set Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- A single genuine C²,δ norm controls every admissible homotopy solution.
The positive δ is selected noncircularly from the proved domain-only γ. -/
theorem intrinsic_dirichletContinuation_uniform_holder_jet_norm [NeZero n] :
    ∃ δ B : ℝ, 0 < δ ∧ δ < 1 ∧ 0 ≤ B ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex δ,
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex δ j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex δ j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ‖j‖ ≤ B := by
  obtain ⟨γ, C, hγ, hγ1, hC, hHolder⟩ := d.intrinsic_dirichletContinuation_global_hessian_holder_all_exponents
  obtain ⟨a, b, ha, hb, hbar⟩ := d.intrinsic_dirichletContinuation_scaled_barriers_all_exponents
  obtain ⟨W, hW, hwW, _⟩ := d.coordinate_defining_first_bounds
  obtain ⟨G, hG, hFirst⟩ := d.intrinsic_dirichletContinuation_uniform_first_all_exponents
  obtain ⟨H, hH, hSecond⟩ := d.intrinsic_dirichletContinuation_uniform_hessian_all_exponents
  let δ := min (γ/2) (1/2 : ℝ)
  have hδ : 0 < δ := lt_min (half_pos hγ) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδγ : δ ≤ γ := (min_le_left _ _).trans (by linarith)
  let L := ‖(coordinateEquiv n).symm.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  let C₂ := (n:ℝ)^2*C*L^γ
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  let B := 2*(b*W+(n:ℝ)*G+(n:ℝ)^2*H+C₂+1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨δ, B, hδ, hδ1, hB, ?_⟩
  intro t ht j hp hMA
  have hs := d.intrinsic_dirichletContinuation_interior_smooth hδ hδ1 ht j hp hMA
  let Q := {x : CoordinateSpace n | d.coordinateDefining x ≤ 0}
  have hv (x : Q) : ‖value Q ℝ δ (jetValue (CoordinateSpace n) ℝ d.coordinate_body_convex δ j.1) x‖ ≤ b*W := by
    have hh := hbar δ hδ t ht j (fun y hy => hp y (interior_subset hy))
      (fun y hy => hMA y (interior_subset hy)) x x.2
    have hw := hwW x x.2
    have hw0 : d.coordinateDefining x ≤ 0 := x.2
    have he : intrinsicValue d.coordinate_body_convex δ j.1 x =
        value Q ℝ δ (jetValue (CoordinateSpace n) ℝ d.coordinate_body_convex δ j.1) x := extendValue_mem δ _ x.2
    rw [he] at hh
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by nlinarith [(abs_le.mp hw).1], by nlinarith⟩
  have hD (x : Q) : ‖value Q (CoordinateSpace n →L[ℝ] ℝ) δ
      (jetFirst (CoordinateSpace n) ℝ d.coordinate_body_convex δ j.1) x‖ ≤ (n:ℝ)*G := by
    apply norm_covector_le_of_coordinate_bound _ hG
    intro i
    have hh := hFirst δ hδ t ht j hs (fun y hy => hp y (interior_subset hy))
      (fun y hy => hMA y (interior_subset hy)) x x.2 i
    simpa only [intrinsicDerivative, intrinsicFirst, extendValue_mem δ _ x.2] using hh
  have hHH (x : Q) : ‖value Q (CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ) δ
      (jetSecond (CoordinateSpace n) ℝ d.coordinate_body_convex δ j.1) x‖ ≤ (n:ℝ)^2*H := by
    apply norm_bilinear_le_of_coordinate_bound _ hH
    intro i l
    have hh := hSecond δ hδ t ht j hs hp hMA x x.2 l i
    simpa only [intrinsicHessian, intrinsicSecond, extendValue_mem δ _ x.2] using hh
  have hHC (x y : Q) :
      ‖value Q (CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ) δ
        (jetSecond (CoordinateSpace n) ℝ d.coordinate_body_convex δ j.1) x -
        value Q (CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ) δ
        (jetSecond (CoordinateSpace n) ℝ d.coordinate_body_convex δ j.1) y‖ ≤ C₂*dist x y^γ := by
    have hx : (coordinateEquiv n).symm x ∈ d.body := x.2
    have hy : (coordinateEquiv n).symm y ∈ d.body := y.2
    have hd : dist ((coordinateEquiv n).symm x) ((coordinateEquiv n).symm y) ≤ L*dist x y := by
      rw [dist_eq_norm, ← map_sub]
      exact (coordinateEquiv n).symm.toContinuousLinearMap.le_opNorm ((x : CoordinateSpace n)-y)
    have hpow := Real.rpow_le_rpow dist_nonneg hd hγ.le
    rw [Real.mul_rpow hL dist_nonneg] at hpow
    have hh (i l : Fin n) : |intrinsicHessian d.coordinate_body_convex δ j.1 x i l-
        intrinsicHessian d.coordinate_body_convex δ j.1 y i l| ≤ (C*L^γ)*dist x y^γ := by
      have he := hHolder δ hδ hδ1 t ht j hp hMA _ hx _ hy i l
      simp only [ContinuousLinearEquiv.apply_symm_apply] at he
      exact he.trans ((mul_le_mul_of_nonneg_left hpow hC).trans_eq (by ring))
    have hBnd := norm_bilinear_le_of_coordinate_bound
      (value Q (CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ) δ
        (jetSecond (CoordinateSpace n) ℝ d.coordinate_body_convex δ j.1) x -
       value Q (CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ) δ
        (jetSecond (CoordinateSpace n) ℝ d.coordinate_body_convex δ j.1) y)
      (show 0 ≤ (C*L^γ)*dist x y^γ by positivity)
      (fun i l => by simpa only [ContinuousLinearMap.sub_apply, intrinsicHessian, intrinsicSecond,
        extendValue_mem δ _ x.2, extendValue_mem δ _ y.2] using hh l i)
    exact hBnd.trans_eq (by dsimp [C₂]; ring)
  exact jet_norm_le_of_bounded_fields_and_higher_hessian d.coordinate_body_convex hδ hδ1.le hδγ
    (mul_nonneg hb.le hW) (mul_nonneg (Nat.cast_nonneg _) hG)
    (mul_nonneg (sq_nonneg _) hH) hC₂ j.1 hv hD hHH hHC

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
