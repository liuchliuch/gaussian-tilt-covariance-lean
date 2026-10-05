import GaussianTilt.MomentMapClassicalDirichletUniformExponentHessian
import GaussianTilt.MomentMapClassicalDirichletIntrinsicThirdBounds
import GaussianTilt.MomentMapClassicalDirichletIntrinsicLipschitz

/-! # Domain-only a priori constants chosen before the input Hölder exponent -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators NNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

theorem intrinsic_dirichletContinuation_uniform_inverse_ellipticity_all_exponents [NeZero n] :
    ∃ lam Λ : ℝ, 0 < lam ∧ 0 < Λ ∧ ∀ (α : ℝ), 0 < α → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ x ∈ {y | d.coordinateDefining y ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 x).PosDef) →
      (∀ x ∈ {y | d.coordinateDefining y ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 x).det = dirichletContinuationDensity d.coordinateDefining t x) →
      ∀ x ∈ {y | d.coordinateDefining y ≤ 0}, ∀ v : CoordinateSpace n,
        lam*(v ⬝ᵥ v) ≤ v ⬝ᵥ ((intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ *ᵥ v) ∧
        v ⬝ᵥ ((intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ *ᵥ v) ≤ Λ*(v ⬝ᵥ v) := by
  obtain ⟨K,hK,hKH⟩ := d.intrinsic_dirichletContinuation_uniform_hessian_all_exponents
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  let U := (n:ℝ)^2*max K 1
  let I := ((n.factorial:ℝ)*(max K 1)^n)/c
  let Λ := (n:ℝ)^2*max I 1
  have hn : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hU : 0 < U := mul_pos (sq_pos_of_pos hn) (zero_lt_one.trans_le (le_max_right _ _))
  have hΛ : 0 < Λ := mul_pos (sq_pos_of_pos hn) (zero_lt_one.trans_le (le_max_right _ _))
  refine ⟨U⁻¹,Λ,inv_pos.mpr hU,hΛ,?_⟩
  intro α hα t ht j hs hp hMA x hx v
  have hentry := hKH α hα t ht j hs hp hMA x hx
  have hdet : c ≤ (intrinsicHessian d.coordinate_body_convex α j.1 x).det := by
    rw [hMA x hx]
    exact (hdens t ht x hx).1
  have hupper (z : CoordinateSpace n) :
      z ⬝ᵥ (intrinsicHessian d.coordinate_body_convex α j.1 x *ᵥ z) ≤ U*(z ⬝ᵥ z) := by
    have hh := quadraticForm_upper_of_entry_bound (zero_le_one.trans (le_max_right K 1))
      (fun i l => (hentry i l).trans (le_max_left K 1)) z
    rwa [coordinateEuclidean_norm_sq] at hh
  refine ⟨inverse_quadratic_lower_of_quadratic_upper (hp x hx) hU hupper v,?_⟩
  have hInv (i l : Fin n) : |(intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ i l| ≤ max I 1 :=
    (inverse_entry_bound_of_det_lower hc hdet hentry i l).trans (le_max_left _ _)
  have hh := quadraticForm_upper_of_entry_bound (zero_le_one.trans (le_max_right I 1)) hInv v
  rwa [coordinateEuclidean_norm_sq] at hh


theorem intrinsic_dirichletContinuation_scaled_inverse_derivative_bound_all_exponents [NeZero n] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : ℝ), 0 < α → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ x : CoordinateSpace n, ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r →
        y ∈ interior {z | d.coordinateDefining z ≤ 0}) → ∀ k a b,
      r*|coordinateDerivative k (fun y => (intrinsicHessian d.coordinate_body_convex α j.1 y)⁻¹ a b) x| ≤ C := by
  obtain ⟨K,hK,hKH⟩ := d.intrinsic_dirichletContinuation_uniform_hessian_all_exponents
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K₂,hK₂,hF₂⟩ := dirichletContinuationDensity_uniform_log_hessian d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K₃,hK₃,hF₃⟩ := dirichletContinuationDensity_uniform_log_thirdDerivatives d.coordinate_body_compact
    d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  let K₀ := max (-Real.log c) 0
  let T := 2*variableThirdDerivativeBound n K K₀ K₂ K₃ 1
  let I := ((n.factorial:ℝ)*(max K 1)^n)/c
  have hT : 0 ≤ T := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hI : 0 ≤ I := by dsimp [I]; positivity
  refine ⟨(n:ℝ)^2*I*T*I,by positivity,?_⟩
  intro α hα t ht j hs hp hMA x r hr hr1 hball k a b
  let B := {y : CoordinateSpace n | ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ ≤ r/2}
  have hBc : IsCompact B := isCompact_coordinateEuclidean_closedBall x (r/2)
  have hBin : B ⊆ interior {y | d.coordinateDefining y ≤ 0} :=
    fun y hy => hball y (lt_of_le_of_lt hy (half_lt_self hr))
  have hxB : x ∈ B := by simp only [B,sub_self,norm_zero,mem_setOf_eq]; exact (half_pos hr).le
  have hxint := hBin hxB
  obtain ⟨u,hu,he⟩ := exists_global_smooth_coordinate_eq_near_compact isOpen_interior hs hBc hBin
  have hHu (y : CoordinateSpace n) (hy : y ∈ B) :
      intrinsicHessian d.coordinate_body_convex α j.1 y = coordinateHessian u y :=
    (intrinsicHessian_eq_actual d.coordinate_body_convex hα j.1 (hBin hy)).trans (coordinateHessian_congr_nhds (he y hy)).symm
  have hHnear : intrinsicHessian d.coordinate_body_convex α j.1 =ᶠ[𝓝 x] coordinateHessian u := by
    filter_upwards [isOpen_interior.mem_nhds hxint,(he x hxB).eventually_nhds] with y hy hey
    exact (intrinsicHessian_eq_actual d.coordinate_body_convex hα j.1 hy).trans (coordinateHessian_congr_nhds hey).symm
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.log _ (fun y => (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y)).ne')
    exact (contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp (contDiff_const.prodMk contDiff_id)
  have hMAlog (y : CoordinateSpace n) (hy : y ∈ {z | d.coordinateDefining z ≤ 0}) :
      (intrinsicHessian d.coordinate_body_convex α j.1 y).det = Real.exp (F y) := by
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
    exact hMA y hy
  have hnear : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y) := by
    filter_upwards [isOpen_interior.mem_nhds hxint,hHnear] with y hy hey
    rw [← hey]
    exact hMAlog y (interior_subset hy)
  have hInv : ∀ i l, |(coordinateHessian u x)⁻¹ i l| ≤ I := by
    rw [← hHu x hxB]
    exact inverse_entry_bound_of_det_lower hc
      (by rw [hMA x (interior_subset hxint)]; exact (hdens t ht x (interior_subset hxint)).1)
      (hKH α hα t ht j hs hp hMA x (interior_subset hxint))
  have hThird (i l q : Fin n) : r*|coordinateThirdDerivative u x i l q| ≤ T := by
    have hR : 0 < r/2 := half_pos hr
    have hbmem (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r/2) : y ∈ B := hy.le
    have hh := variable_thirdDerivative_bound_on_ball_of_hessian_bound (Nat.pos_of_ne_zero (NeZero.ne n))
      hu hF x hR hK₂ hK₃
      (fun y hy => by rw [← hHu y (hbmem y hy)]; exact hp y (interior_subset (hBin (hbmem y hy))))
      (fun y hy => by rw [← hHu y (hbmem y hy)]; exact hMAlog y (interior_subset (hBin (hbmem y hy))))
      (fun y hy => by rw [← hHu y (hbmem y hy)]; exact hKH α hα t ht j hs hp hMA y (interior_subset (hBin (hbmem y hy))))
      (fun y hy => (show -K₀ ≤ Real.log c from by dsimp [K₀]; linarith [le_max_left (-Real.log c) 0]).trans
        (Real.log_le_log hc (hdens t ht y (interior_subset (hBin (hbmem y hy)))).1))
      (fun y hy => hF₂ t ht y (interior_subset (hBin (hbmem y hy))))
      (fun y hy => hF₃ t ht y (interior_subset (hBin (hbmem y hy)))) i l q
    have hscaled := (mul_le_mul_of_nonneg_left hh hR.le).trans
      (variableThirdDerivativeBound_scaled hK₂ hK₃ hR (by linarith))
    dsimp [T]
    nlinarith
  have hInvNear : (fun y => (intrinsicHessian d.coordinate_body_convex α j.1 y)⁻¹ a b) =ᶠ[𝓝 x]
      (fun y => (coordinateHessian u y)⁻¹ a b) := hHnear.mono
    (fun y hy => congrArg (fun H : Matrix (Fin n) (Fin n) ℝ => H⁻¹ a b) hy)
  rw [coordinateDerivative_congr_nhds hInvNear]
  exact scaled_inverse_hessian_derivative_bound hu hF hnear hr.le hI hT hInv hThird k a b


theorem intrinsic_dirichletContinuation_scaled_third_bound_all_exponents [NeZero n] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : ℝ), 0 < α → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ x : CoordinateSpace n, ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r →
        y ∈ interior {z | d.coordinateDefining z ≤ 0}) → ∀ k a b,
      r*|coordinateDerivative k (fun y => intrinsicHessian d.coordinate_body_convex α j.1 y a b) x| ≤ C := by
  obtain ⟨K,hK,hKH⟩ := d.intrinsic_dirichletContinuation_uniform_hessian_all_exponents
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K₂,hK₂,hF₂⟩ := dirichletContinuationDensity_uniform_log_hessian d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K₃,hK₃,hF₃⟩ := dirichletContinuationDensity_uniform_log_thirdDerivatives d.coordinate_body_compact
    d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  let K₀ := max (-Real.log c) 0
  let T := 2*variableThirdDerivativeBound n K K₀ K₂ K₃ 1
  have hT : 0 ≤ T := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  refine ⟨T,hT,?_⟩
  intro α hα t ht j hs hp hMA x r hr hr1 hball k a b
  let B := {y : CoordinateSpace n | ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ ≤ r/2}
  have hBc : IsCompact B := isCompact_coordinateEuclidean_closedBall x (r/2)
  have hBin : B ⊆ interior {y | d.coordinateDefining y ≤ 0} :=
    fun y hy => hball y (lt_of_le_of_lt hy (half_lt_self hr))
  have hxB : x ∈ B := by simp only [B,sub_self,norm_zero,mem_setOf_eq]; exact (half_pos hr).le
  have hxint := hBin hxB
  obtain ⟨u,hu,he⟩ := exists_global_smooth_coordinate_eq_near_compact isOpen_interior hs hBc hBin
  have hHu (y : CoordinateSpace n) (hy : y ∈ B) :
      intrinsicHessian d.coordinate_body_convex α j.1 y = coordinateHessian u y :=
    (intrinsicHessian_eq_actual d.coordinate_body_convex hα j.1 (hBin hy)).trans (coordinateHessian_congr_nhds (he y hy)).symm
  have hHnear : intrinsicHessian d.coordinate_body_convex α j.1 =ᶠ[𝓝 x] coordinateHessian u := by
    filter_upwards [isOpen_interior.mem_nhds hxint,(he x hxB).eventually_nhds] with y hy hey
    exact (intrinsicHessian_eq_actual d.coordinate_body_convex hα j.1 hy).trans (coordinateHessian_congr_nhds hey).symm
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.log _ (fun y => (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y)).ne')
    exact (contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp (contDiff_const.prodMk contDiff_id)
  have hMAlog (y : CoordinateSpace n) (hy : y ∈ {z | d.coordinateDefining z ≤ 0}) :
      (intrinsicHessian d.coordinate_body_convex α j.1 y).det = Real.exp (F y) := by
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
    exact hMA y hy
  have hThird (i l q : Fin n) : r*|coordinateThirdDerivative u x i l q| ≤ T := by
    have hR : 0 < r/2 := half_pos hr
    have hbmem (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r/2) : y ∈ B := hy.le
    have hh := variable_thirdDerivative_bound_on_ball_of_hessian_bound (Nat.pos_of_ne_zero (NeZero.ne n))
      hu hF x hR hK₂ hK₃
      (fun y hy => by rw [← hHu y (hbmem y hy)]; exact hp y (interior_subset (hBin (hbmem y hy))))
      (fun y hy => by rw [← hHu y (hbmem y hy)]; exact hMAlog y (interior_subset (hBin (hbmem y hy))))
      (fun y hy => by rw [← hHu y (hbmem y hy)]; exact hKH α hα t ht j hs hp hMA y (interior_subset (hBin (hbmem y hy))))
      (fun y hy => (show -K₀ ≤ Real.log c from by dsimp [K₀]; linarith [le_max_left (-Real.log c) 0]).trans
        (Real.log_le_log hc (hdens t ht y (interior_subset (hBin (hbmem y hy)))).1))
      (fun y hy => hF₂ t ht y (interior_subset (hBin (hbmem y hy))))
      (fun y hy => hF₃ t ht y (interior_subset (hBin (hbmem y hy)))) i l q
    have hscaled := (mul_le_mul_of_nonneg_left hh hR.le).trans
      (variableThirdDerivativeBound_scaled hK₂ hK₃ hR (by linarith))
    dsimp [T]
    nlinarith
  have hHentry : (fun y => intrinsicHessian d.coordinate_body_convex α j.1 y a b) =ᶠ[𝓝 x]
      (fun y => coordinateHessian u y a b) := hHnear.mono
    (fun y hy => congrArg (fun H : Matrix (Fin n) (Fin n) ℝ => H a b) hy)
  rw [coordinateDerivative_congr_nhds hHentry]
  exact hThird a b k


theorem intrinsic_dirichletContinuation_uniform_first_lipschitz_all_exponents [NeZero n] :
    ∃ C : ℝ≥0, ∀ (α : ℝ), 0 < α → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ a, LipschitzOnWith C (intrinsicDerivative d.coordinate_body_convex α j.1 a)
        {y | d.coordinateDefining y ≤ 0} := by
  obtain ⟨K,hK,hbound⟩ := d.intrinsic_dirichletContinuation_uniform_hessian_all_exponents
  refine ⟨(n:ℝ≥0)*⟨K,hK⟩,?_⟩
  intro α hα t ht j hs hp hMA a
  exact intrinsicDerivative_lipschitzOn_of_hessian_bound d.coordinate_body_convex hα j.1 (K := ⟨K,hK⟩)
    (hbound α hα t ht j hs hp hMA) a


end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
