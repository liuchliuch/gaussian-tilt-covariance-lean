import GaussianTilt.MomentMapClassicalDirichletUniformExponentChart

/-! # Domain-only a priori constants chosen before the input Hölder exponent -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

theorem intrinsic_flat_scalar_data_all_exponents [NeZero n]
    (p : BoundaryChartPatch d.coordinateDefining)
    {s c Cx : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hc : 0 < c) (hCx : 0 ≤ Cx)
    (hXs : ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → ContDiffAt ℝ ∞ (d.intrinsicScaledChart p s) y)
    (hXb : ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 →
      ‖fderiv ℝ (d.intrinsicScaledChart p s) y‖ ≤ Cx ∧
      ‖fderiv ℝ (fderiv ℝ (d.intrinsicScaledChart p s)) y‖ ≤ Cx)
    (hXp : ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → d.intrinsicScaledChart p s y ∈ Metric.closedBall p.center p.radius)
    (hXlevel : ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 →
      d.coordinateDefining (d.intrinsicScaledChart p s y) = -s*y p.index)
    (hBall : ∀ y ∈ flatHalfBall p.index, c*s*y p.index ≤ 1 ∧
      ∀ z, ‖(coordinateEquiv n).symm z-(coordinateEquiv n).symm (d.intrinsicScaledChart p s y)‖ < c*s*y p.index →
        z ∈ interior {x | d.coordinateDefining x ≤ 0}) :
    ∃ β : Fin n → CoordinateSpace n → ℝ, ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      (∀ a, ContDiff ℝ ∞ (β a)) ∧
      (∀ x ∈ Metric.closedBall p.center p.radius, ∀ a,
        β a =ᶠ[𝓝 x] boundaryChartCoefficient d.coordinateDefining p.index a) ∧
      ∀ (α : ℝ), 0 < α → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ a,
      let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
      let T := intrinsicTangentField d.coordinate_body_convex α j.1 (β a) a p.index
      let g := intrinsicTangentSource d.coordinate_body_convex α j.1 F (β a) a p.index
      let b := fun x => linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ d.coordinateDefining x
      let X := d.intrinsicScaledChart p s
      let D := fun y => (intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index (X y)).comp (fderiv ℝ X y)
      FlatScalarData p.index (T ∘ X) (flattenedTangentForcing s g b T X p.index) D M B := by
  obtain ⟨β,N,hN,hβ,heβ,hscalar⟩ := d.intrinsic_dirichletContinuation_chart_scalar_bounds_all_exponents p
  obtain ⟨Cw,hCw,hwithin⟩ := d.intrinsic_dirichletContinuation_chart_within_bounds_all_exponents p
  let M₀ := N+N*((n:ℝ)*N*Cx)
  let M₁ := (n:ℝ)*N*Cx+((n:ℝ)*N*Cx)*((n:ℝ)*N*Cx)+N*((n:ℝ)^2*N*Cx^2+(n:ℝ)*N*Cx)
  let M := max (max M₀ (M₁/(c*s))) 0
  refine ⟨β,M,Cw*Cx,le_max_right _ _,mul_nonneg hCw hCx,hβ,heβ,?_⟩
  intro α hα t ht j hsm hp hMA a
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  let T := intrinsicTangentField d.coordinate_body_convex α j.1 (β a) a p.index
  let g := intrinsicTangentSource d.coordinate_body_convex α j.1 F (β a) a p.index
  let b := fun x => linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ d.coordinateDefining x
  let X := d.intrinsicScaledChart p s
  let D := fun y => (intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index (X y)).comp (fderiv ℝ X y)
  have hXmap : MapsTo X (flatClosedHalfBall p.index) {x | d.coordinateDefining x ≤ 0} := by
    intro y hy
    change d.coordinateDefining (X y) ≤ 0
    rw [hXlevel y hy.1]
    nlinarith [hy.2]
  have hXi (y : CoordinateSpace n) (hy : y ∈ flatHalfBall p.index) :
      X y ∈ interior {x | d.coordinateDefining x ≤ 0} := by
    rw [d.coordinate_body_interior]
    change d.coordinateDefining (X y) < 0
    rw [hXlevel y hy.1.le]
    nlinarith [hy.2]
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.log _ (fun y => (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y)).ne')
    exact (contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp (contDiff_const.prodMk contDiff_id)
  have hMAlog (y : CoordinateSpace n) (hy : y ∈ interior {z | d.coordinateDefining z ≤ 0}) :
      (intrinsicHessian d.coordinate_body_convex α j.1 y).det = Real.exp (F y) := by
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
    exact hMA y (interior_subset hy)
  have hTc := continuousOn_intrinsicTangentField d.coordinate_body_convex α j.1 (hβ a).continuous.continuousOn a p.index
  have hTs := contDiffOn_intrinsicTangentField d.coordinate_body_convex hα j.1 hsm (hβ a) a p.index
  have hgs := contDiffOn_intrinsicTangentSource d.coordinate_body_convex hα j.1 hsm hF (hβ a) hMAlog a p.index
  have hbs := contDiffOn_intrinsicCurvature d.coordinate_body_convex hα j.1 hsm hF d.coordinateDefining_smooth hMAlog
  have hXc : ContinuousOn X (flatClosedHalfBall p.index) := fun y hy => (hXs y hy.1).continuousAt.continuousWithinAt
  have hDXc : ContinuousOn (fderiv ℝ X) (flatClosedHalfBall p.index) := by
    intro y hy
    exact ((hXs y hy.1).fderiv_right (m:=0) (by simp)).continuousAt.continuousWithinAt
  have hDb (y : CoordinateSpace n) (hy : y ∈ flatClosedHalfBall p.index) : ‖D y‖ ≤ Cw*Cx := by
    have hh := (hwithin α hα t ht j hsm hp hMA (X y) (hXp y hy.1) (hXmap hy) a (β a) (heβ _ (hXp y hy.1) a)).2
    exact ((intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index (X y)).opNorm_comp_le _).trans
      (mul_le_mul hh (hXb y hy.1).1 (norm_nonneg _) hCw)
  have hforce (y : CoordinateSpace n) (hy : y ∈ flatHalfBall p.index) :
      |flattenedTangentForcing s g b T X p.index y| ≤ M ∧
      ∀ k, y p.index*|coordinateDerivative k (flattenedTangentForcing s g b T X p.index) y| ≤ M := by
    have hr : 0 < c*s*y p.index := mul_pos (mul_pos hc hs) hy.2
    have hdata := hscalar α hα t ht j hsm hp hMA (X y) (hXp y hy.1.le) (c*s*y p.index) hr
      (hBall y hy).1 (hBall y hy).2 a
    have hh := flattenedTangentForcing_bounds hs.le hs1
      ((hgs.contDiffAt (isOpen_interior.mem_nhds (hXi y hy))).differentiableAt (by simp))
      ((hbs.contDiffAt (isOpen_interior.mem_nhds (hXi y hy))).differentiableAt (by simp))
      (contDiffAt_infty.mp (hTs.contDiffAt (isOpen_interior.mem_nhds (hXi y hy))) 2)
      (contDiffAt_infty.mp (hXs y hy.1.le) 2) hr (hBall y hy).1 hN hN hN hN hCx
      hdata.2.2.2.1 hdata.2.2.2.2.2.1 hdata.2.2.2.2.1 hdata.2.2.2.2.2.2
      hdata.2.1 hdata.2.2.1 (hXb y hy.1.le).1 (hXb y hy.1.le).2 p.index
    refine ⟨hh.1.trans ((le_max_left M₀ (M₁/(c*s))).trans (le_max_left _ _)),?_⟩
    intro k
    have hbnd : y p.index*|coordinateDerivative k (flattenedTangentForcing s g b T X p.index) y| ≤ M₁/(c*s) := by
      apply (le_div_iff₀ (mul_pos hc hs)).mpr
      have hh' := hh.2 k
      dsimp [M₁]
      nlinarith
    exact hbnd.trans ((le_max_right M₀ (M₁/(c*s))).trans (le_max_left _ _))
  refine ⟨hTc.comp hXc hXmap,?_,?_,?_,?_,hDb,?_,fun y hy => (hforce y hy).1,fun y hy => (hforce y hy).2⟩
  · intro y hy
    exact ((hTs.contDiffAt (isOpen_interior.mem_nhds (hXi y hy))).comp y (hXs y hy.1.le)).contDiffWithinAt
  · intro y hy
    exact (contDiffAt_flattenedTangentForcing s
      (hgs.contDiffAt (isOpen_interior.mem_nhds (hXi y hy)))
      (hbs.contDiffAt (isOpen_interior.mem_nhds (hXi y hy)))
      (hTs.contDiffAt (isOpen_interior.mem_nhds (hXi y hy))) (hXs y hy.1.le) p.index).contDiffWithinAt
  · exact ((continuousOn_intrinsicTangentDifferential d.coordinate_body_convex α j.1 (hβ a) a p.index).comp hXc hXmap).clm_comp hDXc
  · intro y hy
    exact (intrinsicTangentField_hasFDerivWithinAt d.coordinate_body_convex hα j.1 (hXmap hy)
      ((hβ a).differentiable (by simp) _) a p.index).comp y
      ((hXs y hy.1).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt hXmap
  · intro y hy hyq
    have hx0 : d.coordinateDefining (X y)=0 := by rw [hXlevel y hy,hyq,mul_zero]
    obtain ⟨a₀,b₀,ha₀,hb₀,hab⟩ := d.intrinsic_dirichletContinuation_scaled_barriers hα
    have hbarr := hab t ht j (fun x hx => hp x (interior_subset hx))
      (fun x hx => hMA x (interior_subset hx))
    have he := (intrinsicTangentField_congr_nhds_beta d.coordinate_body_convex α j.1 (heβ _ (hXp y hy) a) a p.index).self_of_nhds
    exact he.trans (d.intrinsic_tangent_field_zero hα j p (hXp y hy) hx0 hbarr a)


end SmoothInnerDomain
namespace IntrinsicFixedChart
variable {S A : Set (E n)} {d : SmoothInnerDomain S A} {p : BoundaryChartPatch d.coordinateDefining} (c : IntrinsicFixedChart d p)

theorem exists_intrinsic_flat_system_all_exponents [NeZero n] :
    ∃ β : Fin n → CoordinateSpace n → ℝ, ∃ lam Λ K M B : ℝ,
      0 < lam ∧ 0 < Λ ∧ 0 ≤ K ∧ 0 ≤ M ∧ 0 ≤ B ∧
      (∀ a, ContDiff ℝ ∞ (β a)) ∧
      (∀ x ∈ Metric.closedBall p.center p.radius, ∀ a,
        β a =ᶠ[𝓝 x] boundaryChartCoefficient d.coordinateDefining p.index a) ∧
      ∀ (α : ℝ), 0 < α → α < 1 → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ a,
      let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
      let T := intrinsicTangentField d.coordinate_body_convex α j.1 (β a) a p.index
      let g := intrinsicTangentSource d.coordinate_body_convex α j.1 F (β a) a p.index
      let b := fun x => linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ d.coordinateDefining x
      let X := d.intrinsicScaledChart p c.scale
      let D := fun y => (intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index (X y)).comp (fderiv ℝ X y)
      let Ac := scaledRawChartCoefficient d.smooth (d.physicalChartCenter p) p.index
        (d.physicalChartCenter_transverse p) c.scale (fun x => (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹)
      LocalFlatEllipticSystem p.index (T ∘ X) (flattenedTangentForcing c.scale g b T X p.index) Ac lam Λ K M ∧
      FlatScalarData p.index (T ∘ X) (flattenedTangentForcing c.scale g b T X p.index) D M B := by
  obtain ⟨β,M,B,hM,hB,hβ,heβ,hscalar⟩ := d.intrinsic_flat_scalar_data_all_exponents p
    c.scale_pos c.scale_le_one c.radius_factor_pos (zero_le_one.trans c.raw_bound_ge_one)
    (fun y hy => (c.raw_smooth y (by linarith)).1)
    (fun y hy => ⟨(c.raw_derivatives y hy).1.1,(c.raw_derivatives y hy).1.2.1⟩)
    (fun y hy => c.map_patch hy) (fun y hy => c.level hy)
    (fun y hy => ⟨(c.interior_ball hy).2.1,(c.interior_ball hy).2.2⟩)
  obtain ⟨lam,Λ,hlam,hΛ,hEll⟩ := d.intrinsic_dirichletContinuation_uniform_inverse_ellipticity_all_exponents
  obtain ⟨K,hK,hDA⟩ := d.intrinsic_dirichletContinuation_scaled_inverse_derivative_bound_all_exponents
  let Q := (n:ℝ)^2*c.chart_bound^2
  have hn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hCpos : 0 < c.chart_bound := zero_lt_one.trans_le c.chart_bound_ge_one
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let Kc := (n:ℝ)^2*c.jacobian_bound^2*(2*Λ+(n:ℝ)*K*c.raw_bound/(c.radius_factor*c.scale))
  have hKc : 0 ≤ Kc := by
    dsimp [Kc]
    have hCx := c.raw_bound_ge_one
    have hc := c.radius_factor_pos
    have hs := c.scale_pos
    positivity
  refine ⟨β,lam/Q,Λ*Q,Kc,M,B,div_pos hlam hQ,mul_pos hΛ hQ,hKc,hM,hB,hβ,heβ,?_⟩
  intro α hα hα1 t ht j hp hMA a
  have hs := d.intrinsic_dirichletContinuation_interior_smooth hα hα1 ht j hp hMA
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  let T := intrinsicTangentField d.coordinate_body_convex α j.1 (β a) a p.index
  let g := intrinsicTangentSource d.coordinate_body_convex α j.1 F (β a) a p.index
  let b := fun x => linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ d.coordinateDefining x
  let X := d.intrinsicScaledChart p c.scale
  let Ac := scaledRawChartCoefficient d.smooth (d.physicalChartCenter p) p.index
    (d.physicalChartCenter_transverse p) c.scale (fun x => (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹)
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.log _ (fun y => (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y)).ne')
    exact (contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp (contDiff_const.prodMk contDiff_id)
  have hMAlog (z : CoordinateSpace n) (hz : z ∈ interior {w | d.coordinateDefining w ≤ 0}) :
      (intrinsicHessian d.coordinate_body_convex α j.1 z).det = Real.exp (F z) := by
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef z))]
    exact hMA z (interior_subset hz)
  have hAs (i l : Fin n) := contDiffOn_intrinsicInverseHessian d.coordinate_body_convex hα j.1 hs hF hMAlog i l
  have hcBounds (y : CoordinateSpace n) (hy : y ∈ flatHalfBall p.index) :
      (Ac y).PosDef ∧ (∀ v : CoordinateSpace n,
        (lam/Q)*‖(coordinateEquiv n).symm v‖^2 ≤ v ⬝ᵥ (Ac y *ᵥ v) ∧
        v ⬝ᵥ (Ac y *ᵥ v) ≤ (Λ*Q)*‖(coordinateEquiv n).symm v‖^2) ∧
      ∀ k i l, y p.index*|matrixCoordinateDerivative Ac k y i l| ≤ Kc := by
    apply scaled_raw_chart_coefficient_bounds d.smooth (d.physicalChartCenter p) p.index
      (d.physicalChartCenter_transverse p) (Nat.pos_of_ne_zero (NeZero.ne n))
      c.scale_pos c.radius_factor_pos c.chart_bound_ge_one c.raw_bound_ge_one c.jacobian_bound_ge_one
      p.radius_pos hlam.le hΛ.le hK c.inverse c.forward c.raw_smooth c.raw_derivatives hy.1.le hy.2
    · exact (hp _ (interior_subset (c.map_interior hy))).inv
    · intro i l
      exact ((hAs i l).contDiffAt (isOpen_interior.mem_nhds (c.map_interior hy))).differentiableAt (by simp)
    · intro v
      have hh := hEll α hα t ht j hs hp hMA (X y) (interior_subset (c.map_interior hy)) v
      simpa only [coordinateEuclidean_norm_sq] using hh
    · intro k i l
      exact hDA α hα t ht j hs hp hMA (X y) (c.radius_factor*c.scale*y p.index)
        (c.interior_ball hy).1 (c.interior_ball hy).2.1 (c.interior_ball hy).2.2 k i l
  have hsd := hscalar α hα t ht j hs hp hMA a
  refine ⟨⟨hsd.continuous,hsd.smooth,hsd.forcing_smooth,?_,
    fun y hy => (hcBounds y hy).1,fun y hy => (hcBounds y hy).2.1,
    fun y hy => (hcBounds y hy).2.2,hsd.forcing_bound,hsd.forcing_derivative_bound,?_⟩,hsd⟩
  · intro i l y hy
    have hraw := c.raw_smooth y (by linarith [hy.1])
    exact (contDiffAt_scaledRawChartCoefficient d.smooth (d.physicalChartCenter p) p.index
      (d.physicalChartCenter_transverse p) c.scale hraw.1 hraw.2
      (fun k m => (hAs k m).contDiffAt (isOpen_interior.mem_nhds (c.map_interior hy))) i l).contDiffWithinAt
  · intro y hy
    exact d.intrinsic_scaled_chart_equation hα p c.scale ht j hs hp hMA
      (c.map_interior hy) (c.map_patch hy.1.le) (c.scaled_target hy.1.le) (β a) (hβ a) a


end IntrinsicFixedChart
end GaussianTilt.MomentMapRegularity
