import GaussianTilt.MomentMapClassicalDirichletIntrinsicHessian

/-! # Domain-only a priori constants chosen before the input Hölder exponent -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

theorem intrinsic_dirichletContinuation_scaled_barriers_all_exponents [NeZero n] :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ (α : ℝ), 0 < α → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
        (intrinsicHessian d.coordinate_body_convex α j.1 x).PosDef) →
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
        (intrinsicHessian d.coordinate_body_convex α j.1 x).det = dirichletContinuationDensity d.coordinateDefining t x) →
      ∀ x ∈ {y | d.coordinateDefining y ≤ 0},
        b*d.coordinateDefining x ≤ intrinsicValue d.coordinate_body_convex α j.1 x ∧
        intrinsicValue d.coordinate_body_convex α j.1 x ≤ a*d.coordinateDefining x := by
  obtain ⟨a,b,ha,hb,hbar⟩ := dirichletContinuation_scaled_barriers d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth
    (fun x _ => d.coordinateDefining_hessian_posDef x) d.coordinate_zero_boundary
  refine ⟨a,b,ha,hb,?_⟩
  intro α hα t ht j hp hMA
  apply hbar t ht (intrinsicValue d.coordinate_body_convex α j.1)
    (continuousOn_extendValue α _) (fun x hx =>
      (jet_contDiffOn_two d.coordinate_body_convex hα j.1).contDiffAt (isOpen_interior.mem_nhds hx))
  · intro x hx
    rw [← intrinsicHessian_eq_actual d.coordinate_body_convex hα j.1 hx]
    exact hp x hx
  · exact fun x hx => zeroBoundary_value d.coordinate_body_convex d.coordinate_body_compact.isClosed α j hx
  · intro x hx
    rw [← intrinsicHessian_eq_actual d.coordinate_body_convex hα j.1 hx]
    exact hMA x hx


theorem intrinsic_dirichletContinuation_uniform_first_all_exponents [NeZero n] :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (α : ℝ), 0 < α → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
        (intrinsicHessian d.coordinate_body_convex α j.1 x).PosDef) →
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
        (intrinsicHessian d.coordinate_body_convex α j.1 x).det = dirichletContinuationDensity d.coordinateDefining t x) →
      ∀ x ∈ {y | d.coordinateDefining y ≤ 0}, ∀ i,
        |intrinsicDerivative d.coordinate_body_convex α j.1 i x| ≤ G := by
  obtain ⟨a,b,ha,hb,hbar⟩ := d.intrinsic_dirichletContinuation_scaled_barriers_all_exponents
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K,hK,hKF⟩ := dirichletContinuationDensity_uniform_log_coordinateDerivative d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨W,hW,hwW,hDw⟩ := d.coordinate_defining_first_bounds
  let c₀ := d.modulus/max 1 D
  have hmax : 0 < max 1 D := zero_lt_one.trans_le (le_max_left _ _)
  have hc₀ : 0 < c₀ := div_pos d.modulus_pos hmax
  let C := K/c₀
  have hC : 0 ≤ C := div_nonneg hK hc₀.le
  refine ⟨b*W+C*W,add_nonneg (mul_nonneg hb.le hW) (mul_nonneg hC hW),?_⟩
  intro α hα t ht j hs hp hMA x hx i
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  have hMAlog (y : CoordinateSpace n) (hy : y ∈ interior {z | d.coordinateDefining z ≤ 0}) :
      (intrinsicHessian d.coordinate_body_convex α j.1 y).det = Real.exp (F y) := by
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
    exact hMA y hy
  have hbd (y : CoordinateSpace n) (hy : y ∈ frontier {z | d.coordinateDefining z ≤ 0}) :
      |intrinsicDerivative d.coordinate_body_convex α j.1 i y| ≤ b*W := by
    obtain ⟨lam,hlamA,hlamB,hfirst,hsecond⟩ := d.intrinsic_boundary_jet_data hα j hy (hbar α hα t ht j hp hMA)
    have hfirsti := congrArg (fun L : CoordinateSpace n →L[ℝ] ℝ => L (Pi.single i 1)) hfirst
    change intrinsicDerivative d.coordinate_body_convex α j.1 i y = lam*coordinateDerivative i d.coordinateDefining y at hfirsti
    rw [hfirsti,abs_mul,abs_of_nonneg (ha.le.trans hlamA)]
    exact mul_le_mul hlamB (hDw y (d.coordinate_body_compact.isClosed.frontier_subset hy) i) (abs_nonneg _) hb.le
  have hLb (y : CoordinateSpace n) (hy : y ∈ interior {z | d.coordinateDefining z ≤ 0}) :
      c₀ ≤ linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 y)⁻¹ d.coordinateDefining y := by
    have hdet : (intrinsicHessian d.coordinate_body_convex α j.1 y).det ≤ D := by
      rw [hMA y hy]
      exact (hdens t ht y (interior_subset hy)).2
    have htr := trace_inverse_lower_of_det_upper (hp y hy) hdet
    have hlo : 1/max 1 D ≤ (intrinsicHessian d.coordinate_body_convex α j.1 y)⁻¹.trace :=
      (div_le_iff₀ hmax).mpr (by simpa only [mul_comm] using htr)
    have hh := (mul_le_mul_of_nonneg_left hlo d.modulus_pos.le).trans
      (linearizedMA_lower_of_hessian_lower (hp y hy).inv.posSemidef (d.coordinate_hessian_sub_modulus_posSemidef y))
    simpa only [c₀,mul_one_div] using hh
  have hfield := classical_dirichlet_abs_bound_with_barrier d.coordinate_body_compact
    (continuousOn_intrinsicDerivative d.coordinate_body_convex α j.1 i) d.coordinateDefining_smooth.continuous.continuousOn
    (fun y hy => contDiffAt_infty.mp (contDiffAt_intrinsicDerivative d.coordinate_body_convex hα j.1 hs hy i) 2)
    (fun _ _ => (contDiff_infty.mp d.coordinateDefining_smooth 2).contDiffAt)
    (fun y hy => (hp y hy).inv) hK hc₀
    (fun y hy => by
      rw [intrinsic_linearized_first_identity d.coordinate_body_convex hα j.1 hs hMAlog hy]
      exact hKF t ht y (interior_subset hy) i)
    hLb hbd (fun y hy => (d.coordinate_zero_boundary y hy).le) x hx
  have hv := hwW x hx
  dsimp only [C] at *
  nlinarith [neg_abs_le (d.coordinateDefining x)]


theorem intrinsic_tangent_block_bounds_all_exponents {a b : ℝ} (ha : 0 < a)
    (p : BoundaryChartPatch d.coordinateDefining) :
    ∃ δ I T : ℝ, 0 < δ ∧ 0 < I ∧ 0 < T ∧
      ∀ (α : ℝ), 0 < α → ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ∀ x ∈ Metric.closedBall p.center p.radius, d.coordinateDefining x = 0 →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0},
        b*d.coordinateDefining y ≤ intrinsicValue d.coordinate_body_convex α j.1 y ∧
        intrinsicValue d.coordinate_body_convex α j.1 y ≤ a*d.coordinateDefining y) →
      let B := coordinateTangentBlock (intrinsicHessian d.coordinate_body_convex α j.1 x) p.index
        (fun l => boundaryChartCoefficient d.coordinateDefining p.index l x)
      B.PosDef ∧ δ ≤ B.det ∧ (∀ i l, |B⁻¹ i l| ≤ I) ∧ (∀ i l, |B i l| ≤ T) := by
  obtain ⟨δ,I,hδ,hI,hInv⟩ := d.scaled_coordinate_tangent_block_bounds p (b := b) ha
  obtain ⟨T,hT,hentry⟩ := d.scaled_coordinate_tangent_block_entry_bound p a b
  refine ⟨δ,I,T,hδ,hI,hT,?_⟩
  intro α hα j x hxp hx0 hbar
  obtain ⟨lam,hla,hlb,he⟩ := d.intrinsic_tangent_block_eq_scalar_defining hα j p hxp hx0 hbar
  dsimp only
  rw [he]
  exact ⟨(chartTangentBlock_posDef (d.coordinateDefining_hessian_posDef x) p.index).smul (ha.trans_le hla),
    (hInv x hxp lam ⟨hla,hlb⟩).1,(hInv x hxp lam ⟨hla,hlb⟩).2,hentry x hxp lam ⟨hla,hlb⟩⟩


theorem intrinsic_uniform_boundary_hessian_on_chart_all_exponents [NeZero n] {a b G K D W : ℝ}
    (ha : 0 < a) (hG : 0 ≤ G) (hK : 0 ≤ K) (hD : 0 ≤ D) (hW : 0 ≤ W)
    (p : BoundaryChartPatch d.coordinateDefining)
    (hWw : ∀ y ∈ {x | d.coordinateDefining x ≤ 0}, ∀ i, |coordinateDerivative i d.coordinateDefining y| ≤ W) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (α : ℝ), 0 < α → ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ∀ F : CoordinateSpace n → ℝ,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {x | d.coordinateDefining x ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ interior {x | d.coordinateDefining x ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = Real.exp (F y)) →
      (∀ y ∈ {x | d.coordinateDefining x ≤ 0},
        b*d.coordinateDefining y ≤ intrinsicValue d.coordinate_body_convex α j.1 y ∧
        intrinsicValue d.coordinate_body_convex α j.1 y ≤ a*d.coordinateDefining y) →
      (∀ y ∈ {x | d.coordinateDefining x ≤ 0}, ∀ i, |intrinsicDerivative d.coordinate_body_convex α j.1 i y| ≤ G) →
      (∀ y ∈ interior {x | d.coordinateDefining x ≤ 0}, ∀ i, |coordinateDerivative i F y| ≤ K) →
      (∀ y ∈ {x | d.coordinateDefining x ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det ≤ D) →
      ∀ z ∈ frontier {x | d.coordinateDefining x ≤ 0}, z ∈ Metric.ball p.center (p.radius/2) →
        ∀ i l, |intrinsicHessian d.coordinate_body_convex α j.1 z i l| ≤ B := by
  obtain ⟨δ,I,T,hδ,hI,hT,hblock⟩ := d.intrinsic_tangent_block_bounds_all_exponents (b := b) ha p
  let M := ((((1+p.bound₀)*G)/(p.radius^2/8)+
    ((K+p.bound₀*K+2*p.bound₁)*max 1 D+G*(n:ℝ)^2*p.bound₂))/d.modulus)*W+p.bound₁*G
  let N := D/δ+(Fintype.card (TangentIndex p.index):ℝ)^2*I*M^2
  let B := (n:ℝ)*max N (T+2*p.bound₀*M+p.bound₀^2*N)
  have hM : 0 ≤ M := by
    have h0 := p.bound₀_nonneg
    have h1 := p.bound₁_nonneg
    have h2 := p.bound₂_nonneg
    have hκ := d.modulus_pos
    have hr := p.radius_pos
    have hm : 0 ≤ max 1 D := zero_le_one.trans (le_max_left _ _)
    dsimp [M]
    positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨B,mul_nonneg (Nat.cast_nonneg _) (hN.trans (le_max_left _ _)),?_⟩
  intro α hα j F hs hp hMA hbar hGu hKF hdet z hzb hz i l
  have hz0 := d.coordinate_zero_boundary z hzb
  have hzS := d.coordinate_body_compact.isClosed.frontier_subset hzb
  have hzchart : z ∈ Metric.closedBall p.center p.radius := by
    change dist z p.center ≤ p.radius
    exact hz.le.trans (by linarith [p.radius_pos])
  have hmixed (a : Fin n) : |intrinsicHessian d.coordinate_body_convex α j.1 z a p.index-
      boundaryChartCoefficient d.coordinateDefining p.index a z*intrinsicHessian d.coordinate_body_convex α j.1 z p.index p.index| ≤ M :=
    d.intrinsic_mixed_hessian_on_chart hα p j hs (fun y hy => hp y (interior_subset hy)) hMA hbar
      hG hK hW hGu hKF (fun y hy => hdet y (interior_subset hy)) hWw hz0 hz a
  have ht := hblock α hα j z hzchart hz0 hbar
  have hsym : (intrinsicHessian d.coordinate_body_convex α j.1 z).IsSymm := by
    simpa only [Matrix.IsHermitian,Matrix.IsSymm,Matrix.conjTranspose_eq_transpose_of_trivial] using (hp z hzS).isHermitian
  have hn : intrinsicHessian d.coordinate_body_convex α j.1 z p.index p.index ≤ N :=
    coordinate_normal_hessian_bound hsym p.index (fun a => boundaryChartCoefficient d.coordinateDefining p.index a z)
      ht.1 hδ hI.le hM hD ht.2.1 ht.2.2.1 (fun a => hmixed a) (hdet z hzS)
  exact coordinate_hessian_entries_bound_of_adapted_bounds (hp z hzS).posSemidef p.index
    (fun a => boundaryChartCoefficient d.coordinateDefining p.index a z) p.bound₀_nonneg hM hN
    (fun a => ht.2.2.2 a a) (fun a => p.value_bound z hzchart a) (fun a => hmixed a) hn i l


theorem intrinsic_dirichletContinuation_uniform_boundary_hessian_all_exponents [NeZero n] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (α : ℝ), 0 < α → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ x ∈ {y | d.coordinateDefining y ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 x).PosDef) →
      (∀ x ∈ {y | d.coordinateDefining y ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 x).det = dirichletContinuationDensity d.coordinateDefining t x) →
      ∀ x ∈ frontier {y | d.coordinateDefining y ≤ 0}, ∀ i l, |intrinsicHessian d.coordinate_body_convex α j.1 x i l| ≤ B := by
  classical
  obtain ⟨a,b,ha,hb,hbar⟩ := d.intrinsic_dirichletContinuation_scaled_barriers_all_exponents
  obtain ⟨G,hG,hgrad⟩ := d.intrinsic_dirichletContinuation_uniform_first_all_exponents
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K,hK,hKF⟩ := dirichletContinuationDensity_uniform_log_coordinateDerivative d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨W,hW,hwW,hDw⟩ := d.coordinate_defining_first_bounds
  have hcharts := fun p : BoundaryChartPatch d.coordinateDefining =>
    d.intrinsic_uniform_boundary_hessian_on_chart_all_exponents (b := b) ha hG hK hD.le hW p hDw
  choose B hB hbound using hcharts
  obtain ⟨P,hcover⟩ := d.exists_finite_coordinate_boundary_atlas
  refine ⟨∑ p ∈ P, B p,Finset.sum_nonneg (fun p _ => hB p),?_⟩
  intro α hα t ht j hs hp hMA x hx i l
  obtain ⟨p,hpP,hxp⟩ := mem_iUnion₂.mp (hcover hx)
  have hpint := fun y hy => hp y (interior_subset hy)
  have hMAint := fun y hy => hMA y (interior_subset hy)
  have hMAlog : ∀ y ∈ interior {z | d.coordinateDefining z ≤ 0},
      (intrinsicHessian d.coordinate_body_convex α j.1 y).det = Real.exp (Real.log (dirichletContinuationDensity d.coordinateDefining t y)) := by
    intro y hy
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
    exact hMAint y hy
  have hh := hbound p α hα j (fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)) hs hp hMAlog
    (hbar α hα t ht j hpint hMAint) (hgrad α hα t ht j hs hpint hMAint)
    (fun y hy => hKF t ht y (interior_subset hy))
    (fun y hy => (hMA y hy).trans_le (hdens t ht y hy).2) x hx hxp i l
  exact hh.trans (Finset.single_le_sum (fun p _ => hB p) hpP)


theorem intrinsic_dirichletContinuation_uniform_hessian_all_exponents [NeZero n] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (α : ℝ), 0 < α → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ x ∈ {y | d.coordinateDefining y ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 x).PosDef) →
      (∀ x ∈ {y | d.coordinateDefining y ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 x).det = dirichletContinuationDensity d.coordinateDefining t x) →
      ∀ x ∈ {y | d.coordinateDefining y ≤ 0}, ∀ i l, |intrinsicHessian d.coordinate_body_convex α j.1 x i l| ≤ B := by
  obtain ⟨B₀,hB₀,hboundary⟩ := d.intrinsic_dirichletContinuation_uniform_boundary_hessian_all_exponents
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K,hK,hKF⟩ := dirichletContinuationDensity_uniform_log_hessian d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨W,hW,hwW,hDw⟩ := d.coordinate_defining_first_bounds
  let c₀ := d.modulus/max 1 D
  have hmax : 0 < max 1 D := zero_lt_one.trans_le (le_max_left _ _)
  have hc₀ : 0 < c₀ := div_pos d.modulus_pos hmax
  let C := K/c₀
  have hC : 0 ≤ C := div_nonneg hK hc₀.le
  refine ⟨(n:ℝ)*(B₀+C*W),mul_nonneg (Nat.cast_nonneg _) (add_nonneg hB₀ (mul_nonneg hC hW)),?_⟩
  intro α hα t ht j hs hp hMA x hx i l
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.log _ (fun y => (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y)).ne')
    exact (contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp (contDiff_const.prodMk contDiff_id)
  have hMAlog (y : CoordinateSpace n) (hy : y ∈ interior {z | d.coordinateDefining z ≤ 0}) :
      (intrinsicHessian d.coordinate_body_convex α j.1 y).det = Real.exp (F y) := by
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
    exact hMA y (interior_subset hy)
  have hLb (y : CoordinateSpace n) (hy : y ∈ interior {z | d.coordinateDefining z ≤ 0}) :
      c₀ ≤ linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 y)⁻¹ d.coordinateDefining y := by
    have hdet := (hMA y (interior_subset hy)).trans_le (hdens t ht y (interior_subset hy)).2
    have htr := trace_inverse_lower_of_det_upper (hp y (interior_subset hy)) hdet
    have hlo : 1/max 1 D ≤ (intrinsicHessian d.coordinate_body_convex α j.1 y)⁻¹.trace :=
      (div_le_iff₀ hmax).mpr (by simpa only [mul_comm] using htr)
    have hh := (mul_le_mul_of_nonneg_left hlo d.modulus_pos.le).trans
      (linearizedMA_lower_of_hessian_lower (hp y (interior_subset hy)).inv.posSemidef (d.coordinate_hessian_sub_modulus_posSemidef y))
    simpa only [c₀,mul_one_div] using hh
  have hdiag (a : Fin n) : intrinsicHessian d.coordinate_body_convex α j.1 x a a ≤ B₀+C*W := by
    have hb := classical_dirichlet_upper_bound_with_barrier d.coordinate_body_compact
      (continuousOn_intrinsicHessian_entry d.coordinate_body_convex α j.1 a a)
      d.coordinateDefining_smooth.continuous.continuousOn
      (fun y hy => contDiffAt_infty.mp (contDiffAt_intrinsicHessian_entry d.coordinate_body_convex hα j.1 hs hy a a) 2)
      (fun _ _ => (contDiff_infty.mp d.coordinateDefining_smooth 2).contDiffAt)
      (fun y hy => (hp y (interior_subset hy)).inv) hK hc₀
      (fun y hy => ((abs_le.mp (hKF t ht y (interior_subset hy) a a)).1).trans
        (intrinsic_linearized_hessian_diagonal_lower d.coordinate_body_convex hα j.1 hs hF hMAlog hy
          (hp y (interior_subset hy)) a)) hLb
      (fun y hy => (le_abs_self _).trans (hboundary α hα t ht j hs hp hMA y hy a a))
      (fun y hy => (d.coordinate_zero_boundary y hy).le) x hx
    have hv := hwW x hx
    dsimp only [C] at *
    nlinarith [neg_abs_le (d.coordinateDefining x)]
  apply (abs_matrix_entry_le_trace (hp x hx).posSemidef i l).trans
  calc
    (intrinsicHessian d.coordinate_body_convex α j.1 x).trace ≤ ∑ _a : Fin n, (B₀+C*W) :=
      Finset.sum_le_sum (fun a _ => hdiag a)
    _ = _ := by simp; ring


end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
