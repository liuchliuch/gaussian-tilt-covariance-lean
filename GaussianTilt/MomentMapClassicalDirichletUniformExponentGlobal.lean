import GaussianTilt.MomentMapClassicalDirichletUniformExponentBoundary
import GaussianTilt.MomentMapBoundaryRegularityFiniteCover

/-! # A domain-only global Hessian Hölder exponent for every admissible jet -/
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ} {S A : Set (E n)}

/-- Index the actual solution family, including its variable input exponent.
The fields are literal jet positivity and the genuine homotopy equation. -/
structure IntrinsicHomotopySolution (d : SmoothInnerDomain S A) where
  exponent : ℝ
  exponent_pos : 0 < exponent
  exponent_lt_one : exponent < 1
  time : ℝ
  time_mem : time ∈ Icc (0:ℝ) 1
  jet : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex exponent
  positive : ∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex exponent jet.1 y).PosDef
  equation : ∀ y ∈ {z | d.coordinateDefining z ≤ 0},
    (intrinsicHessian d.coordinate_body_convex exponent jet.1 y).det = dirichletContinuationDensity d.coordinateDefining time y

lemma scaled_fderiv_coordinateUnpullback_bound
    {f : CoordinateSpace n → ℝ} {x : E n} (hf : DifferentiableAt ℝ f (coordinateEquiv n x))
    {r T : ℝ} (hr : 0 < r) (hT : 0 ≤ T)
    (hD : ∀ k, r*|coordinateDerivative k f (coordinateEquiv n x)| ≤ T) :
    r*‖fderiv ℝ (f ∘ (coordinateEquiv n)) x‖ ≤ (n:ℝ)*T*‖(coordinateEquiv n).toContinuousLinearMap‖ := by
  have hh : ‖fderiv ℝ f (coordinateEquiv n x)‖ ≤ (n:ℝ)*(T/r) :=
    norm_fderiv_le_of_coordinate_bound (div_nonneg hT hr.le)
      (fun k => (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hD k))
  rw [fderiv_comp _ hf (coordinateEquiv n).differentiableAt,(coordinateEquiv n).fderiv]
  apply (mul_le_mul_of_nonneg_left (((fderiv ℝ f (coordinateEquiv n x)).opNorm_comp_le _).trans
    (mul_le_mul_of_nonneg_right hh (norm_nonneg _))) hr.le).trans_eq
  field_simp

namespace SmoothInnerDomain
variable (d : SmoothInnerDomain S A)

lemma defining_zero_of_mem_frontier_body {x : E n} (hx : x ∈ frontier d.body) : d.defining x=0 := by
  have hle : d.defining x ≤ 0 := d.compact_sublevel.isClosed.frontier_subset hx
  have hn : x ∉ interior d.body := hx.2
  have hnot : ¬d.defining x<0 := by
    intro hlt
    apply hn
    rw [d.interior_body]
    exact hlt
  linarith

lemma coordinate_mem_body {x : E n} (hx : x ∈ d.body) :
    coordinateEquiv n x ∈ {y | d.coordinateDefining y ≤ 0} := by
  change d.defining ((coordinateEquiv n).symm (coordinateEquiv n x)) ≤ 0
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx

lemma coordinate_mem_interior_body {x : E n} (hx : x ∈ interior d.body) :
    coordinateEquiv n x ∈ interior {y | d.coordinateDefining y ≤ 0} := by
  rw [d.coordinate_body_interior]
  change d.defining ((coordinateEquiv n).symm (coordinateEquiv n x)) < 0
  rw [ContinuousLinearEquiv.symm_apply_apply]
  simpa only [d.interior_body] using hx

/-- One actual global Hölder exponent and constant work for the entire
solution family, before the input Banach-space exponent is chosen. The
finite chart cover and interior-distance gluing are both constructed. -/
theorem intrinsic_dirichletContinuation_global_hessian_holder_all_exponents [NeZero n] :
    ∃ γ C : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 ≤ C ∧
      ∀ (α : ℝ), 0 < α → α < 1 → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ x ∈ d.body, ∀ y ∈ d.body, ∀ i l,
      |intrinsicHessian d.coordinate_body_convex α j.1 (coordinateEquiv n x) i l-
        intrinsicHessian d.coordinate_body_convex α j.1 (coordinateEquiv n y) i l| ≤ C*(dist x y)^γ := by
  classical
  obtain ⟨K,hK,hHess⟩ := d.intrinsic_dirichletContinuation_uniform_hessian_all_exponents
  obtain ⟨T,hT,hThird⟩ := d.intrinsic_dirichletContinuation_scaled_third_bound_all_exponents
  let Γ := IntrinsicHomotopySolution d × Fin n × Fin n
  let f : Γ → E n → ℝ := fun g x => intrinsicHessian d.coordinate_body_convex g.1.exponent g.1.jet.1 (coordinateEquiv n x) g.2.1 g.2.2
  let D : Γ → E n → E n →L[ℝ] ℝ := fun g x => fderiv ℝ (f g) x
  have hsmooth (u : IntrinsicHomotopySolution d) := d.intrinsic_dirichletContinuation_interior_smooth
    u.exponent_pos u.exponent_lt_one u.time_mem u.jet u.positive u.equation
  have hfraw (g : Γ) (x : E n) (hx : x ∈ interior d.body) :
      ContDiffAt ℝ ∞ (fun y => intrinsicHessian d.coordinate_body_convex g.1.exponent g.1.jet.1 y g.2.1 g.2.2)
        (coordinateEquiv n x) :=
    contDiffAt_intrinsicHessian_entry d.coordinate_body_convex g.1.exponent_pos g.1.jet.1
      (hsmooth g.1) (d.coordinate_mem_interior_body hx) g.2.1 g.2.2
  have hf (g : Γ) (_ : True) (x : E n) (hx : x ∈ interior d.body) : HasFDerivAt (f g) (D g x) x :=
    (((hfraw g x hx).differentiableAt (by simp)).comp x (coordinateEquiv n).differentiableAt).hasFDerivAt
  have hD (g : Γ) (_ : True) (x : E n) (hx : x ∈ interior d.body) (r : ℝ)
      (hr : 0 < r) (hr1 : r ≤ 1) (hb : Metric.closedBall x r ⊆ interior d.body) :
      r*‖D g x‖ ≤ (n:ℝ)*T*‖(coordinateEquiv n).toContinuousLinearMap‖ := by
    apply scaled_fderiv_coordinateUnpullback_bound ((hfraw g x hx).differentiableAt (by simp)) hr hT
    intro k
    apply hThird g.1.exponent g.1.exponent_pos g.1.time g.1.time_mem g.1.jet (hsmooth g.1)
      g.1.positive g.1.equation (coordinateEquiv n x) r hr hr1 _ k g.2.1 g.2.2
    intro y hy
    have hyb : (coordinateEquiv n).symm y ∈ Metric.closedBall x r := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply,Metric.mem_closedBall,dist_eq_norm] using hy.le
    have hyi := d.coordinate_mem_interior_body (hb hyb)
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hyi
  have hbound (g : Γ) (_ : True) (x : E n) (hx : x ∈ d.body) : ‖f g x‖ ≤ K :=
    hHess g.1.exponent g.1.exponent_pos g.1.time g.1.time_mem g.1.jet (hsmooth g.1)
      g.1.positive g.1.equation (coordinateEquiv n x) (d.coordinate_mem_body hx) g.2.1 g.2.2
  have hlocal (a : E n) (ha : a ∈ frontier d.body) :
      ∃ r γ C : ℝ, 0 < r ∧ 0 < γ ∧ γ ≤ 1 ∧ 0 ≤ C ∧
        ∀ g : Γ, True → ∀ z ∈ frontier d.body, dist z a < r → ∀ x ∈ d.body, dist x z ≤ r →
          ‖f g x-f g z‖ ≤ C*(dist x z)^γ := by
    have ha0 : d.coordinateDefining (coordinateEquiv n a)=0 := by
      change d.defining ((coordinateEquiv n).symm (coordinateEquiv n a))=0
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact d.defining_zero_of_mem_frontier_body ha
    obtain ⟨p,hpa⟩ := exists_boundaryChartPatch d.coordinateDefining_smooth ha0 (d.coordinate_gradient_ne_zero ha0)
    let c : IntrinsicFixedChart d p := Classical.choice (d.exists_intrinsicFixedChart p)
    obtain ⟨γ,r,C,hγ,hγ1,hr,hr1,hrp,hC,happ⟩ := c.exists_intrinsic_hessian_boundary_approach_all_exponents
    have hcenter : d.physicalChartCenter p=a := by
      simp only [physicalChartCenter,hpa,ContinuousLinearEquiv.symm_apply_apply]
    refine ⟨r,γ,C,hr,hγ,hγ1,hC,?_⟩
    intro g _ z hz hza x hx hxz
    have hh := happ g.1.exponent g.1.exponent_pos g.1.exponent_lt_one g.1.time g.1.time_mem
      g.1.jet g.1.positive g.1.equation z (by simpa only [Metric.mem_ball,hcenter] using hza)
      (d.defining_zero_of_mem_frontier_body hz) x hx hxz g.2.1 g.2.2
    exact hh
  obtain ⟨γ,C,hγ,hγ1,hC,hall⟩ := uniform_holder_of_compact_boundary_charts_and_interior_bounds
    (fun _ : Γ => True) f D d.compact_sublevel (by positivity : 0 ≤ (n:ℝ)*T*‖(coordinateEquiv n).toContinuousLinearMap‖)
    hK hlocal hf hD hbound
  refine ⟨γ,C,hγ,hγ1,hC,?_⟩
  intro α hα hα1 t ht j hp hMA x hx y hy i l
  let u : IntrinsicHomotopySolution d := ⟨α,hα,hα1,t,ht,j,hp,hMA⟩
  exact hall (u,i,l) trivial x hx y hy

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
