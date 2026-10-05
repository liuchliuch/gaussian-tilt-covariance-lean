import GaussianTilt.MomentMapClassicalDirichletGeometryDomains

/-! # Genuine near-quadratic section geometry before C² regularity

Uniform value approximation and convexity force the whole actual sublevel
set to be round and compact. No source Hessian, regular section shape or
boundedness premise is used.
-/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma convex_sublevel_subset_ball_of_sphere_gap {u : E n → ℝ}
    (hc : ConvexOn ℝ univ u) {h r : ℝ} (hr : 0 < r) (hu0 : u 0 ≤ h)
    (hgap : ∀ y : E n, ‖y‖ = r → h < u y) :
    {x | u x ≤ h} ⊆ Metric.ball (0 : E n) r := by
  intro x hx
  rw [Metric.mem_ball,dist_zero_right]
  by_contra hn
  have hnorm : r ≤ ‖x‖ := not_lt.mp hn
  have hxn : 0 < ‖x‖ := hr.trans_le hnorm
  let t := r/‖x‖
  have ht : 0 < t := div_pos hr hxn
  have ht1 : t ≤ 1 := (div_le_one hxn).mpr hnorm
  have hc' := hc.2 (mem_univ (0 : E n)) (mem_univ x)
    (show 0 ≤ 1-t by linarith) ht.le (by ring : (1-t)+t=1)
  simp only [smul_zero,zero_add,smul_eq_mul] at hc'
  have hbound : u (t • x) ≤ h := by
    have h0 := mul_le_mul_of_nonneg_left hu0 (show 0 ≤ 1-t by linarith)
    have h1 := mul_le_mul_of_nonneg_left hx ht.le
    nlinarith
  have he : ‖t • x‖ = r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    exact div_mul_cancel₀ r hxn.ne'
  exact (hgap _ he).not_ge hbound

lemma compact_convex_sublevel_of_sphere_gap {u : E n → ℝ}
    (hu : Continuous u) (hc : ConvexOn ℝ univ u) {h r : ℝ} (hr : 0 < r)
    (hu0 : u 0 ≤ h) (hgap : ∀ y : E n, ‖y‖ = r → h < u y) :
    IsCompact {x | u x ≤ h} ∧ Convex ℝ {x | u x ≤ h} := by
  constructor
  · exact isCompact_of_isClosed_isBounded (isClosed_le hu continuous_const)
      (Metric.isBounded_ball.subset (convex_sublevel_subset_ball_of_sphere_gap hc hr hu0 hgap))
  · simpa only [mem_univ,true_and] using hc.convex_le h

/-- A genuinely near-quadratic potential has round actual sections at a
smaller scale, with relative radial error controlled by the value error. -/
theorem near_quadratic_section_ball_sandwich {u : E n → ℝ}
    (hc : ConvexOn ℝ univ u) (hu0 : u 0 = 0)
    {R ρ η ε : ℝ} (hρ : 0 < ρ) (hη : 0 < η) (hη1 : η < 1)
    (houter : ρ*(1+η) ≤ R) (hε : ε ≤ η*ρ^2/2)
    (happrox : ∀ x : E n, ‖x‖ ≤ R → |u x-‖x‖^2/2| ≤ ε) :
    Metric.closedBall (0 : E n) (ρ*(1-η)) ⊆ {x | u x ≤ ρ^2/2} ∧
      {x | u x ≤ ρ^2/2} ⊆ Metric.ball (0 : E n) (ρ*(1+η)) := by
  have hρ2 : 0 < ρ^2 := sq_pos_of_pos hρ
  have hin : 0 < ρ*(1-η) := mul_pos hρ (sub_pos.mpr hη1)
  have hout : 0 < ρ*(1+η) := mul_pos hρ (by linarith)
  constructor
  · intro x hx
    have hnorm : ‖x‖ ≤ ρ*(1-η) := by simpa using hx
    have hnormR : ‖x‖ ≤ R := hnorm.trans ((by nlinarith : ρ*(1-η) ≤ ρ*(1+η)).trans houter)
    have hsq : ‖x‖^2 ≤ (ρ*(1-η))^2 := (sq_le_sq₀ (norm_nonneg _) hin.le).mpr hnorm
    have hh := (abs_le.mp (happrox x hnormR)).2
    have hηsq : 0 ≤ η-η^2 := by nlinarith
    have hprod := mul_nonneg hρ2.le hηsq
    change u x ≤ ρ^2/2
    nlinarith
  · apply convex_sublevel_subset_ball_of_sphere_gap hc hout (by rw [hu0]; positivity)
    intro y hy
    have hh := (abs_le.mp (happrox y (hy.trans_le houter))).1
    rw [hy] at hh
    have hprod : 0 < η*ρ^2 := mul_pos hη hρ2
    nlinarith [sq_nonneg (ρ*η)]

/-- The whole smaller source section is actually compact, convex, contains
an interior ball and has the expected zero boundary after subtracting its
height. These are consequences of value approximation, before any source
second derivative has been constructed. -/
theorem near_quadratic_section_geometry {u : E n → ℝ}
    (hu : Continuous u) (hc : ConvexOn ℝ univ u) (hu0 : u 0 = 0)
    {R ρ η ε : ℝ} (hρ : 0 < ρ) (hη : 0 < η) (hη1 : η < 1)
    (houter : ρ*(1+η) ≤ R) (hε : ε ≤ η*ρ^2/2)
    (happrox : ∀ x : E n, ‖x‖ ≤ R → |u x-‖x‖^2/2| ≤ ε) :
    IsCompact {x | u x ≤ ρ^2/2} ∧ Convex ℝ {x | u x ≤ ρ^2/2} ∧
      Metric.closedBall (0 : E n) (ρ*(1-η)) ⊆ {x | u x ≤ ρ^2/2} ∧
      {x | u x ≤ ρ^2/2} ⊆ Metric.ball (0 : E n) (ρ*(1+η)) ∧
      ({x | u x ≤ ρ^2/2} : Set (E n)).Nonempty ∧
      ∀ x ∈ frontier {x | u x ≤ ρ^2/2}, u x-ρ^2/2 = 0 := by
  obtain ⟨hinner,hout⟩ := near_quadratic_section_ball_sandwich hc hu0 hρ hη hη1 houter hε happrox
  have hclosed : IsClosed {x | u x ≤ ρ^2/2} := isClosed_le hu continuous_const
  have hcompact : IsCompact {x | u x ≤ ρ^2/2} :=
    isCompact_of_isClosed_isBounded hclosed (Metric.isBounded_ball.subset hout)
  refine ⟨hcompact,by simpa only [mem_univ,true_and] using hc.convex_le (ρ^2/2),hinner,hout,
    ⟨0,by rw [mem_setOf_eq,hu0]; positivity⟩,?_⟩
  intro x hx
  have hle : u x ≤ ρ^2/2 := hclosed.frontier_subset hx
  have heq : u x = ρ^2/2 := by
    by_contra hn
    have hlt : u x < ρ^2/2 := lt_of_le_of_ne hle hn
    have hi : x ∈ interior {x | u x ≤ ρ^2/2} :=
      interior_maximal (fun y hy => show u y ≤ ρ^2/2 from le_of_lt hy)
        (isOpen_lt hu continuous_const) hlt
    exact hx.2 hi
  exact sub_eq_zero.mpr heq

end GaussianTilt.MomentMapRegularity
