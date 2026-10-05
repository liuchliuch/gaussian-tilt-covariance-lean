import GaussianTilt.MomentMapBoundaryRegularityGluing

/-! # Uniform boundary approach from a genuine finite compact chart cover -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter Metric
open scoped Topology
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A compact boundary and locally uniform all-center chart estimates
produce one exponent, radius and constant for the entire family. The finite
cover and all minimum/maximum constants are constructed, not supplied. -/
theorem uniform_boundary_approach_of_compact_chart_cover
    {Γ : Type*} (P : Γ → Prop) (f : Γ → E n → F) {S Z : Set (E n)}
    (hZ : IsCompact Z)
    (hlocal : ∀ a ∈ Z, ∃ r α C : ℝ, 0 < r ∧ 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
      ∀ γ, P γ → ∀ z ∈ Z, dist z a < r → ∀ x ∈ S, dist x z ≤ r →
        ‖f γ x-f γ z‖ ≤ C*(dist x z)^α) :
    ∃ α r C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < r ∧ r ≤ 1 ∧ 0 ≤ C ∧
      ∀ γ, P γ → ∀ z ∈ Z, ∀ x ∈ S, dist x z ≤ r →
        ‖f γ x-f γ z‖ ≤ C*(dist x z)^α := by
  classical
  by_cases hZe : Z=∅
  · refine ⟨1,1,0,by norm_num,le_rfl,by norm_num,le_rfl,le_rfl,?_⟩
    intro γ hγ z hz
    simpa only [hZe,mem_empty_iff_false] using hz
  have hZn : Z.Nonempty := Set.nonempty_iff_ne_empty.mpr hZe
  choose r α C hr hα hα1 hC hest using fun a : Z => hlocal a a.property
  have hcover : Z ⊆ ⋃ a : Z, Metric.ball (a:E n) (r a) := by
    intro a ha
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,Metric.mem_ball_self (hr ⟨a,ha⟩)⟩
  obtain ⟨I,hI⟩ := hZ.elim_finite_subcover (fun a : Z => Metric.ball (a:E n) (r a))
    (fun _ => Metric.isOpen_ball) hcover
  have hIn : I.Nonempty := by
    obtain ⟨z,hz⟩ := hZn
    obtain ⟨a,ha,_⟩ := mem_iUnion₂.mp (hI hz)
    exact ⟨a,ha⟩
  let α₀ := I.inf' hIn α
  let r₀ := min 1 (I.inf' hIn r)
  let C₀ := I.sup' hIn C
  have hα₀ : 0 < α₀ := (Finset.lt_inf'_iff hIn).mpr (fun a _ => hα a)
  have hr₀ : 0 < r₀ := lt_min zero_lt_one ((Finset.lt_inf'_iff hIn).mpr (fun a _ => hr a))
  obtain ⟨a₀,ha₀⟩ := hIn
  have hα₀1 : α₀ ≤ 1 := (Finset.inf'_le α ha₀).trans (hα1 a₀)
  have hC₀ : 0 ≤ C₀ := (hC a₀).trans (Finset.le_sup' C ha₀)
  refine ⟨α₀,r₀,C₀,hα₀,hα₀1,hr₀,min_le_left _ _,hC₀,?_⟩
  intro γ hγ z hz x hx hxz
  obtain ⟨a,ha,hza⟩ := mem_iUnion₂.mp (hI hz)
  have hra : r₀ ≤ r a := (min_le_right _ _).trans (Finset.inf'_le r ha)
  have hαa : α₀ ≤ α a := Finset.inf'_le α ha
  have hCa : C a ≤ C₀ := Finset.le_sup' C ha
  have hh := hest a γ hγ z hz hza x hx (hxz.trans hra)
  have hd1 : dist x z ≤ 1 := hxz.trans (min_le_left _ _)
  have hp : (dist x z)^(α a) ≤ (dist x z)^α₀ := by
    by_cases he : x=z
    · subst z
      simp [Real.zero_rpow (hα a).ne',Real.zero_rpow hα₀.ne']
    · exact Real.rpow_le_rpow_of_exponent_ge (dist_pos.mpr he) hd1 hαa
  exact hh.trans (mul_le_mul hCa hp (Real.rpow_nonneg dist_nonneg _) hC₀)

/-- Uniform finite-chart boundary control plus the genuine interior ball
estimates gives a global fixed Hölder modulus for every function in the
family. No global boundary exponent or Lebesgue radius is an input. -/
theorem uniform_holder_of_compact_boundary_charts_and_interior_bounds [NeZero n]
    {Γ : Type*} (P : Γ → Prop) (f : Γ → E n → F)
    (D : Γ → E n → E n →L[ℝ] F) {S : Set (E n)} (hS : IsCompact S)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hlocal : ∀ a ∈ frontier S, ∃ r α C : ℝ, 0 < r ∧ 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
      ∀ γ, P γ → ∀ z ∈ frontier S, dist z a < r → ∀ x ∈ S, dist x z ≤ r →
        ‖f γ x-f γ z‖ ≤ C*(dist x z)^α)
    (hf : ∀ γ, P γ → ∀ z ∈ interior S, HasFDerivAt (f γ) (D γ z) z)
    (hD : ∀ γ, P γ → ∀ x ∈ interior S, ∀ r : ℝ, 0 < r → r ≤ 1 →
      Metric.closedBall x r ⊆ interior S → r*‖D γ x‖ ≤ K)
    (hbound : ∀ γ, P γ → ∀ z ∈ S, ‖f γ z‖ ≤ B) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
      ∀ γ, P γ → ∀ x ∈ S, ∀ y ∈ S, ‖f γ x-f γ y‖ ≤ C*(dist x y)^α := by
  have hFr : IsCompact (frontier S) := hS.of_isClosed_subset isClosed_frontier
    (by intro x hx; exact hS.isClosed.closure_eq ▸ (frontier_subset_closure hx))
  obtain ⟨α,r,L,hα,hα1,hr,hr1,hL,happroach⟩ :=
    uniform_boundary_approach_of_compact_chart_cover P f hFr hlocal
  let C := 2*B+2*max (Metric.diam S) 1*K+max L (2*B/r^α)*((2:ℝ)^α+(3:ℝ)^α)
  refine ⟨boundaryInteriorHolderExponent α,C,boundaryInteriorHolderExponent_pos hα,
    boundaryInteriorHolderExponent_le_one hα.le,by dsimp [C]; positivity,?_⟩
  intro γ hγ
  exact holder_of_local_boundary_approach_and_interior_ball_derivative hS hα hL hK hB hr
    (hf γ hγ) (hD γ hγ) (hbound γ hγ) (fun x hx z hz hxz => happroach γ hγ z hz x hx hxz)

end GaussianTilt.MomentMapRegularity
