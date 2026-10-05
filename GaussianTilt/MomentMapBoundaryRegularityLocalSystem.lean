import GaussianTilt.MomentMapBoundaryRegularityCoreHarnack
import GaussianTilt.MomentMapRegularityReferenceExtension

/-! # Genuine interior smoothness and closed-half-ball continuity -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff Manifold
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def flatClosedHalfBall (j : Fin n) : Set (CoordinateSpace n) :=
  {x | ‖(coordinateEquiv n).symm x‖ ≤ 1 ∧ 0 ≤ x j}

lemma isOpen_flatHalfBall (j : Fin n) : IsOpen (flatHalfBall j) :=
  (isOpen_lt (coordinateEquiv n).symm.continuous.norm continuous_const).inter
    (isOpen_lt continuous_const (continuous_apply j))

lemma flatHalfBall_subset_closed (j : Fin n) : flatHalfBall j ⊆ flatClosedHalfBall j :=
  fun _ hx => ⟨hx.1.le,hx.2.le⟩

/-- This system assumes no regularity outside the domain or across its boundary. -/
structure LocalFlatEllipticSystem (j : Fin n) (u f : CoordinateSpace n → ℝ)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (lam Λ K M : ℝ) : Prop where
  continuous_boundary : ContinuousOn u (flatClosedHalfBall j)
  smooth_interior : ContDiffOn ℝ ∞ u (flatHalfBall j)
  forcing_smooth : ContDiffOn ℝ ∞ f (flatHalfBall j)
  coefficient_smooth : ∀ i k, ContDiffOn ℝ ∞ (fun y => A y i k) (flatHalfBall j)
  positive : ∀ y ∈ flatHalfBall j, (A y).PosDef
  elliptic : ∀ y ∈ flatHalfBall j, ∀ w : CoordinateSpace n,
    lam*‖(coordinateEquiv n).symm w‖^2 ≤ w ⬝ᵥ (A y *ᵥ w) ∧
    w ⬝ᵥ (A y *ᵥ w) ≤ Λ*‖(coordinateEquiv n).symm w‖^2
  coefficient_bound : ∀ y ∈ flatHalfBall j, ∀ k a b,
    y j*|matrixCoordinateDerivative A k y a b| ≤ K
  forcing_bound : ∀ y ∈ flatHalfBall j, |f y| ≤ M
  forcing_derivative_bound : ∀ y ∈ flatHalfBall j, ∀ k,
    y j*|coordinateDerivative k f y| ≤ M
  equation : ∀ y ∈ flatHalfBall j, linearizedMA (A y) u y = f y

theorem exists_global_smooth_eq_near_compact_coordinate {u : CoordinateSpace n → ℝ}
    {U S : Set (CoordinateSpace n)} (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ v : CoordinateSpace n → ℝ, ContDiff ℝ ∞ v ∧ ∀ x ∈ S, v =ᶠ[𝓝 x] u := by
  obtain ⟨χ,hχ0,hχ1,_⟩ := exists_smooth_zero_one_nhds_of_isClosed
    𝓘(ℝ, CoordinateSpace n) hU.isClosed_compl hS.isClosed
    (disjoint_left.mpr (fun x hxU hxS => hxU (hSU hxS)))
  let v := fun x => χ x*u x
  have hχ : ContDiff ℝ ∞ (χ : CoordinateSpace n → ℝ) := χ.contMDiff.contDiff
  have hv : ContDiff ℝ ∞ v := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds hx))
    · have hzero : ∀ᶠ y in 𝓝 x, χ y=0 := hχ0.filter_mono (nhds_le_nhdsSet hx)
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [hzero] with y hy
      change χ y*u y=0
      rw [hy,zero_mul]
  refine ⟨v,hv,?_⟩
  intro x hx
  have hone : ∀ᶠ y in 𝓝 x, χ y=1 := hχ1.filter_mono (nhds_le_nhdsSet hx)
  filter_upwards [hone] with y hy
  change χ y*u y=u y
  rw [hy,one_mul]

def flatCompactInteriorStrip (j : Fin n) : Set (CoordinateSpace n) :=
  {x | ‖(coordinateEquiv n).symm x‖ ≤ 3/4 ∧ 1/64 ≤ x j}

lemma isCompact_flatCompactInteriorStrip (j : Fin n) : IsCompact (flatCompactInteriorStrip j) := by
  have he : flatCompactInteriorStrip j =
      ((coordinateEquiv n) '' Metric.closedBall (0:E n) (3/4)) ∩ {x | 1/64 ≤ x j} := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨(coordinateEquiv n).symm x,by simpa only [Metric.mem_closedBall,dist_zero_right] using hx.1,
        (coordinateEquiv n).apply_symm_apply x⟩,hx.2⟩
    · rintro ⟨⟨y,hy,rfl⟩,hj⟩
      exact ⟨by simpa only [ContinuousLinearEquiv.symm_apply_apply,Metric.mem_closedBall,dist_zero_right] using hy,hj⟩
  rw [he]
  exact ((isCompact_closedBall _ _).image (coordinateEquiv n).continuous).inter_right
    (isClosed_le continuous_const (continuous_apply j))

lemma flatCompactInteriorStrip_inside (j : Fin n) : flatCompactInteriorStrip j ⊆ flatHalfBall j := by
  intro x hx
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

lemma flatInteriorStrip_subset_compact (j : Fin n) : flatInteriorStrip j ⊆ flatCompactInteriorStrip j := by
  intro x hx
  exact ⟨hx.1.le,by linarith [hx.2]⟩

lemma flatInteriorCore_subset_compact (j : Fin n) : flatInteriorCore j ⊆ flatCompactInteriorStrip j := by
  intro x hx
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

end GaussianTilt.MomentMapRegularity
