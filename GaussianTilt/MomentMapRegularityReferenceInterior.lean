import GaussianTilt.MomentMapRegularityReferenceExtension
import GaussianTilt.MomentMapClassicalDirichletDomainComparison
import GaussianTilt.MomentMapRegularityConstantDensityMass

/-! # Interior-only smooth constant-density estimates

A trimmed positive-depth sublevel is compactly contained in the actual
smooth domain. A constructed cutoff extension agrees near that sublevel,
so the existing genuine Pogorelov--Calabi estimate applies without a global
smoothness or boundary extension assumption.
-/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff Gradient ENNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma subgradientImageOn_congr_eqOn {S B : Set (E n)} {u v : E n → ℝ}
    (he : EqOn u v S) (hBS : B ⊆ S) : subgradientImageOn S u B = subgradientImageOn S v B := by
  ext p
  constructor <;> rintro ⟨x,hx,hp⟩ <;> refine ⟨x,hx,?_⟩
  · intro y hy
    have hh := hp y hy
    rwa [he (hBS hx),he hy] at hh
  · intro y hy
    rw [he (hBS hx),he hy]
    exact hp y hy

lemma coordinateThirdDerivative_congr_nhds {f g : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (he : f =ᶠ[𝓝 x] g) (i j k : Fin n) :
    coordinateThirdDerivative f x i j k = coordinateThirdDerivative g x i j k := by
  have hH : (fun y => coordinateHessian f y i j) =ᶠ[𝓝 x] (fun y => coordinateHessian g y i j) := by
    filter_upwards [he.eventuallyEq_nhds] with y hy
    exact congrArg (fun H : Matrix (Fin n) (Fin n) ℝ => H i j) (coordinateHessian_congr_nhds hy)
  exact coordinateDerivative_congr_nhds hH k

lemma coordinateThirdDerivative_add_const (f : CoordinateSpace n → ℝ) (c : ℝ)
    (x : CoordinateSpace n) (i j k : Fin n) :
    coordinateThirdDerivative (fun y => f y+c) x i j k = coordinateThirdDerivative f x i j k := by
  unfold coordinateThirdDerivative
  simp only [coordinateHessian_add_const]

/-- The C³ a-priori estimate now requires smoothness only in the original
domain interior. Every other analytic input remains the natural equation,
convexity, zero boundary values, diameter, mass and positive depth. -/
theorem interior_smooth_constant_density_thirdDerivative_bound_at_depth [NeZero n]
    {u : E n → ℝ} (huc : Continuous u) {S : Set (E n)} (hS : IsCompact S)
    (hu : ContDiffOn ℝ ∞ u (interior S)) (hc : ConvexOn ℝ S u)
    (hb : ∀ y ∈ frontier S, u y = 0)
    (hH : ∀ y ∈ interior S, (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).PosDef)
    (hMA : ∀ y ∈ interior S, (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).det = 1)
    {D M δ : ℝ} (hD : 0 ≤ D) (hdiam : Metric.diam S ≤ D) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hmass : volume (subgradientImageOn S u (interior S)) ≤ ENNReal.ofReal M)
    {x : E n} (hx : x ∈ S) (hdepth : 4*δ ≤ -u x) (i j k : Fin n) :
    |coordinateThirdDerivative (coordinatePullback u) (coordinateEquiv n x) i j k| ≤
      calabiThirdDerivativeBound n (sectionInteriorHessianBound n D M δ)
        (sectionThirdDerivativeRadius n D M δ) := by
  let T := S ∩ {y | u y ≤ -δ}
  have hT : IsCompact T := hS.inter_right (isClosed_le huc continuous_const)
  have hTS : T ⊆ S := inter_subset_left
  have hTint : T ⊆ interior S := by
    intro y hy
    by_contra hnot
    have hh := hb y ⟨subset_closure hy.1,hnot⟩
    have hh' := hy.2
    change u y ≤ -δ at hh'
    rw [hh] at hh'
    linarith
  have hxT : x ∈ T := ⟨hx,by change u x ≤ -δ; linarith⟩
  have hTc : Convex ℝ T := hc.convex_le (-δ)
  obtain ⟨v,hv,hveq⟩ := exists_global_smooth_eq_near_compact isOpen_interior
    (hu.add contDiffOn_const) hT hTint
  have he (y : E n) (hy : y ∈ T) : v y = u y+δ := (hveq y hy).self_of_nhds
  have hvc : ConvexOn ℝ T v := by
    refine ⟨hTc,?_⟩
    intro y hy z hz a b ha hbb hab
    rw [he y hy,he z hz,he _ (hTc hy hz ha hbb hab)]
    have hh := hc.2 hy.1 hz.1 ha hbb hab
    simp only [smul_eq_mul] at hh ⊢
    have hδeq : a*δ+b*δ=δ := by rw [← add_mul,hab,one_mul]
    linarith
  have hvb : ∀ y ∈ frontier T, v y = 0 := by
    intro y hy
    have hyT := hT.isClosed.frontier_subset hy
    have hyle : u y ≤ -δ := hyT.2
    have hyeq : u y = -δ := by
      by_contra hne
      have hlt : u y < -δ := lt_of_le_of_ne hyle hne
      apply hy.2
      apply mem_interior.mpr
      refine ⟨interior S ∩ {z | u z < -δ},?_,?_,⟨hTint hyT,hlt⟩⟩
      · exact fun z hz => ⟨interior_subset hz.1,show u z ≤ -δ from le_of_lt hz.2⟩
      · exact isOpen_interior.inter (isOpen_lt huc continuous_const)
    rw [he y hyT,hyeq]
    ring
  have hraw (y : E n) (hy : y ∈ T) :
      coordinatePullback v =ᶠ[𝓝 (coordinateEquiv n y)] fun z => coordinatePullback u z+δ := by
    have ht : Tendsto (coordinateEquiv n).symm (𝓝 (coordinateEquiv n y)) (𝓝 y) := by
      simpa only [ContinuousAt,(coordinateEquiv n).symm_apply_apply] using
        (coordinateEquiv n).symm.continuous.continuousAt (x:=coordinateEquiv n y)
    exact (hveq y hy).comp_tendsto ht
  have hHv (y : E n) (hy : y ∈ interior T) :
      (coordinateHessian (coordinatePullback v) (coordinateEquiv n y)).PosDef := by
    rw [coordinateHessian_congr_nhds (hraw y (interior_subset hy)),coordinateHessian_add_const]
    exact hH y (hTint (interior_subset hy))
  have hMAv (y : E n) (hy : y ∈ interior T) :
      (coordinateHessian (coordinatePullback v) (coordinateEquiv n y)).det = 1 := by
    rw [coordinateHessian_congr_nhds (hraw y (interior_subset hy)),coordinateHessian_add_const]
    exact hMA y (hTint (interior_subset hy))
  have hmassv : volume (subgradientImageOn T v (interior T)) ≤ ENNReal.ofReal M := by
    rw [subgradientImageOn_congr_eqOn he interior_subset,subgradientImageOn_add_const,
      subgradientImageOn_restrict_compact_interior hS ⟨x,hx⟩ huc.continuousOn hc hT hTint Subset.rfl]
    exact (measure_mono (subgradientImageOn_mono S u (interior_subset.trans hTint))).trans hmass
  have hDv : Metric.diam T ≤ D := (Metric.diam_mono hTS hS.isBounded).trans hdiam
  have hdepthv : 3*δ ≤ -v x := by rw [he x hxT]; linarith
  have hh := smooth_constant_density_thirdDerivative_bound_at_depth hv hT hvc hvb hHv hMAv
    hD hDv hM hδ hmassv hxT hdepthv i j k
  rw [coordinateThirdDerivative_congr_nhds (hraw x hxT),coordinateThirdDerivative_add_const] at hh
  exact hh

/-- The corresponding interior-only second-derivative estimate. -/
theorem interior_smooth_constant_density_hessian_bound_at_depth [NeZero n]
    {u : E n → ℝ} (huc : Continuous u) {S : Set (E n)} (hS : IsCompact S)
    (hu : ContDiffOn ℝ ∞ u (interior S)) (hc : ConvexOn ℝ S u)
    (hb : ∀ y ∈ frontier S, u y = 0)
    (hH : ∀ y ∈ interior S, (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).PosDef)
    (hMA : ∀ y ∈ interior S, (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).det = 1)
    {D M δ : ℝ} (hD : 0 ≤ D) (hdiam : Metric.diam S ≤ D) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hmass : volume (subgradientImageOn S u (interior S)) ≤ ENNReal.ofReal M)
    {x : E n} (hx : x ∈ S) (hdepth : 3*δ ≤ -u x) (i j : Fin n) :
    |coordinateHessian (coordinatePullback u) (coordinateEquiv n x) i j| ≤
      sectionInteriorHessianBound n D M δ := by
  let T := S ∩ {y | u y ≤ -δ}
  have hT : IsCompact T := hS.inter_right (isClosed_le huc continuous_const)
  have hTS : T ⊆ S := inter_subset_left
  have hTint : T ⊆ interior S := by
    intro y hy
    by_contra hnot
    have hh := hb y ⟨subset_closure hy.1,hnot⟩
    have hh' := hy.2
    change u y ≤ -δ at hh'
    rw [hh] at hh'
    linarith
  have hxT : x ∈ T := ⟨hx,by change u x ≤ -δ; linarith⟩
  have hTc : Convex ℝ T := hc.convex_le (-δ)
  obtain ⟨v,hv,hveq⟩ := exists_global_smooth_eq_near_compact isOpen_interior
    (hu.add contDiffOn_const) hT hTint
  have he (y : E n) (hy : y ∈ T) : v y = u y+δ := (hveq y hy).self_of_nhds
  have hvc : ConvexOn ℝ T v := by
    refine ⟨hTc,?_⟩
    intro y hy z hz a b ha hbb hab
    rw [he y hy,he z hz,he _ (hTc hy hz ha hbb hab)]
    have hh := hc.2 hy.1 hz.1 ha hbb hab
    simp only [smul_eq_mul] at hh ⊢
    have hδeq : a*δ+b*δ=δ := by rw [← add_mul,hab,one_mul]
    linarith
  have hvb : ∀ y ∈ frontier T, v y = 0 := by
    intro y hy
    have hyT := hT.isClosed.frontier_subset hy
    have hyle : u y ≤ -δ := hyT.2
    have hyeq : u y = -δ := by
      by_contra hne
      have hlt : u y < -δ := lt_of_le_of_ne hyle hne
      apply hy.2
      apply mem_interior.mpr
      refine ⟨interior S ∩ {z | u z < -δ},?_,?_,⟨hTint hyT,hlt⟩⟩
      · exact fun z hz => ⟨interior_subset hz.1,show u z ≤ -δ from le_of_lt hz.2⟩
      · exact isOpen_interior.inter (isOpen_lt huc continuous_const)
    rw [he y hyT,hyeq]
    ring
  have hraw (y : E n) (hy : y ∈ T) :
      coordinatePullback v =ᶠ[𝓝 (coordinateEquiv n y)] fun z => coordinatePullback u z+δ := by
    have ht : Tendsto (coordinateEquiv n).symm (𝓝 (coordinateEquiv n y)) (𝓝 y) := by
      simpa only [ContinuousAt,(coordinateEquiv n).symm_apply_apply] using
        (coordinateEquiv n).symm.continuous.continuousAt (x:=coordinateEquiv n y)
    exact (hveq y hy).comp_tendsto ht
  have hHv (y : E n) (hy : y ∈ interior T) :
      (coordinateHessian (coordinatePullback v) (coordinateEquiv n y)).PosDef := by
    rw [coordinateHessian_congr_nhds (hraw y (interior_subset hy)),coordinateHessian_add_const]
    exact hH y (hTint (interior_subset hy))
  have hMAv (y : E n) (hy : y ∈ interior T) :
      (coordinateHessian (coordinatePullback v) (coordinateEquiv n y)).det = 1 := by
    rw [coordinateHessian_congr_nhds (hraw y (interior_subset hy)),coordinateHessian_add_const]
    exact hMA y (hTint (interior_subset hy))
  have hmassv : volume (subgradientImageOn T v (interior T)) ≤ ENNReal.ofReal M := by
    rw [subgradientImageOn_congr_eqOn he interior_subset,subgradientImageOn_add_const,
      subgradientImageOn_restrict_compact_interior hS ⟨x,hx⟩ huc.continuousOn hc hT hTint Subset.rfl]
    exact (measure_mono (subgradientImageOn_mono S u (interior_subset.trans hTint))).trans hmass
  have hDv : Metric.diam T ≤ D := (Metric.diam_mono hTS hS.isBounded).trans hdiam
  have hdepthv : 2*δ ≤ -v x := by rw [he x hxT]; linarith
  have hh := smooth_constant_density_hessian_bound_at_depth hv hT hvc hvb hHv hMAv
    hD hDv hM hδ hmassv hxT hdepthv i j
  rw [coordinateHessian_congr_nhds (hraw x hxT),coordinateHessian_add_const] at hh
  exact hh

end GaussianTilt.MomentMapRegularity
