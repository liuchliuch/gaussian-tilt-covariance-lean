import GaussianTilt.MomentMapLinearDirichletAmbientComparison

/-!
# Actual smooth barriers for the weak Dirichlet solution

A compact smooth function nonnegative on the domain supplies an ambient
nonnegative Sobolev barrier by taking its proved positive part. Local weak
integration by parts identifies its energy with the literal negative
Laplacian on the domain, so comparison requires only a pointwise forcing
bound, with no assumed admissibility or supersolution identity.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma tsupport_coordinateDerivative_subset (i : Fin n) (f : CoordinateSpace n → ℝ) :
    tsupport (coordinateDerivative i f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hnot
  exact hx (by simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hnot])

lemma euclideanLaplacian_zero_off_tsupport (f : CoordinateSpace n → ℝ)
    {x : CoordinateSpace n} (hx : x ∉ tsupport f) : euclideanLaplacian f x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : x ∉ tsupport (coordinateDerivative i f) :=
    fun hi => hx (tsupport_coordinateDerivative_subset i f hi)
  simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hi]

/-- Energy against interior tests depends only on actual local values. -/
theorem dirichletEnergy_eq_of_value_ae_eq_on {Ω U : Set (CoordinateSpace n)} (hΩU : Ω ⊆ U)
    (u v : dirichletSobolev U)
    (huv : ∀ᵐ x ∂volume, x ∈ Ω → dirichletValue U u x = dirichletValue U v x)
    (z : dirichletSobolev Ω) :
    dirichletEnergy U u (dirichletInclusion hΩU z) =
      dirichletEnergy U v (dirichletInclusion hΩU z) := by
  have hcore (g : dirichletCore Ω) :
      dirichletEnergy U u (dirichletInclusion hΩU (dirichletCoreToSobolev Ω g)) =
      dirichletEnergy U v (dirichletInclusion hΩU (dirichletCoreToSobolev Ω g)) := by
    simp only [dirichletEnergy_apply]
    change (∑ i, inner ℝ (u.1 i.succ) (smoothCompactToL2 volume (smoothCompactDerivative i g.1))) =
      (∑ i, inner ℝ (v.1 i.succ) (smoothCompactToL2 volume (smoothCompactDerivative i g.1)))
    rw [dirichletSobolev_laplacian_pairing, dirichletSobolev_laplacian_pairing]
    congr 1
    apply integral_congr_ae
    filter_upwards [huv] with x hx
    by_cases hxΩ : x ∈ Ω
    · rw [hx hxΩ]
    · rw [euclideanLaplacian_zero_off_tsupport g.1.1 (fun hh => hxΩ (g.2 hh))]
      simp only [mul_zero]
  obtain ⟨g, hg⟩ := exists_dirichletCore_sequence z
  have hi := (dirichletInclusion hΩU).continuous.continuousAt.tendsto.comp hg
  have h1 := (dirichletEnergy U u).continuous.continuousAt.tendsto.comp hi
  have h2 := (dirichletEnergy U v).continuous.continuousAt.tendsto.comp hi
  exact tendsto_nhds_unique (h1.congr' (Eventually.of_forall (fun k => hcore (g k)))) h2

def ambientSmoothCore (b : smoothCompactCore n) : dirichletSobolev (univ : Set (CoordinateSpace n)) :=
  dirichletCoreToSobolev univ ⟨b, subset_univ _⟩

lemma ambientSmoothCore_energy {Ω : Set (CoordinateSpace n)} (b : smoothCompactCore n)
    (z : dirichletSobolev Ω) :
    dirichletEnergy univ (ambientSmoothCore b) (dirichletInclusion (subset_univ Ω) z) =
      inner ℝ (-smoothCompactToL2 volume (laplaceCore b)) (dirichletValue Ω z) := by
  rw [dirichletEnergy_symm, dirichletEnergy_apply]
  change (∑ i, inner ℝ (z.1 i.succ) (smoothCompactToL2 volume (smoothCompactDerivative i b))) = _
  rw [dirichletSobolev_laplacian_pairing, inner_neg_left, real_inner_comm,
    inner_Lp_smoothCompactToL2]
  rfl

lemma inner_L2_le_of_ae_on {Ω : Set (CoordinateSpace n)} (hΩ : MeasurableSet Ω)
    (f g : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (hfg : ∀ᵐ x ∂volume, x ∈ Ω → f x ≤ g x)
    (z : dirichletSobolev Ω) (hz : 0 ≤ dirichletValue Ω z) :
    inner ℝ f (dirichletValue Ω z) ≤ inner ℝ g (dirichletValue Ω z) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_mono_ae (L2.integrable_inner _ _) (L2.integrable_inner _ _)
  filter_upwards [hfg, (Lp.coeFn_nonneg _).mpr hz, dirichletValue_ae_zero_outside hΩ z] with x hx hz0 hzout
  simp only [RCLike.inner_apply, conj_trivial]
  by_cases hxΩ : x ∈ Ω
  · exact mul_le_mul_of_nonneg_left (hx hxΩ) hz0
  · rw [hzout hxΩ, zero_mul, zero_mul]

/-- A literal compact smooth upper barrier bounds the actual weak
solution. Its positive part and local supersolution pairing are derived. -/
theorem weakDirichletLaplaceSolution_le_smooth_barrier {Ω : Set (CoordinateSpace n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (b : smoothCompactCore n)
    (hb : ∀ x ∈ Ω, 0 ≤ b.1 x)
    (hforce : ∀ᵐ x ∂volume, x ∈ Ω → f x ≤ -euclideanLaplacian b.1 x) :
    ∀ᵐ x ∂volume, x ∈ Ω →
      dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip f) x ≤ b.1 x := by
  let v := dirichletPositivePart (ambientSmoothCore b)
  have hvb : ∀ᵐ x ∂volume, x ∈ Ω → dirichletValue univ v x = b.1 x := by
    filter_upwards [dirichletPositivePart_ae (ambientSmoothCore b), smoothCompactToL2_ae volume b] with x hx hy hxΩ
    change dirichletValue univ v x = _
    rw [hx]
    change (smoothCompactToL2 volume b x + |smoothCompactToL2 volume b x|) / 2 = _
    rw [hy, abs_of_nonneg (hb x hxΩ)]
    ring
  have hvpair (z : dirichletSobolev Ω) :
      dirichletEnergy univ v (dirichletInclusion (subset_univ Ω) z) =
        inner ℝ (-smoothCompactToL2 volume (laplaceCore b)) (dirichletValue Ω z) := by
    rw [dirichletEnergy_eq_of_value_ae_eq_on (subset_univ Ω) v (ambientSmoothCore b) (by
      filter_upwards [hvb, smoothCompactToL2_ae volume b] with x hx hy hxΩ
      exact (hx hxΩ).trans hy.symm), ambientSmoothCore_energy]
  have hle := weakDirichletLaplaceSolution_le_ambient hΩ hΩb (subset_univ Ω) i hR hstrip f v
    (dirichletPositivePart_nonneg _) (by
      intro z hz
      rw [hvpair]
      apply inner_L2_le_of_ae_on hΩ.measurableSet _ _ _ z hz
      filter_upwards [hforce, Lp.coeFn_neg (smoothCompactToL2 volume (laplaceCore b)),
        smoothCompactToL2_ae volume (laplaceCore b)] with x hx hy hlap hxΩ
      rw [hy, Pi.neg_apply, hlap]
      exact hx hxΩ)
  filter_upwards [(Lp.coeFn_le _ _).mpr hle, hvb] with x hx hy hxΩ
  exact hx.trans_eq (hy hxΩ)

end GaussianTilt.MomentMapLinearDirichlet
