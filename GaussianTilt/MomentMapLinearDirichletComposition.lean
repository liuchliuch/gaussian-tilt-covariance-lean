import GaussianTilt.MomentMapLinearDirichletSmoothAbs

/-!
# Actual smooth scalar contractions on Dirichlet core jets

Zero-preserving smooth contractions preserve the genuine domain test core
and contract its full H¹ jet norm. Their induced L² maps are the actual
Lipschitz composition maps. Dominated convergence handles the explicit
smooth approximations of absolute value.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

def composeSmoothCore {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hη0 : η 0 = 0)
    (u : smoothCompactCore n) : smoothCompactCore n :=
  ⟨η ∘ u.1, hη.comp u.2.1, u.2.2.comp_left hη0⟩

lemma tsupport_composeSmoothCore_subset {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hη0 : η 0 = 0) (u : smoothCompactCore n) :
    tsupport (composeSmoothCore hη hη0 u).1 ⊆ tsupport u.1 := by
  apply closure_mono
  intro x hx
  change η (u.1 x) ≠ 0 at hx
  change u.1 x ≠ 0
  intro he
  exact hx (by rw [he, hη0])

def composeDirichletCore {Ω : Set (CoordinateSpace n)} {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hη0 : η 0 = 0) (u : dirichletCore Ω) : dirichletCore Ω :=
  ⟨composeSmoothCore hη hη0 u.1, (tsupport_composeSmoothCore_subset hη hη0 u.1).trans u.2⟩

lemma smoothCompactToL2_compose {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hη0 : η 0 = 0) (hLip : LipschitzWith 1 η) (u : smoothCompactCore n) :
    smoothCompactToL2 volume (composeSmoothCore hη hη0 u) =
      hLip.compLp hη0 (smoothCompactToL2 volume u) := by
  apply Lp.ext
  filter_upwards [smoothCompactToL2_ae volume (composeSmoothCore hη hη0 u),
    hLip.coeFn_compLp hη0 (smoothCompactToL2 volume u), smoothCompactToL2_ae volume u] with x hx hy hz
  change smoothCompactToL2 volume (composeSmoothCore hη hη0 u) x = _
  rw [hx, hy]
  change η (u.1 x) = η (smoothCompactToL2 volume u x)
  rw [hz]

lemma norm_core_composition_derivative_le {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hη0 : η 0 = 0) (hLip : LipschitzWith 1 η) (u : smoothCompactCore n) (i : Fin n) :
    ‖smoothCompactToL2 volume (smoothCompactDerivative i (composeSmoothCore hη hη0 u))‖ ≤
      ‖smoothCompactToL2 volume (smoothCompactDerivative i u)‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [smoothCompactToL2_ae volume (smoothCompactDerivative i (composeSmoothCore hη hη0 u)),
    smoothCompactToL2_ae volume (smoothCompactDerivative i u)] with x hx hy
  rw [hx, hy]
  change ‖coordinateDerivative i (η ∘ u.1) x‖ ≤ ‖coordinateDerivative i u.1 x‖
  rw [coordinateDerivative_comp (hη.differentiable (by simp)) (u.2.1.differentiable (by simp)), norm_mul]
  have hd : ‖deriv η (u.1 x)‖ ≤ (1 : ℝ) := norm_deriv_le_of_lipschitz hLip
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hd (norm_nonneg (coordinateDerivative i u.1 x))

/-- Full jet norm contraction is proved before taking any Sobolev closure. -/
theorem norm_smoothCompactJet_compose_le {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hη0 : η 0 = 0) (hLip : LipschitzWith 1 η) (u : smoothCompactCore n) :
    ‖smoothCompactJet volume (composeSmoothCore hη hη0 u)‖ ≤ ‖smoothCompactJet volume u‖ := by
  have hv : ‖smoothCompactToL2 volume (composeSmoothCore hη hη0 u)‖ ≤ ‖smoothCompactToL2 volume u‖ := by
    rw [smoothCompactToL2_compose hη hη0 hLip]
    simpa only [NNReal.coe_one, one_mul] using hLip.norm_compLp_le hη0 (smoothCompactToL2 volume u)
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro j _
  refine Fin.cases ?_ (fun i => ?_) j
  · exact pow_le_pow_left₀ (norm_nonneg _) hv 2
  · exact pow_le_pow_left₀ (norm_nonneg _) (norm_core_composition_derivative_le hη hη0 hLip u i) 2

lemma norm_Lp_sq_eq_integral (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    ‖f‖ ^ 2 = ∫ x, f x ^ 2 := by
  simpa only [Lp.toLp_coeFn] using norm_toLp_sq_eq_integral (Lp.memLp f)

/-- Actual L² convergence of the explicit smooth absolute-value
compositions, including the singular level set f=0. -/
theorem smoothAbs_compLp_tendsto_abs (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    Tendsto (fun k : ℕ => (lipschitzWith_smoothAbs (absRegularizationScale_pos k)).compLp
      (smoothAbs_zero (absRegularizationScale_pos k)) f) atTop (𝓝 |f|) := by
  let η := fun k => smoothAbs (absRegularizationScale k)
  let F := fun k => (lipschitzWith_smoothAbs (absRegularizationScale_pos k)).compLp
    (smoothAbs_zero (absRegularizationScale_pos k)) f
  have hnorm (k : ℕ) : ‖F k - |f|‖ ^ 2 = ∫ x, (η k (f x) - |f x|) ^ 2 := by
    rw [norm_Lp_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (F k) |f|,
      (lipschitzWith_smoothAbs (absRegularizationScale_pos k)).coeFn_compLp
        (smoothAbs_zero (absRegularizationScale_pos k)) f, Lp.coeFn_abs f] with x hx hy hz
    change F k x = η k (f x) at hy
    simp only [hx, hz, Pi.sub_apply, hy]
  have hi : Integrable (fun x => f x ^ 2) := (Lp.memLp f).integrable_sq
  have ht : Tendsto (fun k : ℕ => ∫ x, (η k (f x) - |f x|) ^ 2) atTop (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (l := (atTop : Filter ℕ)) (μ := (volume : Measure (CoordinateSpace n)))
      (F := fun k x => (η k (f x) - |f x|) ^ 2) (f := fun _ => (0 : ℝ)) (fun x => f x ^ 2)
      (Eventually.of_forall (fun k =>
        ((((lipschitzWith_smoothAbs (absRegularizationScale_pos k)).continuous.comp_aestronglyMeasurable
          (Lp.memLp f).aestronglyMeasurable).sub (Lp.memLp f).aestronglyMeasurable.norm).pow 2)))
      (Eventually.of_forall (fun k => ae_of_all _ (fun x => ?_))) hi
      (ae_of_all _ (fun x => ?_))
    · simpa only [integral_zero] using hh
    · have hb := smoothAbs_bounds (absRegularizationScale_pos k) (f x)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      dsimp [η]
      nlinarith [sq_abs (f x)]
    · simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        ((smoothAbs_tendsto_abs (f x)).sub_const |f x|).pow 2
  have hs := ht.sqrt
  simp_rw [← hnorm, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hs

/-- The scalar contractions are uniformly Lipschitz on actual L², so the
same absolute-value limit survives a simultaneously varying L² argument. -/
theorem smoothAbs_compLp_tendsto_abs_of_tendsto
    {f : ℕ → Lp ℝ 2 (volume : Measure (CoordinateSpace n))}
    {g : Lp ℝ 2 (volume : Measure (CoordinateSpace n))} (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun k : ℕ => (lipschitzWith_smoothAbs (absRegularizationScale_pos k)).compLp
      (smoothAbs_zero (absRegularizationScale_pos k)) (f k)) atTop (𝓝 |g|) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h1 := tendsto_iff_norm_sub_tendsto_zero.mp hf
  have h2 := tendsto_iff_norm_sub_tendsto_zero.mp (smoothAbs_compLp_tendsto_abs g)
  apply squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
    (by simpa only [zero_add] using h1.add h2)
  let L := lipschitzWith_smoothAbs (absRegularizationScale_pos k)
  let z := smoothAbs_zero (absRegularizationScale_pos k)
  calc
    _ ≤ ‖L.compLp z (f k) - L.compLp z g‖ + ‖L.compLp z g - |g|‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖f k - g‖ + ‖L.compLp z g - |g|‖ := by
      apply add_le_add_right
      simpa only [NNReal.coe_one, one_mul] using L.norm_compLp_sub_le z (f k) g

end GaussianTilt.MomentMapLinearDirichlet
