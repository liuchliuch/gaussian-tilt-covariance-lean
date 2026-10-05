import GaussianTilt.MomentMapLinearDirichletTangentialDifferencePairing
import GaussianTilt.MomentMapLinearDirichletMarkov
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! # Actual L² difference quotients of H₀¹ jets

The derivative of translated pairings is first proved on the genuine
smooth core, then extended by uniform limits in the actual Hilbert closure.
The sharp quotient estimate and strong derivative limit follow from the
Hilbert norm identity, not from assumed Sobolev differentiation rules.
-/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma tendstoUniformly_inner_volumeTranslate
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    {u : ℕ → Lp ℝ 2 (volume : Measure (CoordinateSpace n))} {v : Lp ℝ 2 (volume : Measure (CoordinateSpace n))}
    (hu : Tendsto u atTop (𝓝 v)) :
    TendstoUniformly (fun k a => inner ℝ f (volumeTranslate a (u k))) (fun a => inner ℝ f (volumeTranslate a v)) atTop := by
  have ht : Tendsto (fun k => ‖f‖*‖u k-v‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_iff_norm_sub_tendsto_zero.mp hu).const_mul ‖f‖
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp ht).2 ε hε] with k hk a
  calc
    dist (inner ℝ f (volumeTranslate a v)) (inner ℝ f (volumeTranslate a (u k))) =
        |inner ℝ f (volumeTranslate a (v-u k))| := by rw [Real.dist_eq,map_sub,inner_sub_right]
    _ ≤ ‖f‖*‖volumeTranslate a (v-u k)‖ := abs_real_inner_le_norm _ _
    _ = ‖f‖*‖u k-v‖ := by rw [norm_volumeTranslate,norm_sub_rev]
    _ < ε := hk

/-- Actual weak derivative coordinates in the H¹ closure differentiate
all translated L² pairings, with a genuine classical scalar derivative. -/
theorem hasDerivAt_inner_volumeTranslate_dirichlet {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun h : ℝ => inner ℝ f (volumeTranslate (h • (Pi.single i 1 : CoordinateSpace n)) (dirichletValue Ω u)))
      (inner ℝ f (volumeTranslate (t • (Pi.single i 1 : CoordinateSpace n)) (u.1 i.succ))) t := by
  obtain ⟨v,hv⟩ := exists_dirichletCore_sequence u
  have hval : Tendsto (fun k => smoothCompactToL2 volume (v k).1) atTop (𝓝 (dirichletValue Ω u)) :=
    ((dirichletValue Ω).continuous.tendsto u).comp hv
  have hgrad : Tendsto (fun k => smoothCompactToL2 volume (smoothCompactDerivative i (v k).1))
      atTop (𝓝 (u.1 i.succ)) :=
    (((volumeJetDerivative i).comp (dirichletSobolev Ω).subtypeL).continuous.tendsto u).comp hv
  have hDu := (tendstoUniformly_inner_volumeTranslate f hgrad).comp
    (fun t : ℝ => t • (Pi.single i 1 : CoordinateSpace n))
  have hU := (tendstoUniformly_inner_volumeTranslate f hval).comp
    (fun t : ℝ => t • (Pi.single i 1 : CoordinateSpace n))
  exact hasDerivAt_of_tendstoUniformly hDu
    (Eventually.of_forall (fun k t => hasDerivAt_inner_volumeTranslate_core f (v k).1 i t))
    (fun t => hU.tendsto_at t) t

/-- The sharp translation increment bound is derived by scalar mean value
and testing against the actual Hilbert-space increment. -/
theorem norm_volumeTranslate_sub_le_dirichlet_derivative {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (i : Fin n) (h : ℝ) :
    ‖volumeTranslate (h • (Pi.single i 1 : CoordinateSpace n)) (dirichletValue Ω u)-dirichletValue Ω u‖ ≤
      |h| * ‖u.1 i.succ‖ := by
  let v := volumeTranslate (h • (Pi.single i 1 : CoordinateSpace n)) (dirichletValue Ω u)-dirichletValue Ω u
  have hb (t : ℝ) : ‖inner ℝ v (volumeTranslate (t • (Pi.single i 1 : CoordinateSpace n)) (u.1 i.succ))‖ ≤ ‖v‖*‖u.1 i.succ‖ := by
    simpa only [Real.norm_eq_abs,norm_volumeTranslate] using abs_real_inner_le_norm v
      (volumeTranslate (t • (Pi.single i 1 : CoordinateSpace n)) (u.1 i.succ))
  have hm := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_inner_volumeTranslate_dirichlet u v i t).hasDerivWithinAt)
    (fun t _ => hb t) (mem_univ 0) (mem_univ h)
  simp only [zero_smul,volumeTranslate_zero,sub_zero,← inner_sub_right] at hm
  change ‖inner ℝ v v‖ ≤ ‖v‖*‖u.1 i.succ‖*‖h‖ at hm
  rw [real_inner_self_eq_norm_sq,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),Real.norm_eq_abs] at hm
  change ‖v‖ ≤ |h| * ‖u.1 i.succ‖
  by_cases hv : ‖v‖=0
  · rw [hv]
    positivity
  · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    nlinarith

/-- The literal L² difference quotient. -/
def dirichletDifferenceQuotient {Ω : Set (CoordinateSpace n)} (u : dirichletSobolev Ω)
    (i : Fin n) (h : ℝ) : Lp ℝ 2 (volume : Measure (CoordinateSpace n)) :=
  h⁻¹ • (volumeTranslate (h • (Pi.single i 1 : CoordinateSpace n)) (dirichletValue Ω u)-dirichletValue Ω u)

theorem norm_dirichletDifferenceQuotient_le {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (i : Fin n) (h : ℝ) :
    ‖dirichletDifferenceQuotient u i h‖ ≤ ‖u.1 i.succ‖ := by
  by_cases hh : h=0
  · simp [dirichletDifferenceQuotient,hh]
  rw [dirichletDifferenceQuotient,norm_smul,Real.norm_eq_abs,abs_inv]
  calc
    _ ≤ |h|⁻¹*(|h| * ‖u.1 i.succ‖) := mul_le_mul_of_nonneg_left
      (norm_volumeTranslate_sub_le_dirichlet_derivative u i h) (inv_nonneg.mpr (abs_nonneg _))
    _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ (abs_ne_zero.mpr hh),one_mul]

/-- Actual strong L² convergence to the stored weak derivative follows
from the sharp norm estimate and the differentiated Hilbert pairing. -/
theorem dirichletDifferenceQuotient_tendsto {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (i : Fin n) :
    Tendsto (dirichletDifferenceQuotient u i) (𝓝[≠] (0:ℝ)) (𝓝 (u.1 i.succ)) := by
  have hp := (hasDerivAt_inner_volumeTranslate_dirichlet u (u.1 i.succ) i 0).tendsto_slope_zero
  have hi : Tendsto (fun h => inner ℝ (u.1 i.succ) (dirichletDifferenceQuotient u i h))
      (𝓝[≠] (0:ℝ)) (𝓝 (‖u.1 i.succ‖^2)) := by
    simpa only [zero_add,zero_smul,volumeTranslate_zero,dirichletDifferenceQuotient,
      real_inner_smul_right,inner_sub_right,smul_eq_mul,real_inner_self_eq_norm_sq] using hp
  have hs : Tendsto (fun h => ‖dirichletDifferenceQuotient u i h-u.1 i.succ‖^2) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    apply squeeze_zero (fun h => sq_nonneg _) (fun h => ?_)
      (show Tendsto (fun h => 2*‖u.1 i.succ‖^2-2*inner ℝ (u.1 i.succ) (dirichletDifferenceQuotient u i h))
        (𝓝[≠] (0:ℝ)) (𝓝 0) from by
        have ht := ((hi.const_mul 2).const_sub (2*‖u.1 i.succ‖^2))
        convert ht using 1 <;> ring)
    rw [norm_sub_sq_real,real_inner_comm (dirichletDifferenceQuotient u i h)]
    have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_dirichletDifferenceQuotient_le u i h) 2
    linarith
  have hn := hs.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end GaussianTilt.MomentMapLinearDirichlet
