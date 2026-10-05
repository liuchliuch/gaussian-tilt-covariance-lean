import GaussianTilt.MomentMapLinearDirichletTangentialDifferenceTranslation
import GaussianTilt.NegativeSobolevMollifierDistribution

/-! # Exact scalar differentiation of translated Sobolev core pairings -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal Convolution
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma inner_volumeTranslate_core_eq_integral
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (u : smoothCompactCore n) (a : CoordinateSpace n) :
    inner ℝ f (volumeTranslate a (smoothCompactToL2 volume u)) = ∫ x, f x*u.1 (x+a) := by
  rw [volumeTranslate_core,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [smoothCompactToL2_ae volume (translateSmoothCompactCore a u)] with x hx
  change inner ℝ (f x) (smoothCompactToL2 volume (translateSmoothCompactCore a u) x) = _
  rw [hx]
  simp only [RCLike.inner_apply,conj_trivial,translateSmoothCompactCore]
  ring

lemma inner_volumeTranslate_core_eq_convolution
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (u : smoothCompactCore n) (a : CoordinateSpace n) :
    inner ℝ f (volumeTranslate a (smoothCompactToL2 volume u)) = scalarConvolution u.1 (fun x => f (-x)) a := by
  rw [inner_volumeTranslate_core_eq_integral,scalarConvolution_flip_apply]
  have he := integral_neg_eq_self (fun x : CoordinateSpace n => f x*u.1 (x+a)) volume
  simpa only [neg_neg,sub_eq_add_neg,add_comm] using he.symm

/-- The translated pairing is differentiated by its actual compact kernel.
This is the starting classical statement before taking the H¹ closure. -/
theorem hasDerivAt_inner_volumeTranslate_core
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (u : smoothCompactCore n)
    (i : Fin n) (t : ℝ) :
    HasDerivAt (fun h : ℝ => inner ℝ f (volumeTranslate (h • (Pi.single i 1 : CoordinateSpace n)) (smoothCompactToL2 volume u)))
      (inner ℝ f (volumeTranslate (t • (Pi.single i 1 : CoordinateSpace n))
        (smoothCompactToL2 volume (smoothCompactDerivative i u)))) t := by
  let g : CoordinateSpace n → ℝ := fun x => f (-x)
  have hg : MemLp g 2 volume := (Lp.memLp f).comp_measurePreserving (Measure.measurePreserving_neg volume)
  have hconv : ContDiff ℝ ∞ (scalarConvolution u.1 g) :=
    u.2.2.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) u.2.1 (hg.locallyIntegrable (by norm_num))
  simp_rw [inner_volumeTranslate_core_eq_convolution]
  have hd := ((hconv.differentiable (by simp) (t • (Pi.single i 1 : CoordinateSpace n))).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const (Pi.single i 1 : CoordinateSpace n))
  have he : fderiv ℝ (scalarConvolution u.1 g) (t • (Pi.single i 1 : CoordinateSpace n)) (Pi.single i 1) =
      scalarConvolution (coordinateDerivative i u.1) g (t • (Pi.single i 1 : CoordinateSpace n)) :=
    congrFun (coordinateDerivative_scalarConvolution u.2.1 u.2.2 hg i) _
  simpa only [one_smul,he,Function.comp_def] using hd

end GaussianTilt.MomentMapLinearDirichlet
