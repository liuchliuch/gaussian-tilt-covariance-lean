import GaussianTilt.NegativeSobolevMollifierFamily
import GaussianTilt.EllipticRegularityDistribution

/-! # Actual mollification of the weak elliptic equation -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal Convolution
namespace GaussianTilt.Letwin

lemma scalarConvolution_comm {n : ℕ} (ρ f : CoordinateSpace n → ℝ) :
    scalarConvolution ρ f = scalarConvolution f ρ := by
  have hflip : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip =
      ContinuousLinearMap.lsmul ℝ ℝ := by
    ext a b
    simp [mul_comm]
  simpa only [scalarConvolution, hflip] using
    (convolution_flip (ContinuousLinearMap.lsmul ℝ ℝ) (f := ρ) (g := f) (μ := volume)).symm

lemma scalarConvolution_flip_apply {n : ℕ} (ρ f : CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    scalarConvolution ρ f x = ∫ y, f y * ρ (x-y) := by
  rw [scalarConvolution_comm]
  rfl

/-- Coordinate differentiation of actual convolution differentiates its
smooth compact kernel. -/
lemma coordinateDerivative_scalarConvolution_of_locallyIntegrable {n : ℕ} {ρ f : CoordinateSpace n → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hf : LocallyIntegrable f volume)
    (i : Fin n) :
    coordinateDerivative i (scalarConvolution ρ f) = scalarConvolution (coordinateDerivative i ρ) f := by
  rw [scalarConvolution_comm ρ f]
  funext x
  unfold coordinateDerivative
  change (fderiv ℝ (convolution f ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) (Pi.single i 1) = _
  rw [(hρc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    hf (contDiff_infty.mp hρ 1) x).fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ)
    hf (hρc.fderiv ℝ)
    ((contDiff_infty.mp hρ 1).continuous_fderiv le_rfl)]
  exact congrFun (scalarConvolution_comm f (coordinateDerivative i ρ)) x

lemma coordinateDerivative_scalarConvolution {n : ℕ} {ρ f : CoordinateSpace n → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hf : MemLp f 2 volume)
    (i : Fin n) :
    coordinateDerivative i (scalarConvolution ρ f) = scalarConvolution (coordinateDerivative i ρ) f :=
  coordinateDerivative_scalarConvolution_of_locallyIntegrable hρ hρc (hf.locallyIntegrable (by norm_num)) i

lemma coordinateDerivative_const_sub_comp {n : ℕ} {ρ : CoordinateSpace n → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (a : CoordinateSpace n) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => ρ (a-y)) x = -coordinateDerivative i ρ (a-x) := by
  unfold coordinateDerivative
  change (fderiv ℝ (ρ ∘ (fun y => a-y)) x) (Pi.single i 1) = _
  rw [(((hρ.differentiable (by simp) (a-x)).hasFDerivAt).comp x
    ((hasFDerivAt_const a x).sub (hasFDerivAt_id x))).fderiv]
  simp

lemma euclideanLaplacian_const_sub_comp {n : ℕ} {ρ : CoordinateSpace n → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (a x : CoordinateSpace n) :
    euclideanLaplacian (fun y => ρ (a-y)) x = euclideanLaplacian ρ (a-x) := by
  have hd (i : Fin n) : coordinateDerivative i (fun y => ρ (a-y)) =
      fun y => -coordinateDerivative i ρ (a-y) :=
    funext (coordinateDerivative_const_sub_comp hρ a i)
  simp only [euclideanLaplacian, hd, coordinateDerivative_neg,
    coordinateDerivative_const_sub_comp (smooth_coordinateDerivative hρ _) a, neg_neg]

lemma euclideanLaplacian_scalarConvolution {n : ℕ} {ρ f : CoordinateSpace n → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hf : MemLp f 2 volume)
    (x : CoordinateSpace n) :
    euclideanLaplacian (scalarConvolution ρ f) x = scalarConvolution (euclideanLaplacian ρ) f x := by
  have hi (i : Fin n) : Integrable (fun y => f y *
      coordinateDerivative i (coordinateDerivative i ρ) (x-y)) volume :=
    ((hρc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ) (hf.locallyIntegrable (by norm_num))
      (smooth_coordinateDerivative (smooth_coordinateDerivative hρ i) i).continuous x
  simp only [euclideanLaplacian, coordinateDerivative_scalarConvolution hρ hρc hf,
    coordinateDerivative_scalarConvolution (smooth_coordinateDerivative hρ _)
      (hρc.fderiv_apply (𝕜 := ℝ) (Pi.single _ 1)) hf,
    scalarConvolution_flip_apply, Finset.mul_sum]
  exact (integral_finset_sum _ (fun i _ => hi i)).symm

/-- Testing the original distribution against a translated kernel proves
the ordinary pointwise PDE for the mollified functions. -/
theorem HasDistributionLaplacian.scalarConvolution_pointwise {n : ℕ}
    {ρ f g : CoordinateSpace n → ℝ} {F : Fin n → CoordinateSpace n → ℝ}
    (heq : HasDistributionLaplacian f F g)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hf : MemLp f 2 volume) (hF : ∀ i, MemLp (F i) 2 volume) (hg : MemLp g 2 volume)
    (x : CoordinateSpace n) :
    euclideanLaplacian (scalarConvolution ρ f) x =
      (∑ i, coordinateDerivative i (scalarConvolution ρ (F i)) x) + scalarConvolution ρ g x := by
  have hψ : ContDiff ℝ ∞ (fun y => ρ (x-y)) := hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun y => ρ (x-y)) :=
    hρc.comp_homeomorph (Homeomorph.subLeft x)
  have ht := heq (fun y => ρ (x-y)) hψ hψc
  have hA : Integrable (fun y => f y * euclideanLaplacian ρ (x-y)) volume :=
    (euclideanLaplacian_compact hρc).convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (hf.locallyIntegrable (by norm_num)) (smooth_euclideanLaplacian hρ).continuous x
  have hB (i : Fin n) : Integrable (fun y => F i y * coordinateDerivative i ρ (x-y)) volume :=
    (hρc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ) ((hF i).locallyIntegrable (by norm_num))
      (smooth_coordinateDerivative hρ i).continuous x
  have hC : Integrable (fun y => g y * ρ (x-y)) volume :=
    hρc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) (hg.locallyIntegrable (by norm_num)) hρ.continuous x
  simp only [euclideanLaplacian_const_sub_comp hρ, coordinateDerivative_const_sub_comp hρ,
    mul_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg] at ht
  have hBs : Integrable (fun y => ∑ i, F i y * coordinateDerivative i ρ (x-y)) volume :=
    integrable_finset_sum Finset.univ (fun i _ => hB i)
  rw [integral_sub (f := fun y => f y * euclideanLaplacian ρ (x-y) -
      ∑ i, F i y * coordinateDerivative i ρ (x-y)) (g := fun y => g y * ρ (x-y)) (hA.sub hBs) hC,
    integral_sub hA hBs, integral_finset_sum _ (fun i _ => hB i)] at ht
  simp only [euclideanLaplacian_scalarConvolution hρ hρc hf,
    coordinateDerivative_scalarConvolution hρ hρc (hF _), scalarConvolution_flip_apply]
  linarith

lemma integral_mul_coordinateDerivative_compact_test {n : ℕ}
    {f ψ : CoordinateSpace n → ℝ} (hf : ContDiff ℝ ∞ f) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (i : Fin n) :
    (∫ x, f x * coordinateDerivative i ψ x) = -(∫ x, coordinateDerivative i f x * ψ x) := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (v := Pi.single i 1)
    (((smooth_coordinateDerivative hf i).continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left)
    ((hf.continuous.mul (smooth_coordinateDerivative hψ i).continuous).integrable_of_hasCompactSupport
      (hψc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).mul_left)
    ((hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left)
    (hf.differentiable (by simp)) (hψ.differentiable (by simp))
  exact h

lemma integral_mul_euclideanLaplacian_compact_test {n : ℕ}
    {f ψ : CoordinateSpace n → ℝ} (hf : ContDiff ℝ ∞ f) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) :
    (∫ x, f x * euclideanLaplacian ψ x) = ∫ x, euclideanLaplacian f x * ψ x := by
  have hi (i : Fin n) : (∫ x, f x * coordinateDerivative i (coordinateDerivative i ψ) x) =
      ∫ x, coordinateDerivative i (coordinateDerivative i f) x * ψ x := by
    rw [integral_mul_coordinateDerivative_compact_test hf (smooth_coordinateDerivative hψ i)
      (hψc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)) i,
      integral_mul_coordinateDerivative_compact_test (smooth_coordinateDerivative hf i) hψ hψc i,
      neg_neg]
  have hA (i : Fin n) : Integrable (fun x => f x * coordinateDerivative i (coordinateDerivative i ψ) x) volume :=
    (hf.continuous.mul (smooth_coordinateDerivative (smooth_coordinateDerivative hψ i) i).continuous).integrable_of_hasCompactSupport
      ((hψc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).mul_left
  have hB (i : Fin n) : Integrable (fun x => coordinateDerivative i (coordinateDerivative i f) x * ψ x) volume :=
    ((smooth_coordinateDerivative (smooth_coordinateDerivative hf i) i).continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  simp only [euclideanLaplacian, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finset_sum _ (fun i _ => hA i), integral_finset_sum _ (fun i _ => hB i)]
  simp only [hi]

/-- A pointwise smooth divergence-form equation implies its genuine
distributional formulation; compact support is required only of the tests. -/
theorem hasDistributionLaplacian_of_pointwise {n : ℕ}
    {f g : CoordinateSpace n → ℝ} {F : Fin n → CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hg : Continuous g)
    (heq : ∀ x, euclideanLaplacian f x = (∑ i, coordinateDerivative i (F i) x) + g x) :
    HasDistributionLaplacian f F g := by
  intro ψ hψ hψc
  have hA : Integrable (fun x => f x * euclideanLaplacian ψ x) volume :=
    (hf.continuous.mul (smooth_euclideanLaplacian hψ).continuous).integrable_of_hasCompactSupport
      (euclideanLaplacian_compact hψc).mul_left
  have hB (i : Fin n) : Integrable (fun x => F i x * coordinateDerivative i ψ x) volume :=
    ((hF i).continuous.mul (smooth_coordinateDerivative hψ i).continuous).integrable_of_hasCompactSupport
      (hψc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).mul_left
  have hD (i : Fin n) : Integrable (fun x => coordinateDerivative i (F i) x * ψ x) volume :=
    ((smooth_coordinateDerivative (hF i) i).continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have hC : Integrable (fun x => g x * ψ x) volume :=
    (hg.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have hL : Integrable (fun x => euclideanLaplacian f x * ψ x) volume :=
    ((smooth_euclideanLaplacian hf).continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have hBs : Integrable (fun x => ∑ i, F i x * coordinateDerivative i ψ x) volume :=
    integrable_finset_sum _ (fun i _ => hB i)
  have hDs : Integrable (fun x => ∑ i, coordinateDerivative i (F i) x * ψ x) volume :=
    integrable_finset_sum _ (fun i _ => hD i)
  rw [integral_sub (f := fun x => f x * euclideanLaplacian ψ x + ∑ i, F i x * coordinateDerivative i ψ x)
    (g := fun x => g x * ψ x) (hA.add hBs) hC, integral_add hA hBs,
    integral_mul_euclideanLaplacian_compact_test hf hψ hψc,
    integral_finset_sum _ (fun i _ => hB i)]
  simp_rw [integral_mul_coordinateDerivative_compact_test (hF _) hψ hψc,
    Finset.sum_neg_distrib, ← sub_eq_add_neg]
  rw [← integral_finset_sum _ (fun i _ => hD i), ← integral_sub hL hDs,
    ← integral_sub (f := fun x => euclideanLaplacian f x * ψ x -
      ∑ i, coordinateDerivative i (F i) x * ψ x) (g := fun x => g x * ψ x) (hL.sub hDs) hC]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  change _ = (0 : ℝ)
  rw [heq x, add_mul, Finset.sum_mul]
  simp only [mul_comm]
  ring

/-- Actual convolution preserves Δf=div F+g, with all smoothness,
integrability and differentiation-under-the-integral steps proved. -/
theorem HasDistributionLaplacian.scalarConvolution {n : ℕ}
    {ρ f g : CoordinateSpace n → ℝ} {F : Fin n → CoordinateSpace n → ℝ}
    (heq : HasDistributionLaplacian f F g)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hf : MemLp f 2 volume) (hF : ∀ i, MemLp (F i) 2 volume) (hg : MemLp g 2 volume) :
    HasDistributionLaplacian (scalarConvolution ρ f)
      (fun i => scalarConvolution ρ (F i)) (scalarConvolution ρ g) := by
  have hs {v : CoordinateSpace n → ℝ} (hv : MemLp v 2 volume) :
      ContDiff ℝ ∞ (GaussianTilt.Letwin.scalarConvolution ρ v) :=
    hρc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ (hv.locallyIntegrable (by norm_num))
  exact hasDistributionLaplacian_of_pointwise (hs hf) (fun i => hs (hF i)) (hs hg).continuous
    (heq.scalarConvolution_pointwise hρ hρc hf hF hg)

/-- The explicit canonical mollifier preserves the actual weak PDE. -/
theorem HasDistributionLaplacian.mollify {n : ℕ}
    {f g : CoordinateSpace n → ℝ} {F : Fin n → CoordinateSpace n → ℝ}
    (heq : HasDistributionLaplacian f F g)
    (hf : MemLp f 2 volume) (hF : ∀ i, MemLp (F i) 2 volume) (hg : MemLp g 2 volume) (k : ℕ) :
    HasDistributionLaplacian (mollify k f) (fun i => mollify k (F i)) (mollify k g) :=
  heq.scalarConvolution (canonicalMollifier_smooth n k) (canonicalMollifier_compact n k) hf hF hg

end GaussianTilt.Letwin
