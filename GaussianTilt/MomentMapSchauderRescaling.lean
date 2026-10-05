import GaussianTilt.MomentMapSchauderEuclideanOperator

/-! # Exact derivative scaling for centered dilations -/
noncomputable section
open Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def centeredRescale (f : E → F) (a : E) (c : ℝ) (x : E) : F := f (c • (x-a))

lemma contDiff_centeredRescale {f : E → F} {k : WithTop ℕ∞} (hf : ContDiff ℝ k f)
    (a : E) (c : ℝ) : ContDiff ℝ k (centeredRescale f a c) :=
  hf.comp (contDiff_const.smul (contDiff_id.sub contDiff_const))

lemma fderiv_centeredRescale {f : E → F} (hf : Differentiable ℝ f) (a x : E) (c : ℝ) :
    fderiv ℝ (centeredRescale f a c) x = c • fderiv ℝ f (c • (x-a)) := by
  have ha : HasFDerivAt (fun y : E => c • (y-a)) (c • ContinuousLinearMap.id ℝ E) x :=
    ((hasFDerivAt_id x).sub_const a).const_smul c
  have hh := (hf (c • (x-a))).hasFDerivAt.comp x ha
  have hder : HasFDerivAt (centeredRescale f a c) (c • fderiv ℝ f (c • (x-a))) x := by
    convert hh using 1
    ext v
    simp
  exact hder.fderiv

lemma secondFrechet_centeredRescale {f : E → F} (hf : ContDiff ℝ 2 f) (a x : E) (c : ℝ) :
    fderiv ℝ (fderiv ℝ (centeredRescale f a c)) x =
      c ^ 2 • fderiv ℝ (fderiv ℝ f) (c • (x-a)) := by
  have hDf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl
  have he : fderiv ℝ (centeredRescale f a c) = c • centeredRescale (fderiv ℝ f) a c := by
    funext y
    exact fderiv_centeredRescale (hf.differentiable (by norm_num)) a y c
  rw [he, fderiv_const_smul (𝕜 := ℝ) (f := centeredRescale (fderiv ℝ f) a c)
    (hDf.comp ((differentiable_id.sub_const a).const_smul c) x) c, fderiv_centeredRescale hDf, smul_smul]
  congr 1
  ring

lemma thirdFrechet_centeredRescale {f : E → F} (hf : ContDiff ℝ 3 f) (a x : E) (c : ℝ) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (centeredRescale f a c))) x =
      c ^ 3 • fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (c • (x-a)) := by
  have hD2 : Differentiable ℝ (fderiv ℝ (fderiv ℝ f)) :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiable le_rfl
  have he : fderiv ℝ (fderiv ℝ (centeredRescale f a c)) =
      c ^ 2 • centeredRescale (fderiv ℝ (fderiv ℝ f)) a c := by
    funext y
    exact secondFrechet_centeredRescale (hf.of_le (by norm_num)) a y c
  rw [he, fderiv_const_smul (𝕜 := ℝ) (f := centeredRescale (fderiv ℝ (fderiv ℝ f)) a c)
    (hD2.comp ((differentiable_id.sub_const a).const_smul c) x) (c ^ 2), fderiv_centeredRescale hD2, smul_smul]
  congr 1

end GaussianTilt.MomentMapSchauder
