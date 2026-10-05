import GaussianTilt.MomentMapHolderInteriorEmbedding
import GaussianTilt.MomentMapHolderJetBounds

/-! # Exact second-jet composition algebra with quantitative operator bounds -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set
namespace GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def postcomposeBilinear (D : F →L[ℝ] ℝ) (Q : E →L[ℝ] E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E F ℝ) D).comp Q

@[simp] lemma postcomposeBilinear_apply (D : F →L[ℝ] ℝ) (Q : E →L[ℝ] E →L[ℝ] F) (v w : E) :
    postcomposeBilinear D Q v w = D (Q v w) := rfl

lemma norm_postcomposeBilinear_le (D : F →L[ℝ] ℝ) (Q : E →L[ℝ] E →L[ℝ] F) :
    ‖postcomposeBilinear D Q‖ ≤ ‖D‖*‖Q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  change ‖D (Q v w)‖ ≤ _
  calc
    _ ≤ ‖D‖*‖Q v w‖ := D.le_opNorm _
    _ ≤ ‖D‖*(‖Q v‖*‖w‖) := mul_le_mul_of_nonneg_left ((Q v).le_opNorm w) (norm_nonneg _)
    _ ≤ ‖D‖*((‖Q‖*‖v‖)*‖w‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (Q.le_opNorm v) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

lemma norm_bilinearComp_two_le (B : F →L[ℝ] F →L[ℝ] ℝ) (P Q : E →L[ℝ] F) :
    ‖B.bilinearComp P Q‖ ≤ ‖B‖*‖P‖*‖Q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [ContinuousLinearMap.bilinearComp_apply]
  calc
    _ ≤ ‖B (P v)‖*‖Q w‖ := (B (P v)).le_opNorm _
    _ ≤ (‖B‖*‖P v‖)*‖Q w‖ := mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
    _ ≤ (‖B‖*(‖P‖*‖v‖))*(‖Q‖*‖w‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (P.le_opNorm v) (norm_nonneg B)) (Q.le_opNorm w)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma norm_postcomposeBilinear_sub_le (D G : F →L[ℝ] ℝ) (Q R : E →L[ℝ] E →L[ℝ] F) :
    ‖postcomposeBilinear D Q-postcomposeBilinear G R‖ ≤ ‖D-G‖*‖Q‖+‖G‖*‖Q-R‖ := by
  have he : postcomposeBilinear D Q-postcomposeBilinear G R =
      postcomposeBilinear (D-G) Q+postcomposeBilinear G (Q-R) := by
    ext v w
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,postcomposeBilinear_apply,map_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖postcomposeBilinear (D-G) Q‖+‖postcomposeBilinear G (Q-R)‖ := norm_add_le (postcomposeBilinear (D-G) Q) (postcomposeBilinear G (Q-R))
    _ ≤ _ := add_le_add (norm_postcomposeBilinear_le (D-G) Q) (norm_postcomposeBilinear_le G (Q-R))

lemma norm_bilinearComp_diagonal_sub_le
    (B C : F →L[ℝ] F →L[ℝ] ℝ) (P Q : E →L[ℝ] F) :
    ‖B.bilinearComp P P-C.bilinearComp Q Q‖ ≤
      ‖B-C‖*‖P‖*‖P‖+‖C‖*‖P-Q‖*‖P‖+‖C‖*‖Q‖*‖P-Q‖ := by
  have he : B.bilinearComp P P-C.bilinearComp Q Q =
      (B-C).bilinearComp P P + C.bilinearComp (P-Q) P + C.bilinearComp Q (P-Q) := by
    ext v w
    simp only [ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply,map_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖(B-C).bilinearComp P P + C.bilinearComp (P-Q) P‖ + ‖C.bilinearComp Q (P-Q)‖ := norm_add_le ((B-C).bilinearComp P P + C.bilinearComp (P-Q) P) (C.bilinearComp Q (P-Q))
    _ ≤ (‖(B-C).bilinearComp P P‖+‖C.bilinearComp (P-Q) P‖)+‖C.bilinearComp Q (P-Q)‖ :=
      add_le_add_right (norm_add_le ((B-C).bilinearComp P P) (C.bilinearComp (P-Q) P)) _
    _ ≤ _ := add_le_add (add_le_add (norm_bilinearComp_two_le (B-C) P P)
      (norm_bilinearComp_two_le C (P-Q) P)) (norm_bilinearComp_two_le C Q (P-Q))

lemma norm_clm_comp_sub_le (D G : F →L[ℝ] ℝ) (P Q : E →L[ℝ] F) :
    ‖D.comp P-G.comp Q‖ ≤ ‖D-G‖*‖P‖+‖G‖*‖P-Q‖ := by
  have he : D.comp P-G.comp Q = (D-G).comp P+G.comp (P-Q) := by
    ext v
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,map_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _))

end GaussianTilt.HolderSpace
