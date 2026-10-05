import GaussianTilt.MomentMapRegularityImprovementNumeric
import GaussianTilt.MomentMapRegularityImprovementComposition

/-! # The finite affine budget closes at every genuine adaptive scale -/
noncomputable section
open Set
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity

lemma adaptiveRadius_rpow_geometric_bound {R c d : ℝ}
    (hR : 0 < R) (hR1 : R≤1) (hc : 0≤c) (hd : 0≤d) (k : ℕ) :
    (adaptiveRadius R c k)^d ≤ R^d*(R^(c*d))^k := by
  induction k with
  | zero => simp [adaptiveRadius]
  | succ k ih =>
    have hp := adaptiveRadius_pos (c:=c) hR k
    have he : (adaptiveRadius R c (k+1))^d =
        (adaptiveRadius R c k)^d*(adaptiveRadius R c k)^(c*d) := by
      rw [adaptiveRadius,← Real.rpow_mul hp.le,← Real.rpow_add hp]
      congr 1
      ring
    rw [he,pow_succ]
    have hm := Real.rpow_le_rpow hp.le (adaptiveRadius_le_initial hR hR1 hc k) (mul_nonneg hc hd)
    have hh := mul_le_mul ih hm (Real.rpow_nonneg hp.le _) (by positivity)
    convert hh using 1 <;> ring

def improvementDistortionBudget (R c d K : ℝ) (k : ℕ) : ℝ :=
  2*K*∑ i∈Finset.range k, (adaptiveRadius R c i)^d

@[simp] lemma improvementDistortionBudget_zero (R c d K : ℝ) :
    improvementDistortionBudget R c d K 0=0 := by simp [improvementDistortionBudget]

lemma improvementDistortionBudget_succ (R c d K : ℝ) (k : ℕ) :
    improvementDistortionBudget R c d K (k+1)=
      improvementDistortionBudget R c d K k+2*K*(adaptiveRadius R c k)^d := by
  simp only [improvementDistortionBudget,Finset.sum_range_succ]
  ring

lemma improvementDistortionBudget_le {R c d K : ℝ}
    (hR : 0 < R) (hR1 : R<1) (hc : 0 < c) (hd : 0 < d) (hK : 0≤K) (k : ℕ) :
    improvementDistortionBudget R c d K k≤2*K*R^d/(1-R^(c*d)) := by
  have hq : 0≤R^(c*d) := Real.rpow_nonneg hR.le _
  have hq1 : R^(c*d)<1 := Real.rpow_lt_one hR.le hR1 (mul_pos hc hd)
  have hs := sum_le_hasSum (Finset.range k)
    (fun i _ => mul_nonneg (Real.rpow_nonneg hR.le d) (pow_nonneg hq i))
    ((hasSum_geometric_of_lt_one hq hq1).mul_left (R^d))
  have hb : (∑ i∈Finset.range k, (adaptiveRadius R c i)^d)≤R^d/(1-R^(c*d)) := by
    apply (Finset.sum_le_sum (fun i _ => adaptiveRadius_rpow_geometric_bound hR hR1.le hc.le hd.le i)).trans
    simpa only [div_eq_mul_inv] using hs
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0≤2*K)
  convert hh using 1 <;> dsimp only [improvementDistortionBudget] <;> ring

lemma improvementDistortionBudget_exp_le_two {R c d K : ℝ}
    (hR : 0 < R) (hR1 : R<1) (hc : 0 < c) (hd : 0 < d) (hK : 0≤K)
    (hsmall : 2*K*R^d/(1-R^(c*d))≤Real.log 2) (k : ℕ) :
    Real.exp (improvementDistortionBudget R c d K k)≤2 := by
  have hh := Real.exp_le_exp.mpr ((improvementDistortionBudget_le hR hR1 hc hd hK k).trans hsmall)
  simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using hh

end GaussianTilt.MomentMapRegularity
