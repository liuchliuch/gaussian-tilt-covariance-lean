import GaussianTilt.MomentMapLinearDirichletCampanatoL2Coherence

/-! # Actual volume and overlap geometry of truncated boundary balls -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def upperCampanatoBall (j : Fin n) (x : KernelSpace n) (r : ℝ) : Set (KernelSpace n) :=
  Metric.ball x r ∩ {y | 0 < y j}

lemma isOpen_upperCampanatoBall (j : Fin n) (x : KernelSpace n) (r : ℝ) :
    IsOpen (upperCampanatoBall j x r) :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_const (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous)

lemma upperCampanatoBall_finite (j : Fin n) (x : KernelSpace n) (r : ℝ) :
    volume (upperCampanatoBall j x r) ≠ ∞ :=
  (lt_of_le_of_lt (measure_mono inter_subset_left) measure_ball_lt_top).ne

/-- Every truncated ball centered in the closed half-space contains a real
half-radius interior ball, including when its center lies on the boundary. -/
lemma ball_subset_upperCampanatoBall (j : Fin n) (x : KernelSpace n) (hx : 0 ≤ x j)
    {r : ℝ} (hr : 0 < r) :
    Metric.ball (x+(r/2) • EuclideanSpace.basisFun (Fin n) ℝ j) (r/2) ⊆ upperCampanatoBall j x r := by
  intro y hy
  let c := x+(r/2) • EuclideanSpace.basisFun (Fin n) ℝ j
  have hn : ‖y-c‖ < r/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
  have hc : ‖c-x‖ = r/2 := by
    dsimp [c]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hr),
      (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one]
  constructor
  · rw [Metric.mem_ball,dist_eq_norm]
    have ht : ‖y-x‖ ≤ ‖y-c‖+‖c-x‖ := by
      simpa only [dist_eq_norm] using dist_triangle y c x
    rw [hc] at ht
    linarith
  · change 0 < y j
    have ht : |(y-c) j| ≤ ‖y-c‖ := PiLp.norm_apply_le (y-c) j
    have hcj : c j = x j+r/2 := by simp [c]
    simp only [PiLp.sub_apply,hcj] at ht
    linarith [neg_abs_le (y j-(x j+r/2))]

lemma real_volume_euclidean_ball [NeZero n] (x : KernelSpace n) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.ball x r) = r^n*volume.real (Metric.ball (0 : KernelSpace n) 1) := by
  rw [measureReal_def,volume.addHaar_ball x hr,ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg hr _)]
  simp only [KernelSpace,finrank_euclideanSpace,Fintype.card_fin]
  rfl

/-- A dimension-only genuine lower volume bound for all boundary-truncated balls. -/
lemma upperCampanatoBall_volume_lower [NeZero n] (j : Fin n) (x : KernelSpace n)
    (hx : 0 ≤ x j) {r : ℝ} (hr : 0 < r) :
    ((1/2 : ℝ)^n*volume.real (Metric.ball (0 : KernelSpace n) 1))*r^n ≤
      volume.real (upperCampanatoBall j x r) := by
  have hm := measureReal_mono (μ := (volume : Measure (KernelSpace n)))
    (ball_subset_upperCampanatoBall j x hx hr) (upperCampanatoBall_finite j x r)
  rw [real_volume_euclidean_ball _ (half_pos hr).le] at hm
  convert hm using 1 <;> ring

lemma upperCampanatoBall_mono {j : Fin n} {x y : KernelSpace n} {r R : ℝ}
    (h : dist x y+r ≤ R) : upperCampanatoBall j x r ⊆ upperCampanatoBall j y R := by
  intro z hz
  refine ⟨?_,hz.2⟩
  have hzdist : dist z x < r := hz.1
  have ht := dist_triangle z x y
  change dist z y < R
  linarith

lemma upperCampanatoBall_volume_constant_pos [NeZero n] :
    0 < (1/2 : ℝ)^n*volume.real (Metric.ball (0 : KernelSpace n) 1) := by
  have hb : 0 < volume.real (Metric.ball (0 : KernelSpace n) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne
  positivity

end GaussianTilt.MomentMapLinearDirichlet
