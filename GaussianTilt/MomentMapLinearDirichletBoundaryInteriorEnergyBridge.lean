import GaussianTilt.MomentMapLinearDirichletBoundaryMeanBounds

/-! # Scale-correct transfer from boundary excess to an interior starting ball -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- An actual height-scale interior ball lies inside the boundary-centered
half-ball of radius four times its height. -/
theorem height_ball_subset_projected_upperBall (j : Fin n) (x : KernelSpace n)
    (hx : 0 < x j) :
    Metric.ball x (x j/2) ⊆ upperCampanatoBall j
      (x-x j • EuclideanSpace.basisFun (Fin n) ℝ j) (4*x j) := by
  intro y hy
  have hyx : ‖y-x‖ < x j/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
  have hcoord : |y j-x j| ≤ ‖y-x‖ := by simpa only [PiLp.sub_apply] using PiLp.norm_apply_le (y-x) j
  have hheight : 0 < y j := by linarith [neg_abs_le (y j-x j)]
  refine ⟨?_,hheight⟩
  change dist y (x-x j • EuclideanSpace.basisFun (Fin n) ℝ j) < 4*x j
  have hd : dist x (x-x j • EuclideanSpace.basisFun (Fin n) ℝ j) = x j := by
    rw [dist_eq_norm,sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos hx,
      (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one]
  have ht := dist_triangle y x (x-x j • EuclideanSpace.basisFun (Fin n) ℝ j)
  rw [hd] at ht
  simp only [dist_eq_norm] at ht ⊢
  linarith

/-- The genuine squared residual on the height-scale interior ball is
controlled by the boundary normal excess, with its radius power intact. -/
theorem interior_initial_error_of_boundary_excess
    (j : Fin n) (x : KernelSpace n) (hx : 0 < x j)
    {G : KernelSpace n → KernelSpace n} {p : KernelSpace n} {C β : ℝ}
    (hG : MemLp G 2 (volume.restrict (upperCampanatoBall j
      (x-x j • EuclideanSpace.basisFun (Fin n) ℝ j) (4*x j))))
    (hE : (∫ y in upperCampanatoBall j (x-x j • EuclideanSpace.basisFun (Fin n) ℝ j) (4*x j),
      ‖G y-p‖^2) ≤ C*(4*x j)^((n:ℝ)+β)) :
    (∫ y in Metric.ball x (x j/2), ‖G y-p‖^2) ≤ C*(4*x j)^((n:ℝ)+β) := by
  haveI : Fact (volume (upperCampanatoBall j
      (x-x j • EuclideanSpace.basisFun (Fin n) ℝ j) (4*x j)) < ∞) :=
    ⟨(upperCampanatoBall_finite _ _ _).lt_top⟩
  have hI := (hG.sub (memLp_const p)).integrable_norm_pow (p := 2) (by norm_num)
  apply le_trans _ hE
  exact setIntegral_mono_set hI (ae_of_all _ (fun _ => sq_nonneg _))
    (ae_of_all _ (fun y hy => height_ball_subset_projected_upperBall j x hx hy))

/-- Uniform boundary estimates at every center give an actual normal
comparison with scale-correct interior starting error and uniformly
bounded coefficient. No pointwise bound on the field is assumed. -/
theorem exists_uniform_normal_interior_start [NeZero n]
    {R C β M : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hβ : 0 < β) (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (j : Fin n) (Z : Set (KernelSpace n))
      (G : KernelSpace n → KernelSpace n),
      (∀ z ∈ Z, z j=0) →
      (∀ z ∈ Z, MemLp G 2 (volume.restrict (upperCampanatoBall j z R))) →
      (∀ z ∈ Z, (∫ y in upperCampanatoBall j z R, ‖G y‖^2) ≤ M) →
      (∀ z ∈ Z, ∀ r, 0 < r → r ≤ R →
        (∫ y in upperCampanatoBall j z r,
          ‖G y-normalMean (volume.restrict (upperCampanatoBall j z r)) j G •
            EuclideanSpace.basisFun (Fin n) ℝ j‖^2) ≤ C*r^((n:ℝ)+β)) →
      ∀ x : KernelSpace n, 0 < x j → 4*x j ≤ R →
        (x-x j • EuclideanSpace.basisFun (Fin n) ℝ j) ∈ Z →
        ∃ t : ℝ, |t| ≤ L ∧
          (∫ y in Metric.ball x (x j/2),
            ‖G y-t • EuclideanSpace.basisFun (Fin n) ℝ j‖^2) ≤ C*(4*x j)^((n:ℝ)+β) := by
  obtain ⟨L,hL,hbound⟩ := exists_uniform_normalMean_bound (n := n) hR hC hβ hM
  refine ⟨L,hL,?_⟩
  intro j Z G hZ hG hEnergy hExcess x hx hxR hxZ
  let z := x-x j • EuclideanSpace.basisFun (Fin n) ℝ j
  let t := normalMean (volume.restrict (upperCampanatoBall j z (4*x j))) j G
  have hr : 0 < 4*x j := by positivity
  refine ⟨t,hbound j z (by rw [hZ z hxZ]) G (hG z hxZ) (hEnergy z hxZ)
    (hExcess z hxZ) _ hr hxR,?_⟩
  apply interior_initial_error_of_boundary_excess j x hx
  · apply (hG z hxZ).mono_measure
    apply Measure.restrict_mono _ le_rfl
    apply upperCampanatoBall_mono
    simpa only [z,dist_self,zero_add] using hxR
  · exact hExcess z hxZ _ hr hxR

end GaussianTilt.MomentMapLinearDirichlet
