import GaussianTilt.MomentMapSchauderBoundaryHeightEstimate
import GaussianTilt.MomentMapSchauderBoundaryPolynomial
import GaussianTilt.MomentMapLinearDirichletFlatJetCoherence

/-! # Boundary polynomials determine the actual interior derivative limits

The Hessian boundary limit is proved from the polynomial value remainder
and the literal Poisson equation by the radius-uniform interior estimate.
-/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2400000
open Set InnerProductSpace
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma near_flat_projection_ball {j : Fin n} {x z : KernelSpace n} {d : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1/8) (hz : ‖z‖ ≤ 1) (hxj : x j=d) (hxz : ‖x-z‖=d)
    {y : KernelSpace n} (hy : y ∈ Metric.ball x (d/2)) :
    y ∈ flatUpperBall j 2 ∧ ‖y-z‖ ≤ 2*d := by
  have hyx : ‖y-x‖ < d/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
  have hyz : ‖y-z‖ ≤ 2*d := by
    have hh := norm_sub_le_norm_sub_add_norm_sub y x z
    rw [hxz] at hh
    linarith
  have hyj : 0 < y j := by
    have hh : |y j-x j| ≤ ‖y-x‖ := PiLp.norm_apply_le (y-x) j
    rw [hxj] at hh
    linarith [neg_abs_le (y j-d)]
  refine ⟨⟨?_,hyj⟩,hyz⟩
  rw [Metric.mem_ball,dist_zero_right]
  have hh : ‖y‖ ≤ ‖y-z‖+‖z‖ := by
    simpa only [sub_add_cancel] using norm_add_le (y-z) z
  linarith

/-- Actual first and second derivatives converge to the symmetric boundary
polynomial at the correct rates. The interior Hessian Hölder estimate is
uniform down to the plane. -/
theorem exists_flat_boundary_interior_jet_convergence [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin n) (u f : KernelSpace n → ℝ),
      ContDiffOn ℝ 2 u (flatUpperBall j 2) → Continuous f →
      (∀ y ∈ flatUpperBall j 2, kernelLaplacian u y= -f y) →
      ∀ M H : ℝ, 0 ≤ M → 0 ≤ H → (∀ y z, |f y-f z| ≤ H*‖y-z‖^α) →
      ∀ (z p : KernelSpace n) (T : KernelSpace n →L[ℝ] KernelSpace n),
      ‖z‖ ≤ 1 → z j=0 → (∀ v w, inner ℝ (T v) w=inner ℝ v (T w)) →
      (∀ h, kernelLaplacian (quadraticJet 0 p 0 T) h= -f z) →
      (∀ h, ‖h‖ ≤ 1/4 → 0 ≤ h j → |u (z+h)-quadraticJet 0 p 0 T h| ≤ M*‖h‖^(2+α)) →
      ∀ (x : KernelSpace n) (d : ℝ), 0 < d → d ≤ 1/8 → x j=d → ‖x-z‖=d →
      ‖fderiv ℝ u x-toDual ℝ (KernelSpace n) (p+T (x-z))‖ ≤ C*(M+H)*d*d^α ∧
      ‖fderiv ℝ (fderiv ℝ u) x-operatorBilinear T‖ ≤ C*(M+H)*d^α ∧
      (∀ y ∈ Metric.ball x (d/64), ∀ v ∈ Metric.ball x (d/64),
        ‖fderiv ℝ (fderiv ℝ u) y-fderiv ℝ (fderiv ℝ u) v‖ ≤ C*(M+H)*‖y-v‖^α) := by
  obtain ⟨K,hK,hbound⟩ := exists_height_scale_poisson_jet_bound (n := n) hα hα1
  let D := (2:ℝ)^(2+α)+2^α
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro j u f hu hf heq M H hM hH hfH z p T hz hzj hT hPlap hRem x d hd hd1 hxj hxz
  let P := quadraticJet 0 p 0 T
  let Pz := fun y => P (y-z)
  let w := fun y => u y-Pz y
  let g := fun y => -(f y-f z)
  have hPc : ContDiff ℝ 2 P := contDiff_infty.mp (contDiff_quadraticJet_zero p T) 2
  have hPzc : ContDiff ℝ 2 Pz := hPc.comp (contDiff_id.sub contDiff_const)
  have hgeo : ∀ y ∈ Metric.ball x (d/2), y ∈ flatUpperBall j 2 ∧ ‖y-z‖ ≤ 2*d :=
    fun y hy => near_flat_projection_ball hd hd1 hz hxj hxz hy
  have hsub : Metric.ball x (d/4) ⊆ Metric.ball x (d/2) := Metric.ball_subset_ball (by linarith)
  have huLocal : ContDiffOn ℝ 2 u (Metric.ball x (d/4)) := hu.mono (fun y hy => (hgeo y (hsub hy)).1)
  have hw : ContDiffOn ℝ 2 w (Metric.ball x (d/4)) := huLocal.sub hPzc.contDiffOn
  have hg : Continuous g := (hf.sub continuous_const).neg
  have hPzeq (y : KernelSpace n) : kernelLaplacian Pz y= -f z := by
    change kernelLaplacian (fun v => P (v-z)) y= _
    simp only [sub_eq_add_neg,kernelLaplacian_comp_add_right]
    exact hPlap _
  have hweq : ∀ y ∈ Metric.ball x (d/4), kernelLaplacian w y=g y := by
    intro y hy
    rw [kernelLaplacian_sub_at (huLocal.contDiffAt (Metric.isOpen_ball.mem_nhds hy)) hPzc.contDiffAt,
      heq y (hgeo y (hsub hy)).1,hPzeq]
    dsimp [g]
    ring
  let M' := M*(2:ℝ)^(2+α)
  let H' := H*(2:ℝ)^α
  have hHle : H ≤ H' := by
    have hh : (1:ℝ) ≤ 2^α := Real.one_le_rpow (by norm_num) hα.le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hH
  have hwB : ∀ y ∈ Metric.ball x (d/4), |w y| ≤ M'*d^2*d^α := by
    intro y hy
    have hG := hgeo y (hsub hy)
    have hr := hRem (y-z) (by linarith [hG.2]) (by
      simp only [PiLp.sub_apply,hzj,sub_zero]
      exact hG.1.2.le)
    have he : z+(y-z)=y := by abel
    rw [he] at hr
    have hh := hr.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hG.2 (by linarith : 0 ≤ 2+α)) hM)
    have hscale : (2*d)^(2+α)=2^(2+α)*d^2*d^α := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hd.le,Real.rpow_add hd]
      norm_num [Real.rpow_two]
      ring
    rw [hscale] at hh
    exact hh.trans_eq (by dsimp [M']; ring)
  have hgB : ∀ y ∈ Metric.ball x (d/2), |g y| ≤ H'*d^α := by
    intro y hy
    rw [show g y= -(f y-f z) from rfl,abs_neg]
    have hh := (hfH y z).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (hgeo y hy).2 hα.le) hH)
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hd.le] at hh
    exact hh.trans_eq (by dsimp [H']; ring)
  have hgH : ∀ y ∈ Metric.ball x (d/2), ∀ v ∈ Metric.ball x (d/2),
      |g y-g v| ≤ H'*‖y-v‖^α := by
    intro y hy v hv
    have he : g y-g v= -(f y-f v) := by dsimp [g]; ring
    rw [he,abs_neg]
    exact (hfH y v).trans (mul_le_mul_of_nonneg_right hHle (Real.rpow_nonneg (norm_nonneg _) α))
  obtain ⟨hDw,hQw,hHw⟩ := hbound w g x d M' H' hd (by dsimp [M']; positivity)
    (by dsimp [H']; positivity) hw hg hweq hwB hgB hgH
  have htotal : K*(M'+H') ≤ K*D*(M+H) := by
    have hh : M'+H' ≤ D*(M+H) := by
      dsimp [M',H',D]
      nlinarith [mul_nonneg hM (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) α),
        mul_nonneg hH (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (2+α))]
    exact (mul_le_mul_of_nonneg_left hh hK.le).trans_eq (by ring)
  have hx0 : x ∈ Metric.ball x (d/4) := Metric.mem_ball_self (by positivity)
  have hDPeq (y : KernelSpace n) : fderiv ℝ Pz y=toDual ℝ (KernelSpace n) (p+T (y-z)) := by
    change fderiv ℝ (fun v => P (v-z)) y=_
    simp only [sub_eq_add_neg,fderiv_comp_add_right]
    exact fderiv_quadraticJet_zero p T hT _
  have hQPeq (y : KernelSpace n) : fderiv ℝ (fderiv ℝ Pz) y=operatorBilinear T := by
    change fderiv ℝ (fderiv ℝ (fun v => P (v-z))) y=_
    simp only [sub_eq_add_neg,secondFrechet_comp_add_right]
    exact secondFrechet_quadraticJet_zero p T hT _
  have hDweq : fderiv ℝ w x=fderiv ℝ u x-toDual ℝ (KernelSpace n) (p+T (x-z)) := by
    rw [fderiv_fun_sub ((huLocal.contDiffAt (Metric.isOpen_ball.mem_nhds hx0)).differentiableAt (by norm_num))
      (hPzc.differentiable (by norm_num) x),hDPeq]
  have hQweq (y : KernelSpace n) (hy : y ∈ Metric.ball x (d/4)) :
      fderiv ℝ (fderiv ℝ w) y=fderiv ℝ (fderiv ℝ u) y-operatorBilinear T := by
    rw [secondFrechet_sub_at (huLocal.contDiffAt (Metric.isOpen_ball.mem_nhds hy)) hPzc.contDiffAt,hQPeq]
  rw [hDweq] at hDw
  rw [hQweq x hx0] at hQw
  refine ⟨hDw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htotal hd.le) (Real.rpow_nonneg hd.le α)),
    hQw.trans (mul_le_mul_of_nonneg_right htotal (Real.rpow_nonneg hd.le α)),?_⟩
  intro y hy v hv
  have hh := hHw y hy v hv
  have hsmall : Metric.ball x (d/64) ⊆ Metric.ball x (d/4) := Metric.ball_subset_ball (by linarith)
  rw [hQweq y (hsmall hy),hQweq v (hsmall hv),sub_sub_sub_cancel_right] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right htotal (Real.rpow_nonneg (norm_nonneg _) α))

end GaussianTilt.MomentMapSchauder
