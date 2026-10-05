import GaussianTilt.MomentMapSchauderBoundaryHarmonic
import GaussianTilt.MomentMapSchauderLocalPatch
import GaussianTilt.MomentMapLinearDirichletFlatWeakReflection

/-! # Scale-uniform interior Poisson jet estimates

The constants are chosen before the solution. The only solution norm on
the right is its actual local supremum; no initial derivative bound occurs.
-/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2200000
open Set Filter
open scoped ContDiff Topology
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

lemma secondFrechet_add_at {u v : KernelSpace n → ℝ} {x : KernelSpace n}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    fderiv ℝ (fderiv ℝ (fun y => u y+v y)) x =
      fderiv ℝ (fderiv ℝ u) x+fderiv ℝ (fderiv ℝ v) x := by
  obtain ⟨u', hu', heu⟩ := exists_global_contDiff_eventuallyEq 2 hu
  obtain ⟨v', hv', hev⟩ := exists_global_contDiff_eventuallyEq 2 hv
  have he : (fun y => u' y+v' y) =ᶠ[𝓝 x] (fun y => u y+v y) := heu.add hev
  rw [← he.fderiv.fderiv_eq, secondFrechet_add_C2 hu' hv',
    heu.fderiv.fderiv_eq, hev.fderiv.fderiv_eq]

lemma kernelLaplacian_sub_at {u v : KernelSpace n → ℝ} {x : KernelSpace n}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    kernelLaplacian (fun y => u y-v y) x=kernelLaplacian u x-kernelLaplacian v x := by
  obtain ⟨u', hu', heu⟩ := exists_global_contDiff_eventuallyEq 2 hu
  obtain ⟨v', hv', hev⟩ := exists_global_contDiff_eventuallyEq 2 hv
  have he : (fun y => u' y-v' y) =ᶠ[𝓝 x] (fun y => u y-v y) := heu.sub hev
  rw [← kernelLaplacian_congr_nhds he, kernelLaplacian_sub_C2 hu' hv',
    kernelLaplacian_congr_nhds heu, kernelLaplacian_congr_nhds hev]

/-- Genuine local C² solutions of Poisson's equation have quantitative
center gradient/Hessian bounds and an interior Hessian Hölder estimate,
linear in the solution supremum and the prescribed forcing norms. -/
theorem exists_unit_poisson_interior_jet_bound [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u f : KernelSpace n → ℝ,
      ContDiffOn ℝ 2 u (Metric.ball 0 2) → Continuous f → HasCompactSupport f →
      Function.support f ⊆ Metric.closedBall 0 4 →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, kernelLaplacian u x=f x) →
      ∀ U F H : ℝ, 0 ≤ U → 0 ≤ F → 0 ≤ H →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ U) →
      (∀ x, |f x| ≤ F) → (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) →
      ‖fderiv ℝ u 0‖ ≤ C*(U+F+H) ∧ ‖fderiv ℝ (fderiv ℝ u) 0‖ ≤ C*(U+F+H) ∧
      (∀ x ∈ Metric.ball (0 : KernelSpace n) (1/8), ∀ y ∈ Metric.ball (0 : KernelSpace n) (1/8),
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ C*(U+F+H)*‖x-y‖^α) := by
  obtain ⟨Ch, hCh, hhar⟩ := exists_local_harmonic_interior_jet_bounds (n := n)
  obtain ⟨CP, hCP, hpot⟩ := exists_holder_newtonian_hessian_quantitative (n := n) hα hα1
  obtain ⟨CQ, hCQ, hpotQ⟩ := exists_holder_newtonian_hessian_origin_bound (n := n) hα hα1 4
  obtain ⟨CD, hCD, hpotD⟩ := exists_holder_newtonian_gradient_origin_bound (n := n) hα hα1 4
  let N := 2*(n : ℝ)*fundamentalApproxMass n
  have hN : 0 < N := by
    have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    exact mul_pos (mul_pos (by norm_num) hn) (fundamentalApproxMass_pos n)
  let c := N⁻¹
  have hc : 0 < c := inv_pos.mpr hN
  let Z := newtonianLocalMass n 6
  have hZ : 0 ≤ Z := newtonianLocalMass_nonneg _ _
  let C := Ch*(1+c*Z)+c*(CP+CQ+CD)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u f hu hf hfc hfs heq U F H hU hF hH hub hfb hfH
  let P := fun x => c*newtonianPotential f x
  have hpotc := newtonianPotential_contDiff_two hf hfc hα hα1 hH hfH
  have hPc : ContDiff ℝ 2 P := contDiff_const.mul hpotc
  have hPeq (x : KernelSpace n) : kernelLaplacian P x=f x := by
    rw [kernelLaplacian_const_mul_C2 c hpotc, newtonianPotential_laplacian_holder hf hfc hα hα1 hH hfH]
    exact inv_mul_cancel_left₀ hN.ne' _
  have hPb : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |P x| ≤ c*F*Z := by
    intro x hx
    change |c*newtonianPotential f x| ≤ _
    rw [abs_mul, abs_of_pos hc]
    have hh := newtonianPotential_local_bound (R := 2) hF hfb hfs
      (show ‖x‖ ≤ 2 by exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hx))
    exact (mul_le_mul_of_nonneg_left hh hc.le).trans_eq (by dsimp [Z]; norm_num; ring)
  let h := fun x => u x-P x
  have hhc : ContDiffOn ℝ 2 h (Metric.ball 0 2) := hu.sub hPc.contDiffOn
  have hheq : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, kernelLaplacian h x=0 := by
    intro x hx
    rw [kernelLaplacian_sub_at (hu.contDiffAt (Metric.isOpen_ball.mem_nhds hx)) hPc.contDiffAt, heq x hx, hPeq, sub_self]
  have hhb : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |h x| ≤ U+c*F*Z :=
    fun x hx => (abs_sub _ _).trans (add_le_add (hub x hx) (hPb x hx))
  obtain ⟨hD, hQ, hLH⟩ := hhar h hhc hheq (U+c*F*Z) (by positivity) hhb
  have he : u=(fun x => h x+P x) := by funext x; dsimp [h]; ring
  have hqeq (x : KernelSpace n) (hx : x ∈ Metric.ball (0 : KernelSpace n) 2) :
      fderiv ℝ (fderiv ℝ u) x = fderiv ℝ (fderiv ℝ h) x+c • fderiv ℝ (fderiv ℝ (newtonianPotential f)) x := by
    conv_lhs => rw [he]
    rw [secondFrechet_add_at (hhc.contDiffAt (Metric.isOpen_ball.mem_nhds hx)) hPc.contDiffAt,
      secondFrechet_const_mul_C2 c hpotc]
  have hDeq : fderiv ℝ u 0 = fderiv ℝ h 0+c • fderiv ℝ (newtonianPotential f) 0 := by
    conv_lhs => rw [he]
    rw [fderiv_fun_add ((hhc.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0:ℝ)<2)))).differentiableAt (by norm_num))
      (hPc.differentiable (by norm_num) 0)]
    change _=fderiv ℝ h 0+_
    congr 1
    change fderiv ℝ (c • newtonianPotential f) 0=_
    exact fderiv_const_smul (hpotc.differentiable (by norm_num) 0) c
  have htotal (T : ℝ) (hT : 0 ≤ T) (hTC : T ≤ CP+CQ+CD) :
      Ch*(U+c*F*Z)+c*T*(F+H) ≤ C*(U+F+H) := by
    have hh1 : U+c*F*Z ≤ (1+c*Z)*(U+F+H) := by
      nlinarith [mul_nonneg (mul_nonneg hc.le hZ) hU, mul_nonneg (mul_nonneg hc.le hZ) hH]
    have hh2 : T*(F+H) ≤ (CP+CQ+CD)*(U+F+H) := by
      apply mul_le_mul hTC (by linarith)
      · positivity
      · positivity
    have hh3 := mul_le_mul_of_nonneg_left hh1 hCh.le
    have hh4 := mul_le_mul_of_nonneg_left hh2 hc.le
    dsimp [C]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hDeq]
    apply (norm_add_le _ _).trans
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    apply (add_le_add hD (mul_le_mul_of_nonneg_left (hpotD f hf hfc hfs F H hF hH hfb hfH) hc.le)).trans
    exact (by simpa only [mul_assoc] using htotal CD hCD.le (by linarith))
  · rw [hqeq 0 (Metric.mem_ball_self (by norm_num))]
    apply (norm_add_le _ _).trans
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    apply (add_le_add hQ (mul_le_mul_of_nonneg_left (hpotQ f hf hfc hfs F H hF hH hfb hfH) hc.le)).trans
    exact (by simpa only [mul_assoc] using htotal CQ hCQ.le (by linarith))
  · intro x hx y hy
    have hx2 := Metric.ball_subset_ball (by norm_num : (1/8:ℝ)≤2) hx
    have hy2 := Metric.ball_subset_ball (by norm_num : (1/8:ℝ)≤2) hy
    have hxy : ‖x-y‖ ≤ 1 := by
      have hx' : ‖x‖ < 1/8 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
      have hy' : ‖y‖ < 1/8 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
      exact (norm_sub_le _ _).trans (by linarith)
    have hxyα := Real.self_le_rpow_of_le_one (norm_nonneg (x-y)) hxy hα1.le
    rw [hqeq x hx2, hqeq y hy2]
    have he' : (fderiv ℝ (fderiv ℝ h) x+c • fderiv ℝ (fderiv ℝ (newtonianPotential f)) x)-
        (fderiv ℝ (fderiv ℝ h) y+c • fderiv ℝ (fderiv ℝ (newtonianPotential f)) y) =
        (fderiv ℝ (fderiv ℝ h) x-fderiv ℝ (fderiv ℝ h) y)+
          c • (fderiv ℝ (fderiv ℝ (newtonianPotential f)) x-fderiv ℝ (fderiv ℝ (newtonianPotential f)) y) := by module
    rw [he']
    apply (norm_add_le _ _).trans
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    have hb1 := (hLH x hx y hy).trans (mul_le_mul_of_nonneg_left hxyα (by positivity))
    have hb2 := mul_le_mul_of_nonneg_left (hpot f hf hfc F H hF hH hfb hfH x y hxy) hc.le
    apply (add_le_add hb1 hb2).trans
    have ht := mul_le_mul_of_nonneg_right (htotal CP hCP.le (by linarith)) (Real.rpow_nonneg (norm_nonneg (x-y)) α)
    nlinarith

end GaussianTilt.MomentMapSchauder
