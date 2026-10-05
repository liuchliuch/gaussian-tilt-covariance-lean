import GaussianTilt.MomentMapLinearDirichletFlatImprovement

/-!
# Actual geometric flat-boundary quadratic approximations

Each normalized residual is a concretely constructed L² weak solution.
The proved improvement theorem chooses its harmonic polynomial, and an
exact coefficient update records the approximation in the original
variables. Induction produces genuine half-ball approximations at every
geometric scale, without supplying a Campanato approximation premise.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma flatTaylorPolynomial_update (A A' : KernelSpace n →L[ℝ] ℝ)
    (Q Q' : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) (t r : ℝ) (y : KernelSpace n) :
    flatTaylorPolynomial (A+(t*r⁻¹) • A') (Q+(t*(r⁻¹)^2) • Q') y =
      flatTaylorPolynomial A Q y + t*flatTaylorPolynomial A' Q' (r⁻¹ • y) := by
  simp only [flatTaylorPolynomial, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    map_smul, smul_eq_mul]
  ring

lemma kernelLaplacian_add_C2 {f g : KernelSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : KernelSpace n) :
    kernelLaplacian (fun y => f y+g y) x = kernelLaplacian f x+kernelLaplacian g x := by
  rw [kernelLaplacian_eq_trace (hf.add hg), secondFrechet_add_C2 hf hg,
    kernelLaplacian_eq_trace hf, kernelLaplacian_eq_trace hg]
  simp only [kernelHessianTrace, ContinuousLinearMap.add_apply, Finset.sum_add_distrib]

structure FlatIterationState (j : Fin n) (u : KernelSpace n → ℝ) (θ α H : ℝ) (k : ℕ) where
  linear : KernelSpace n →L[ℝ] ℝ
  quadratic : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ
  residual : KernelSpace n → ℝ
  forcing : KernelSpace n → ℝ
  data : FlatWeakPoisson j residual forcing
  forcing_continuous : Continuous forcing
  forcing_compact : HasCompactSupport forcing
  forcing_holder : ∀ x y, |forcing x-forcing y| ≤ H*‖x-y‖^α
  forcing_zero : forcing 0 = 0
  residual_bound : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |residual x| ≤ 1
  plane : ∀ x, x j = 0 → flatTaylorPolynomial linear quadratic x = 0
  harmonic : ∀ x, kernelLaplacian (flatTaylorPolynomial linear quadratic) x = 0
  identity : ∀ x ∈ flatUpperBall j 2,
    u (θ^k • x)-flatTaylorPolynomial linear quadratic (θ^k • x) =
      (θ^(2+α))^k * residual x

/-- The actual normalized construction produces quadratic approximations
on every closed upper half-ball. The constants θ and ε depend only on
n and the specified forcing exponent. -/
theorem exists_flat_geometric_quadratic_approximations [NeZero n] {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ θ ε : ℝ, 0 < θ ∧ θ ≤ 1/8 ∧ 0 < ε ∧ ε ≤ 1/4 ∧
      ∀ (j : Fin n) (u f : KernelSpace n → ℝ), FlatWeakPoisson j u f →
      Continuous f → HasCompactSupport f → ∀ H : ℝ, 0 ≤ H →
      (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) → f 0 = 0 → H*2^α ≤ ε →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ 1) →
      ∃ A : ℕ → KernelSpace n →L[ℝ] ℝ,
      ∃ Q : ℕ → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ,
        (∀ k x, x j = 0 → flatTaylorPolynomial (A k) (Q k) x = 0) ∧
        (∀ k x, kernelLaplacian (flatTaylorPolynomial (A k) (Q k)) x = 0) ∧
        (∀ k x, ‖x‖ ≤ θ^k → 0 ≤ x j →
          |u x-flatTaylorPolynomial (A k) (Q k) x| ≤ (θ^(2+α))^k) := by
  obtain ⟨θ,ε,hθ,hθ8,hε,hε4,hImprove⟩ := exists_flat_normalized_improvement (n := n) hα hα1
  refine ⟨θ,ε,hθ,hθ8,hε,hε4,?_⟩
  intro j u f hu hfc hfs H hH hholder hf0 hsmall hub
  have hθ1 : θ ≤ 1 := hθ8.trans (by norm_num)
  let σ := θ^(2+α)
  have hσ : 0 < σ := Real.rpow_pos_of_pos hθ _
  have hstates : ∀ k : ℕ, Nonempty (FlatIterationState j u θ α H k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨⟨0, 0, u, f, hu, hfc, hfs, hholder, hf0, hub, ?_, ?_, ?_⟩⟩
      · intro x _
        simp [flatTaylorPolynomial]
      · intro x
        rw [kernelLaplacian_flatTaylorPolynomial]
        simp
      · intro x _
        simp [flatTaylorPolynomial]
    | succ k ih =>
      obtain ⟨s⟩ := ih
      obtain ⟨a,q,hPlane,hHarm,hNext,hBound⟩ := hImprove j s.residual s.forcing s.data
        s.forcing_continuous s.forcing_compact H hH s.forcing_holder s.forcing_zero hsmall s.residual_bound
      let P := flatTaylorPolynomial a q
      let A := s.linear+(σ^k*(θ^k)⁻¹) • a
      let Q := s.quadratic+(σ^k*((θ^k)⁻¹)^2) • q
      have hup (y : KernelSpace n) : flatTaylorPolynomial A Q y =
          flatTaylorPolynomial s.linear s.quadratic y + σ^k*P ((θ^k)⁻¹ • y) :=
        flatTaylorPolynomial_update s.linear a s.quadratic q (σ^k) (θ^k) y
      refine ⟨⟨A, Q, normalizedFlatResidual j θ α s.residual P,
        normalizedFlatSource θ α s.forcing, hNext,
        normalizedFlatSource_continuous s.forcing_continuous θ α,
        normalizedFlatSource_compact s.forcing_compact hθ α,
        normalizedFlatSource_holder hθ hH s.forcing_holder,
        normalizedFlatSource_zero s.forcing_zero θ α, hBound, ?_, ?_, ?_⟩⟩
      · intro y hy
        have hp : P ((θ^k)⁻¹ • y) = 0 := hPlane _ (by simp [hy])
        rw [hup, s.plane y hy, hp, mul_zero, add_zero]
      · intro y
        have hOld := contDiff_infty.mp (contDiff_flatTaylorPolynomial s.linear s.quadratic) 2
        have hPS : ContDiff ℝ 2 (fun z : KernelSpace n => P ((θ^k)⁻¹ • z)) :=
          (contDiff_infty.mp (contDiff_flatTaylorPolynomial a q) 2).comp (contDiff_const.smul contDiff_id)
        have hfunc : flatTaylorPolynomial A Q =
            (fun z => flatTaylorPolynomial s.linear s.quadratic z + σ^k*P ((θ^k)⁻¹ • z)) := funext hup
        have hPH : ∀ z, kernelLaplacian P z = 0 := hHarm
        rw [hfunc, kernelLaplacian_add_C2 hOld (contDiff_const.mul hPS), s.harmonic,
          kernelLaplacian_const_mul_C2 _ hPS,
          kernelLaplacian_comp_smul_C2 (contDiff_infty.mp (contDiff_flatTaylorPolynomial a q) 2),
          hPH, mul_zero, mul_zero, add_zero]
      · intro x hx
        have hθx := smul_mem_flatUpperBall j hθ hθ1 hx
        have hold := s.identity (θ • x) hθx
        have hpow : θ^k • (θ • x) = θ^(k+1) • x := by rw [smul_smul, pow_succ]
        rw [hpow] at hold
        have hinv : (θ^k)⁻¹ • (θ^(k+1) • x) = θ • x := by
          rw [smul_smul, pow_succ, ← mul_assoc, inv_mul_cancel₀ (pow_pos hθ k).ne', one_mul]
        have hres := normalizedFlatResidual_eq (u := s.residual) (P := P) (r := θ) (α := α) hx
        have hcancel : σ*flatNormalizationFactor θ α = 1 := by
          simpa only [σ, mul_comm] using flatNormalizationFactor_cancel hθ α
        have hresid : σ*normalizedFlatResidual j θ α s.residual P x = s.residual (θ • x)-P (θ • x) := by
          rw [hres, ← mul_assoc, hcancel, one_mul]
        change u (θ^(k+1) • x)-flatTaylorPolynomial A Q (θ^(k+1) • x) =
          σ^(k+1)*normalizedFlatResidual j θ α s.residual P x
        rw [hup, hinv]
        calc
          _ = (u (θ^(k+1) • x)-flatTaylorPolynomial s.linear s.quadratic (θ^(k+1) • x)) - σ^k*P (θ • x) := by ring
          _ = σ^k*s.residual (θ • x)-σ^k*P (θ • x) := by rw [hold]
          _ = σ^k*(σ*normalizedFlatResidual j θ α s.residual P x) := by rw [hresid]; ring
          _ = _ := by rw [pow_succ]; ring
  let s := fun k => Classical.choice (hstates k)
  refine ⟨fun k => (s k).linear, fun k => (s k).quadratic, fun k => (s k).plane, fun k => (s k).harmonic, ?_⟩
  intro k z hz hzj
  by_cases hzpos : 0 < z j
  · let x := (θ^k)⁻¹ • z
    have hθk : 0 < θ^k := pow_pos hθ k
    have hxnorm : ‖x‖ ≤ 1 := by
      dsimp [x]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hθk)]
      exact (inv_mul_le_one₀ hθk).mpr hz
    have hxj : 0 < x j := by
      change 0 < (θ^k)⁻¹*z j
      exact mul_pos (inv_pos.mpr hθk) hzpos
    have hxball : x ∈ Metric.ball (0 : KernelSpace n) 2 := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have he := (s k).identity x ⟨hxball,hxj⟩
    have hxinv : θ^k • x = z := by dsimp [x]; rw [smul_smul, mul_inv_cancel₀ hθk.ne', one_smul]
    rw [hxinv] at he
    rw [he, abs_mul, abs_of_nonneg (pow_pos (Real.rpow_pos_of_pos hθ _) k).le]
    exact (mul_le_mul_of_nonneg_left ((s k).residual_bound x hxball) (pow_pos (Real.rpow_pos_of_pos hθ _) k).le).trans_eq (mul_one _)
  · have hz0 : z j = 0 := le_antisymm (le_of_not_gt hzpos) hzj
    rw [hu.zero_lower z hz0.le, (s k).plane z hz0, sub_self, abs_zero]
    positivity

end GaussianTilt.MomentMapLinearDirichlet
