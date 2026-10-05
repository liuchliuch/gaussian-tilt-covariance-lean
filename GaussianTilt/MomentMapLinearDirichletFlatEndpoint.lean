import GaussianTilt.MomentMapLinearDirichletFlatIteration
import GaussianTilt.MomentMapLinearDirichletFlatCampanatoJets

/-!
# The genuine normalized flat boundary Taylor expansion

The constructed geometric polynomials are converted to their actual
symmetric jets. Proved half-ball coefficient convergence and radius
interpolation produce a true order-(2+α) expansion. Exact plane vanishing
and harmonicity pass to the limit through continuous evaluation and trace.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Gradient ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma oscillationExponent_rpow_eq {θ α : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    oscillationExponent θ (θ^α) = α := by
  unfold oscillationExponent
  rw [Real.log_rpow hθ]
  exact mul_div_cancel_right₀ α (Real.log_neg hθ hθ1).ne

/-- Actual normalized flat boundary Schauder expansion, with a symmetric
harmonic polynomial vanishing on the boundary plane. The constants depend
only on the dimension and forcing exponent. -/
theorem exists_normalized_flat_boundary_expansion [NeZero n] {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧ ∀ (j : Fin n) (u f : KernelSpace n → ℝ),
      FlatWeakPoisson j u f → Continuous f → HasCompactSupport f → ∀ H : ℝ, 0 ≤ H →
      (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) → f 0 = 0 → H*2^α ≤ ε →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ 1) →
      ∃ A : KernelSpace n →L[ℝ] ℝ, ∃ Q : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ,
        (∀ v w, Q v w = Q w v) ∧
        (∀ x, x j = 0 → flatTaylorPolynomial A Q x = 0) ∧
        (∀ x, kernelLaplacian (flatTaylorPolynomial A Q) x = 0) ∧
        (∀ x, ‖x‖ ≤ 1 → 0 ≤ x j →
          |u x-flatTaylorPolynomial A Q x| ≤ M*‖x‖^(2+α)) := by
  obtain ⟨θ,ε,hθ,hθ8,hε,hε4,hGeom⟩ := exists_flat_geometric_quadratic_approximations (n := n) hα hα1
  have hθ1 : θ < 1 := hθ8.trans_lt (by norm_num)
  let q := θ^α
  have hq : 0 < q := Real.rpow_pos_of_pos hθ _
  have hq1 : q < 1 := Real.rpow_lt_one hθ.le hθ1 hα
  let C := campanatoHalfBallLimitConstant 1 θ q 1
  let M := max C 0+1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨ε,M,hε,hM,?_⟩
  intro j u f hu hfc hfs H hH hholder hf0 hsmall hub
  obtain ⟨Aseq,Qseq,hPlane,hHarm,hApprox⟩ := hGeom j u f hu hfc hfs H hH hholder hf0 hsmall hub
  let p := fun k => gradient (flatTaylorPolynomial (Aseq k) (Qseq k)) 0
  let T := fun k => frechetHessian (flatTaylorPolynomial (Aseq k) (Qseq k)) 0
  have hsym := fun k => flatTaylorPolynomial_frechetHessian_symmetric (Aseq k) (Qseq k)
  have hpower : θ^(2+α) = θ^2*q := by
    dsimp [q]
    rw [Real.rpow_add hθ]
    norm_num
  have happ : ∀ k, ∀ x : KernelSpace n, ‖x‖ ≤ 1*θ^k → 0 ≤ x j →
      |u x-quadraticJet 0 (p k) 0 (T k) x| ≤ 1*(θ^2*q)^k := by
    intro k x hx hxj
    rw [← flatTaylorPolynomial_eq_quadraticJet]
    simpa only [one_mul, hpower] using hApprox k x (by simpa using hx) hxj
  obtain ⟨hC,a₀,p₀,T₀,ha,hp,hT,hTs,hrem⟩ := geometric_halfBall_quadratic_approximation_endpoint_with_limits
    j u (fun _ => 0) p T (R := 1) (ρ := θ) (q := q) (C := 1)
      zero_lt_one hθ hθ1 hq hq1 (by norm_num) hsym happ
  have ha0 : a₀ = 0 := tendsto_nhds_unique ha tendsto_const_nhds
  subst a₀
  let A : KernelSpace n →L[ℝ] ℝ := innerSL ℝ p₀
  let Q : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ := (innerSL ℝ).comp T₀
  have hquad (x : KernelSpace n) : flatTaylorPolynomial A Q x = quadraticJet 0 p₀ 0 T₀ x := by
    simp [flatTaylorPolynomial, quadraticJet, A, Q, innerSL_apply]
  have hQ (v w : KernelSpace n) : Q v w = inner ℝ (T₀ v) w := rfl
  have htrace : (∑ i : Fin n, inner ℝ (T₀ (EuclideanSpace.basisFun (Fin n) ℝ i))
      (EuclideanSpace.basisFun (Fin n) ℝ i)) = 0 := by
    let tr := fun S : KernelSpace n →L[ℝ] KernelSpace n => ∑ i : Fin n,
      inner ℝ (S (EuclideanSpace.basisFun (Fin n) ℝ i)) (EuclideanSpace.basisFun (Fin n) ℝ i)
    have hc : Continuous tr := by dsimp [tr]; fun_prop
    have htk (k : ℕ) : tr (T k) = 0 := by
      dsimp [tr,T]
      simp only [inner_frechetHessian]
      rw [← kernelLaplacian_eq_trace_at (contDiff_infty.mp (contDiff_flatTaylorPolynomial (Aseq k) (Qseq k)) 2).contDiffAt]
      exact hHarm k 0
    have ht := hc.continuousAt.tendsto.comp hT
    have ht0 : Tendsto (fun k => tr (T k)) atTop (𝓝 (0 : ℝ)) := by simpa only [htk] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique ht ht0
  refine ⟨A,Q,?_,?_,?_,?_⟩
  · intro v w
    rw [hQ,hQ]
    exact (hTs v w).trans (real_inner_comm (T₀ w) v)
  · intro y hy
    have hc : Continuous (fun z : KernelSpace n × (KernelSpace n →L[ℝ] KernelSpace n) =>
        quadraticJet 0 z.1 0 z.2 y) := by unfold quadraticJet; fun_prop
    have hv := hc.continuousAt.tendsto.comp (hp.prodMk_nhds hT)
    change Tendsto (fun k => quadraticJet 0 (p k) 0 (T k) y) atTop (𝓝 (quadraticJet 0 p₀ 0 T₀ y)) at hv
    have he (k : ℕ) : quadraticJet 0 (p k) 0 (T k) y = 0 := by
      rw [← flatTaylorPolynomial_eq_quadraticJet]
      exact hPlane k y hy
    have hv0 : Tendsto (fun k => quadraticJet 0 (p k) 0 (T k) y) atTop (𝓝 (0 : ℝ)) := by
      simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    rw [hquad]
    exact tendsto_nhds_unique hv hv0
  · intro x
    rw [kernelLaplacian_flatTaylorPolynomial]
    exact htrace
  · intro x hx hxj
    rw [hquad]
    have hb := hrem x hx hxj
    rw [oscillationExponent_rpow_eq hθ hθ1] at hb
    apply hb.trans
    exact mul_le_mul_of_nonneg_right (show C ≤ M by dsimp [M]; linarith [le_max_left C 0])
      (Real.rpow_nonneg (norm_nonneg x) _)

end GaussianTilt.MomentMapLinearDirichlet
