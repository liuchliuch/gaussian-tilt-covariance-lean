import GaussianTilt.MomentMapSchauderBoundaryVariableCompact

/-! # Genuine normalized small-coefficient boundary absorption -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff BoundedContinuousFunction
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- The true normalized boundary perturbation estimate. The coefficient
supremum and Hölder modulus are small after spatial rescaling. The actual
Hölder Banach norm of the initial Hessian field is absorbed, so no initial
second-derivative bound remains on the right. -/
theorem exists_compact_flat_small_coefficient_bound [NeZero n] {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (j : Fin n) (u f : KernelSpace n → ℝ)
      (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
      (B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ),
      MemLp u 2 volume → (∀ x, x j ≤ 0 → u x=0) →
      ContDiffOn ℝ 2 u (flatUpperBall j 2) →
      (∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ L*|x j|) →
      ContinuousOn B (flatClosedPatch j 2) →
      (∀ x ∈ flatUpperBall j 2, B x=fderiv ℝ (fderiv ℝ u) x) →
      (∀ x ∈ flatClosedPatch j 2, 1/64 ≤ ‖x‖ → B x=0) →
      (∃ Q : ℝ, 0 ≤ Q ∧ (∀ x ∈ flatClosedPatch j 2, ‖B x‖ ≤ Q) ∧
        ∀ x ∈ flatClosedPatch j 2, ∀ y ∈ flatClosedPatch j 2, ‖B x-B y‖ ≤ Q*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j 2, ∀ i k, |(1 : Matrix (Fin n) (Fin n) ℝ) i k-A x i k| ≤ ε) →
      (∀ x ∈ flatClosedPatch j 2, ∀ y ∈ flatClosedPatch j 2, ∀ i k, |A x i k-A y i k| ≤ ε*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j 2, matrixContraction (A x) (bilinearEntryMatrix (B x))=f x) →
      ∀ U F H : ℝ, 0 ≤ U → 0 ≤ F → 0 ≤ H →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ U) →
      (∀ x ∈ flatClosedPatch j 2, |f x| ≤ F) →
      (∀ x ∈ flatClosedPatch j 2, ∀ y ∈ flatClosedPatch j 2, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j 2, ‖B x‖ ≤ C*(U+F+H)) ∧
      (∀ x ∈ flatClosedPatch j 2, ∀ y ∈ flatClosedPatch j 2, ‖B x-B y‖ ≤ C*(U+F+H)*‖x-y‖^α) := by
  obtain ⟨C0,hC0,hbase⟩ := exists_compact_flat_poisson_hessian_bound (n := n) hα hα1
  have hn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  let ε := (6*C0*(n:ℝ)^2)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : 3*C0*(n:ℝ)^2*ε=(1:ℝ)/2 := by dsimp [ε]; field_simp; ring
  refine ⟨ε,2*C0,hε,by positivity,?_⟩
  intro j u f A B huL2 hu0 hu hgrowth hBc hBeq hB0 hinit hA hAH heq U F H hU hF hH huB hfB hfH
  let S := flatClosedPatch j 2
  have hSc : IsCompact S := isCompact_flatClosedPatch j 2
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hSc
  obtain ⟨Q0,hQ0,hBsup0,hBHolder0⟩ := hinit
  let b : S →ᵇ (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) :=
    BoundedContinuousFunction.mkOfCompact ⟨fun x => B x,continuousOn_iff_continuous_restrict.mp hBc⟩
  have hbH : ∀ x y : S, ‖b x-b y‖ ≤ Q0*dist x y^α := by
    intro x y
    exact hBHolder0 x x.2 y y.2
  let V := HolderSpace.ofBounded S (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) α b Q0 hbH
  let q := ‖V‖
  have hq : 0 ≤ q := norm_nonneg V
  have hBsup : ∀ x ∈ S, ‖B x‖ ≤ q := by
    intro x hx
    exact HolderSpace.norm_value_apply_le S _ α V ⟨x,hx⟩
  have hBHolder : ∀ x ∈ S, ∀ y ∈ S, ‖B x-B y‖ ≤ q*‖x-y‖^α := by
    intro x hx y hy
    exact HolderSpace.norm_value_sub_le S _ α V ⟨x,hx⟩ ⟨y,hy⟩
  have hSnon : S.Nonempty := ⟨0,⟨Metric.mem_closedBall_self (by norm_num),by simp⟩⟩
  obtain ⟨g,hgc,hge,hgB,hgH⟩ := exists_boundary_frozen_forcing_extension hSnon hα hα1.le
    hε.le hε.le hq hF hH A f B hA hAH hBsup hBHolder hfB hfH heq
  have hPoisson : ∀ x ∈ flatUpperBall j 2, kernelLaplacian u x= -g x := by
    intro x hx
    have hxS : x ∈ S := ⟨Metric.ball_subset_closedBall hx.1,(show 0 < x j from hx.2).le⟩
    rw [hge x hxS,hBeq x hx,neg_neg]
    exact kernelLaplacian_eq_trace_at (hu.contDiffAt ((isOpen_flatUpperBall j 2).mem_nhds hx))
  have hbounds := hbase j u g huL2 hu0 hu hgrowth hgc hPoisson U
    (F+(n:ℝ)^2*ε*q) (H+(n:ℝ)^2*(ε+ε)*q) hU (by positivity) (by positivity) huB hgB hgH B hBc hBeq hB0
  let R := C0*(U+(F+(n:ℝ)^2*ε*q)+(H+(n:ℝ)^2*(ε+ε)*q))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hqR : q ≤ R := by
    apply HolderSpace.norm_le_of_value_bounds hR V
    · intro x
      exact hbounds.1 x x.2
    · intro x y
      exact hbounds.2 x x.2 y y.2
  have hRexp : R=C0*(U+F+H)+q/2 := by
    calc
      R = C0*(U+F+H)+(3*C0*(n:ℝ)^2*ε)*q := by dsimp [R]; ring
      _ = _ := by rw [hsmall]; ring
  have hqFinal : q ≤ (2*C0)*(U+F+H) := by rw [hRexp] at hqR; linarith
  exact ⟨fun x hx => (hBsup x hx).trans hqFinal,
    fun x hx y hy => (hBHolder x hx y hy).trans (mul_le_mul_of_nonneg_right hqFinal
      (Real.rpow_nonneg (norm_nonneg _) α))⟩

end GaussianTilt.MomentMapSchauder
