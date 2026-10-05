import GaussianTilt.MomentMapSchauderBoundaryVariableJetEstimate

/-! # Boundary a priori estimate including the true curvature drift -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2800000
open Set Matrix
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.HolderSpace
variable {n : ℕ}

/-- This is the local input for the genuine compact-cover global a priori
estimate: all lower-jet terms are eliminated, and the remaining highest
norm has any prescribed small coefficient. The radius is independent of
that coefficient and of the unknown jet. -/
theorem exists_boundary_drift_jet_estimate_small_highest [NeZero n]
    {α K R lam Λ L0 L1 : ℝ} (hα : 0 < α) (hα1 : α < 1) (hK : 0 ≤ K) (hR : 0 < R)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) :
    ∃ ρ : ℝ, 0 < ρ ∧ 4*ρ ≤ R ∧ ∀ (j : Fin n) (δ : ℝ), 0 < δ →
      ∃ C : ℝ, 0 < C ∧ ∀ J : Jet (KernelSpace n) ℝ (convex_flatClosedPatch j R) α,
      (∀ x : flatClosedPatch j R, (x : KernelSpace n) j=0 →
        value (flatClosedPatch j R) ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J) x=0) →
      ∀ (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ) (b : KernelSpace n → KernelSpace n) (f : KernelSpace n → ℝ), (A 0).PosDef →
      (∀ v : KernelSpace n, lam*‖v‖^2 ≤ euclideanQuadratic (A 0) v) →
      (∀ v : KernelSpace n, euclideanQuadratic (A 0) v ≤ Λ*‖v‖^2) →
      (∀ x ∈ flatClosedPatch j (R/2), (A x).IsSymm) →
      (∀ x ∈ flatClosedPatch j (R/2), ∀ y ∈ flatClosedPatch j (R/2), ∀ i k, |A x i k-A y i k| ≤ K*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j (R/2), ‖b x‖ ≤ L0) →
      (∀ x ∈ flatClosedPatch j (R/2), ∀ y ∈ flatClosedPatch j (R/2), ‖b x-b y‖ ≤ L1*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j (R/2), matrixContraction (A x) (bilinearEntryMatrix (flatJetSecond j R α J x))+flatJetFirst j R α J x (b x)=f x) →
      ∀ U F H : ℝ, 0 ≤ U → 0 ≤ F → 0 ≤ H →
      (∀ x : flatClosedPatch j R, |value (flatClosedPatch j R) ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J) x| ≤ U) →
      (∀ x ∈ flatClosedPatch j (R/2), |f x| ≤ F) →
      (∀ x ∈ flatClosedPatch j (R/2), ∀ y ∈ flatClosedPatch j (R/2), |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j ρ, ‖flatJetSecond j R α J x‖ ≤ C*(U+F+H)+δ*flatJetSecondNorm j R α J) ∧
      (∀ x ∈ flatClosedPatch j ρ, ∀ y ∈ flatClosedPatch j ρ,
        ‖flatJetSecond j R α J x-flatJetSecond j R α J y‖ ≤
          (C*(U+F+H)+δ*flatJetSecondNorm j R α J)*‖x-y‖^α) := by
  obtain ⟨ρ,C0,hρ,hρR,hC0,hbase⟩ := exists_elliptic_boundary_first_jet_bound (n := n) hα hα1 hK (half_pos hR) hlam hΛ
  refine ⟨ρ,hρ,by linarith,?_⟩
  intro j δ hδ
  let Z := 3+2*L0+L1
  have hZ : 0 < Z := by dsimp [Z]; positivity
  let η := δ/(Z*C0)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨L,hL,hinterp⟩ := halfBall_jet_lower_holder_small_highest_norm j hR hα hα1.le hη
  let C := C0*(1+Z*L)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro J hzero A b f hA0 hlower hupper hAs hAH hbB hbH heq U F H hU hF hH huB hfB hfH
  let u := flatJetValue j R α J
  let D := flatJetFirst j R α J
  let B := flatJetSecond j R α J
  let Q := flatJetSecondNorm j R α J
  have hQ : 0 ≤ Q := norm_nonneg _
  let V := L*U+η*Q
  have hV : 0 ≤ V := by dsimp [V]; positivity
  obtain ⟨hu0,huC2,hD,hB,hBH,hgrowth⟩ := flat_zero_jet_classical_data j hR hα J hzero
  have hsub : flatClosedPatch j (R/2) ⊆ flatClosedPatch j R := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (by linarith) hx.1,hx.2⟩
  have hsubO : flatUpperBall j (R/2) ⊆ flatUpperBall j R := fun x hx =>
    ⟨Metric.ball_subset_ball (by linarith) hx.1,hx.2⟩
  have hlocal := hinterp J U hU huB
  dsimp only at hlocal
  have hub : ∀ x ∈ flatClosedPatch j (R/2), |u x| ≤ U := by
    intro x hx
    rw [show u x=value (flatClosedPatch j R) ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J) ⟨x,hsub hx⟩ from
      extendValue_mem α _ (hsub hx)]
    exact huB ⟨x,hsub hx⟩
  let g := fun x => f x-D x (b x)
  have hgeq : ∀ x ∈ flatClosedPatch j (R/2), matrixContraction (A x) (bilinearEntryMatrix (B x))=g x := by
    intro x hx
    have hh := heq x hx
    dsimp [g]
    linarith
  have hgB : ∀ x ∈ flatClosedPatch j (R/2), |g x| ≤ F+V*L0 := by
    intro x hx
    apply (abs_sub _ _).trans
    have hh : |D x (b x)| ≤ V*L0 := by
      have ht := (D x).le_opNorm (b x)
      rw [Real.norm_eq_abs] at ht
      exact ht.trans (mul_le_mul (hlocal.1 x hx).1 (hbB x hx) (norm_nonneg _) hV)
    exact add_le_add (hfB x hx) hh
  have hgH : ∀ x ∈ flatClosedPatch j (R/2), ∀ y ∈ flatClosedPatch j (R/2),
      |g x-g y| ≤ (H+V*L1+V*L0)*‖x-y‖^α := by
    intro x hx y hy
    have hh := holder_clm_apply_bound hV hL0 hV hL1
      (fun z hz => (hlocal.1 z hz).1) hbB hlocal.2.2 hbH x hx y hy
    rw [Real.norm_eq_abs] at hh
    have he : g x-g y=(f x-f y)-(D x (b x)-D y (b y)) := by dsimp [g]; ring
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add (hfH x hx y hy) hh).trans_eq (by ring))
  have hbounds := hbase j u g A D B hu0 (huC2.mono hsubO)
    ⟨‖jetFirst (KernelSpace n) ℝ (convex_flatClosedPatch j R) α J‖,norm_nonneg _,hgrowth⟩
    (fun x hx => hD x (hsubO hx)) (fun x hx => hB x (hsubO hx)) (hBH.mono hsub)
    hA0 hlower hupper hAs hAH hgeq U V V V (F+V*L0) (H+V*L1+V*L0) hU hV hV hV (by positivity) (by positivity) hub
    (fun x hx => (hlocal.1 x hx).1) hlocal.2.1 hlocal.2.2 hgB hgH
  have hηeq : Z*C0*η=δ := by dsimp [η]; field_simp
  have htotal : C0*(U+V+V+V+(F+V*L0)+(H+V*L1+V*L0)) ≤ C*(U+F+H)+δ*Q := by
    have he : C0*(U+V+V+V+(F+V*L0)+(H+V*L1+V*L0))=C0*(1+Z*L)*U+C0*(F+H)+δ*Q := by
      have hηQ := congrArg (fun z : ℝ => z*Q) hηeq
      dsimp [Z] at hηQ ⊢
      dsimp [V]
      nlinarith only [hηQ]
    rw [he]
    have hLC : C0*(1+Z*L) ≤ C := by dsimp [C]; linarith
    have hC0C : C0 ≤ C := by dsimp [C]; nlinarith [mul_nonneg (mul_nonneg hC0.le hZ.le) hL]
    have hh1 := mul_le_mul_of_nonneg_right hLC hU
    have hh2 := mul_le_mul_of_nonneg_right hC0C (add_nonneg hF hH)
    nlinarith only [hh1,hh2]
  exact ⟨fun x hx => (hbounds.1 x hx).trans htotal,
    fun x hx y hy => (hbounds.2 x hx y hy).trans (mul_le_mul_of_nonneg_right htotal
      (Real.rpow_nonneg (norm_nonneg _) α))⟩

end GaussianTilt.MomentMapSchauder
