import GaussianTilt.MomentMapSchauderBoundaryVariableAffineJets
import GaussianTilt.MomentMapSchauderBoundaryVariableRescaled

/-! # Uniform boundary first-jet estimate through an actual normalization map -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 3200000
open Set Matrix
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- The estimate constants depend only on fixed map/inverse bounds,
coefficient modulus and working radius. The actual affine covariance and
boundary preservation are verified for the supplied normalization. -/
theorem exists_boundary_first_jet_bound_of_normalization [NeZero n]
    {α K R M I : ℝ} (hα : 0 < α) (hα1 : α < 1) (hK : 0 ≤ K) (hR : 0 < R)
    (hM : 0 < M) (hI : 0 < I) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 2*ρ ≤ R ∧ 0 < C ∧ ∀ (j : Fin n)
      (P : KernelSpace n ≃L[ℝ] KernelSpace n) (c : ℝ), 0 < c →
      (∀ x, (P x) j=c*x j) → ‖P.toContinuousLinearMap‖ ≤ M → ‖P.symm.toContinuousLinearMap‖ ≤ I →
      ∀ (u f : KernelSpace n → ℝ) (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
      (D : KernelSpace n → KernelSpace n →L[ℝ] ℝ)
      (B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ),
      (∀ x, x j ≤ 0 → u x=0) → ContDiffOn ℝ 2 u (flatUpperBall j R) →
      (∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.ball (0 : KernelSpace n) R, |u x| ≤ L*|x j|) →
      (∀ x ∈ flatUpperBall j R, D x=fderiv ℝ u x) →
      (∀ x ∈ flatUpperBall j R, B x=fderiv ℝ (fderiv ℝ u) x) →
      BoundedHolderOn α B (flatClosedPatch j R) →
      euclideanEquivMatrix P*(euclideanEquivMatrix P)ᵀ=A 0 →
      (∀ x ∈ flatClosedPatch j R, (A x).IsSymm) →
      (∀ x ∈ flatClosedPatch j R, ∀ y ∈ flatClosedPatch j R, ∀ i k, |A x i k-A y i k| ≤ K*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j R, matrixContraction (A x) (bilinearEntryMatrix (B x))=f x) →
      ∀ U V HU HD F H : ℝ, 0 ≤ U → 0 ≤ V → 0 ≤ HU → 0 ≤ HD → 0 ≤ F → 0 ≤ H →
      (∀ x ∈ flatClosedPatch j R, |u x| ≤ U) → (∀ x ∈ flatClosedPatch j R, ‖D x‖ ≤ V) →
      (∀ x ∈ flatClosedPatch j R, ∀ y ∈ flatClosedPatch j R, |u x-u y| ≤ HU*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j R, ∀ y ∈ flatClosedPatch j R, ‖D x-D y‖ ≤ HD*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j R, |f x| ≤ F) →
      (∀ x ∈ flatClosedPatch j R, ∀ y ∈ flatClosedPatch j R, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j ρ, ‖B x‖ ≤ C*(U+V+HU+HD+F+H)) ∧
      (∀ x ∈ flatClosedPatch j ρ, ∀ y ∈ flatClosedPatch j ρ,
        ‖B x-B y‖ ≤ C*(U+V+HU+HD+F+H)*‖x-y‖^α) := by
  let K' := (n:ℝ)^2*I^2*K*M^α
  obtain ⟨r,C0,hr,hrR,hC0,hbase⟩ := exists_rescaled_normalized_boundary_first_jet_bound (n := n)
    hα hα1 (show 0 ≤ K' by dsimp [K']; positivity) (div_pos hR hM)
  let ρ := min (R/2) (r/(512*I))
  have hρ : 0 < ρ := lt_min (half_pos hR) (div_pos hr (by positivity))
  have hρR : 2*ρ ≤ R := by have hh := min_le_left (R/2) (r/(512*I)); dsimp [ρ]; linarith
  have hρr : ρ ≤ r/(512*I) := min_le_right _ _
  let T := 2+M+2*M^α+M*M^α
  have hT : 0 < T := by dsimp [T]; positivity
  let C := C0*T*(1+I^2)*(1+I^α)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ρ,C,hρ,hρR,hC,?_⟩
  intro j P c hc hplane hP hPi u f A D B hu0 hu hgrowth hD hB hBH hPP hAs hAH heq U V HU HD F H hU hV hHU hHD hF hH huB hDB huH hDH hfB hfH
  let v := u ∘ P
  let Av := boundaryPullbackCoefficient P A
  let Dv := fun x => (D (P x)).comp P.toContinuousLinearMap
  let Bv := fun x => (B (P x)).bilinearComp P.toContinuousLinearMap P.toContinuousLinearMap
  let fv := f ∘ P
  have hmap : MapsTo P (flatClosedPatch j (R/M)) (flatClosedPatch j R) := by
    intro x hx
    have hh := (boundary_normalization_maps_halfball P j hc hM hP hplane).2 ⟨flat_patch_norm hx,hx.2⟩
    exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hh.1,hh.2⟩
  have hmapO : MapsTo P (flatUpperBall j (R/M)) (flatUpperBall j R) := by
    intro x hx
    have hn : ‖x‖ < R/M := by simpa only [Metric.mem_ball,dist_zero_right] using hx.1
    have hh := (boundary_normalization_maps_halfball P j hc hM hP hplane).1 ⟨hn,hx.2⟩
    exact ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hh.1,hh.2⟩
  have hv0 : ∀ x, x j ≤ 0 → v x=0 := by
    intro x hx
    exact hu0 _ (by rw [hplane]; exact mul_nonpos_of_nonneg_of_nonpos hc.le hx)
  have hv : ContDiffOn ℝ 2 v (flatUpperBall j (R/M)) := hu.comp P.contDiff.contDiffOn hmapO
  have hvg : ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.ball (0 : KernelSpace n) (R/M), |v x| ≤ L*|x j| := by
    obtain ⟨L,hL,hug⟩ := hgrowth
    refine ⟨L*c,by positivity,?_⟩
    intro x hx
    have hn : ‖x‖ < R/M := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hPx : P x ∈ Metric.ball (0 : KernelSpace n) R := by
      rw [Metric.mem_ball,dist_zero_right]
      have hh := (P.toContinuousLinearMap.le_opNorm x).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg x))
      change ‖P x‖ ≤ M*‖x‖ at hh
      have ht := (lt_div_iff₀ hM).mp hn
      nlinarith only [hh,ht]
    have hh := hug (P x) hPx
    rw [hplane,abs_mul,abs_of_pos hc] at hh
    exact hh.trans_eq (by ring)
  have hDv : ∀ x ∈ flatUpperBall j (R/M), Dv x=fderiv ℝ v x := by
    intro x hx
    have hud := (hu.contDiffAt ((isOpen_flatUpperBall j R).mem_nhds (hmapO hx))).differentiableAt (by norm_num)
    rw [show v=u ∘ P from rfl,fderiv_comp x hud P.differentiableAt,P.fderiv]
    rw [show Dv x=(D (P x)).comp P.toContinuousLinearMap from rfl,hD _ (hmapO hx)]
  have hBv : ∀ x ∈ flatUpperBall j (R/M), Bv x=fderiv ℝ (fderiv ℝ v) x := by
    intro x hx
    rw [show v=u ∘ P from rfl,secondFrechet_comp_equiv_at P (hu.contDiffAt ((isOpen_flatUpperBall j R).mem_nhds (hmapO hx)))]
    rw [show Bv x=(B (P x)).bilinearComp P.toContinuousLinearMap P.toContinuousLinearMap from rfl,hB _ (hmapO hx)]
  have hBvH := boundedHolderOn_boundaryPullbackHessian P hmap hα.le hBH
  have hAv0 : Av 0=1 := boundaryPullbackCoefficient_at_zero P A hPP
  have hAvs : ∀ x ∈ flatClosedPatch j (R/M), (Av x).IsSymm :=
    fun x hx => boundaryPullbackCoefficient_isSymm P A (hAs _ (hmap hx))
  have hAvH := boundaryPullbackCoefficient_holder P A hmap hα.le hK hM.le hI.le hP hPi hAH
  have hveq : ∀ x ∈ flatClosedPatch j (R/M), matrixContraction (Av x) (bilinearEntryMatrix (Bv x))=fv x := by
    intro x hx
    rw [boundary_pullback_operator_identity]
    exact heq _ (hmap hx)
  have hvb : ∀ x ∈ flatClosedPatch j (R/M), |v x| ≤ U := fun x hx => huB _ (hmap hx)
  have hDvb : ∀ x ∈ flatClosedPatch j (R/M), ‖Dv x‖ ≤ M*V :=
    fun x hx => norm_comp_linear_le P hP (hDB _ (hmap hx)) hV
  have hvh := scalar_holder_comp_equiv P hmap hα.le hHU hM.le hP huH
  have hDvh := boundaryPullbackFirst_holder P D hmap hα.le hHD hM.le hP hDH
  have hfvb : ∀ x ∈ flatClosedPatch j (R/M), |fv x| ≤ F := fun x hx => hfB _ (hmap hx)
  have hfvh := scalar_holder_comp_equiv P hmap hα.le hH hM.le hP hfH
  obtain ⟨hsup,hholder⟩ := hbase j v fv Av Dv Bv hv0 hv hvg hDv hBv hBvH hAv0 hAvs hAvH hveq
    U (M*V) (HU*M^α) (M*HD*M^α) F (H*M^α) hU (by positivity) (by positivity) (by positivity) hF (by positivity)
    hvb hDvb hvh hDvh hfvb hfvh
  let W := U+V+HU+HD+F+H
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hdata : U+M*V+HU*M^α+M*HD*M^α+F+H*M^α ≤ T*W := by
    have h1 : U ≤ W := by dsimp [W]; linarith
    have h2 := mul_le_mul_of_nonneg_left (show V ≤ W by dsimp [W]; linarith) hM.le
    have h3 := mul_le_mul_of_nonneg_right (show HU ≤ W by dsimp [W]; linarith) (Real.rpow_nonneg hM.le α)
    have h4 := mul_le_mul_of_nonneg_left (show HD ≤ W by dsimp [W]; linarith) (show 0 ≤ M*M^α by positivity)
    have h5 : F ≤ W := by dsimp [W]; linarith
    have h6 := mul_le_mul_of_nonneg_right (show H ≤ W by dsimp [W]; linarith) (Real.rpow_nonneg hM.le α)
    dsimp [T]
    nlinarith only [h1,h2,h3,h4,h5,h6]
  have hdataC := mul_le_mul_of_nonneg_left hdata hC0.le
  have hInv : ∀ x ∈ flatClosedPatch j ρ, P.symm x ∈ flatClosedPatch j (r/512) := by
    intro x hx
    constructor
    · rw [Metric.mem_closedBall,dist_zero_right]
      have hh := (P.symm.toContinuousLinearMap.le_opNorm x).trans (mul_le_mul_of_nonneg_right hPi (norm_nonneg x))
      have hn := mul_le_mul_of_nonneg_left ((flat_patch_norm hx).trans hρr) hI.le
      have he : I*(r/(512*I))=r/512 := by field_simp
      rw [he] at hn
      exact hh.trans hn
    · have hh := hplane (P.symm x)
      rw [P.apply_symm_apply] at hh
      exact (mul_nonneg_iff_of_pos_left hc).mp (hh ▸ hx.2)
  have hscale (x : KernelSpace n) : Bv (P.symm x)=(B x).bilinearComp P.toContinuousLinearMap P.toContinuousLinearMap := by
    simp only [Bv,P.apply_symm_apply]
  have hPi2 : ‖P.symm.toContinuousLinearMap‖^2 ≤ I^2 := sq_le_sq₀ (norm_nonneg _) hI.le |>.mpr hPi
  have hCsup : C0*T*I^2 ≤ C := by
    calc
      _ ≤ C0*T*(1+I^2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ C := by
        dsimp [C]
        exact le_mul_of_one_le_right (by positivity) (by linarith [Real.rpow_nonneg hI.le α])
  have hCH : C0*T*I^2*I^α ≤ C := by
    dsimp [C]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (by linarith : I^2 ≤ 1+I^2) (by positivity)
    · linarith
    · exact Real.rpow_nonneg hI.le α
    · positivity
  constructor
  · intro x hx
    have hh := (hsup _ (hInv x hx)).trans hdataC
    rw [hscale] at hh
    have hb := (boundaryPullbackHessian_norm_recover P (B x)).trans (mul_le_mul hh hPi2 (sq_nonneg _) (by positivity))
    exact hb.trans (by convert mul_le_mul_of_nonneg_right hCsup hW using 1 <;> ring)
  · intro x hx y hy
    have hh := (hholder _ (hInv x hx) _ (hInv y hy)).trans
      (mul_le_mul_of_nonneg_right hdataC (Real.rpow_nonneg (norm_nonneg _) α))
    rw [hscale,hscale,← bilinearComp_sub] at hh
    have hn : ‖P.symm x-P.symm y‖ ≤ I*‖x-y‖ := by
      rw [← map_sub]
      exact (P.symm.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_right hPi (norm_nonneg _))
    have hpw := Real.rpow_le_rpow (norm_nonneg _) hn hα.le
    rw [Real.mul_rpow hI.le (norm_nonneg _)] at hpw
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hpw (by positivity))
    have hb := (boundaryPullbackHessian_norm_recover P (B x-B y)).trans
      (mul_le_mul hh' hPi2 (sq_nonneg _) (by positivity))
    apply hb.trans
    have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCH hW)
      (Real.rpow_nonneg (norm_nonneg (x-y)) α)
    convert ht using 1 <;> ring

end GaussianTilt.MomentMapSchauder
