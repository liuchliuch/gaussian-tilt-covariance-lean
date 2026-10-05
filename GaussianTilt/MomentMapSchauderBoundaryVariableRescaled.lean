import GaussianTilt.MomentMapSchauderBoundaryVariableFirstJet
import GaussianTilt.MomentMapSchauderBoundaryVariableScale

/-! # Actual small-radius normalized boundary Schauder localization -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 3200000
open Set Filter Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- Radius and estimate constant are chosen before the coefficient field
and solution. The actual local coefficient modulus, rather than an assumed
smallness property of the equation, supplies normalized absorption. -/
theorem exists_rescaled_normalized_boundary_first_jet_bound [NeZero n]
    {α K R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hK : 0 ≤ K) (hR : 0 < R) :
    ∃ r C : ℝ, 0 < r ∧ 4*r ≤ R ∧ 0 < C ∧ ∀ (j : Fin n) (u f : KernelSpace n → ℝ)
      (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
      (D : KernelSpace n → KernelSpace n →L[ℝ] ℝ)
      (B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ),
      (∀ x, x j ≤ 0 → u x=0) → ContDiffOn ℝ 2 u (flatUpperBall j R) →
      (∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.ball (0 : KernelSpace n) R, |u x| ≤ L*|x j|) →
      (∀ x ∈ flatUpperBall j R, D x=fderiv ℝ u x) →
      (∀ x ∈ flatUpperBall j R, B x=fderiv ℝ (fderiv ℝ u) x) →
      BoundedHolderOn α B (flatClosedPatch j R) → A 0=1 →
      (∀ x ∈ flatClosedPatch j R, (A x).IsSymm) →
      (∀ x ∈ flatClosedPatch j R, ∀ y ∈ flatClosedPatch j R, ∀ i k, |A x i k-A y i k| ≤ K*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j R, matrixContraction (A x) (bilinearEntryMatrix (B x))=f x) →
      ∀ U V HU HD F H : ℝ, 0 ≤ U → 0 ≤ V → 0 ≤ HU → 0 ≤ HD → 0 ≤ F → 0 ≤ H →
      (∀ x ∈ flatClosedPatch j R, |u x| ≤ U) → (∀ x ∈ flatClosedPatch j R, ‖D x‖ ≤ V) →
      (∀ x ∈ flatClosedPatch j R, ∀ y ∈ flatClosedPatch j R, |u x-u y| ≤ HU*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j R, ∀ y ∈ flatClosedPatch j R, ‖D x-D y‖ ≤ HD*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j R, |f x| ≤ F) →
      (∀ x ∈ flatClosedPatch j R, ∀ y ∈ flatClosedPatch j R, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ flatClosedPatch j (r/512), ‖B x‖ ≤ C*(U+V+HU+HD+F+H)) ∧
      (∀ x ∈ flatClosedPatch j (r/512), ∀ y ∈ flatClosedPatch j (r/512),
        ‖B x-B y‖ ≤ C*(U+V+HU+HD+F+H)*‖x-y‖^α) := by
  obtain ⟨ε,C0,hε,hC0,hunit⟩ := exists_normalized_boundary_first_jet_bound (n := n) hα hα1
  obtain ⟨r,hr,hrR,hcoeff⟩ := exists_normalized_boundary_coefficient_radius (n := n) hα hK hR hε
  let T := 1+r+r^α+r*r^α+r^2+r^2*r^α
  have hT : 0 < T := by dsimp [T]; positivity
  let C := C0*T*(1+(r^2)⁻¹)*(1+(r⁻¹)^α)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨r,C,hr,hrR,hC,?_⟩
  intro j u f A D B hu0 hu hgrowth hD hB hBH hA0 hAs hAH heq U V HU HD F H hU hV hHU hHD hF hH huB hDB huH hDH hfB hfH
  let v := fun x : KernelSpace n => u (r • x)
  let Av := fun x : KernelSpace n => A (r • x)
  let Dv := fun x : KernelSpace n => r • D (r • x)
  let Bv := fun x : KernelSpace n => r^2 • B (r • x)
  let fv := fun x : KernelSpace n => r^2*f (r • x)
  have hmap : ∀ x ∈ flatClosedPatch j 2, r • x ∈ flatClosedPatch j R := by
    intro x hx
    have hh := smul_mem_flatClosedPatch hr.le hx
    exact ⟨Metric.closedBall_subset_closedBall (by linarith) hh.1,hh.2⟩
  have hmapO : ∀ x ∈ flatUpperBall j 2, r • x ∈ flatUpperBall j R := by
    intro x hx
    refine ⟨?_,?_⟩
    · rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      have hn : ‖x‖ < 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hx.1
      nlinarith
    · change 0 < r*x j
      exact mul_pos hr hx.2
  have hdif (x y : KernelSpace n) : ‖r • x-r • y‖^α=r^α*‖x-y‖^α := by
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hr,Real.mul_rpow hr.le (norm_nonneg _)]
  have hv0 : ∀ x, x j ≤ 0 → v x=0 := by
    intro x hx
    exact hu0 _ (by change r*x j ≤ 0; exact mul_nonpos_of_nonneg_of_nonpos hr.le hx)
  have hv : ContDiffOn ℝ 2 v (flatUpperBall j 2) := hu.comp (contDiff_const.smul contDiff_id).contDiffOn hmapO
  have hvGrowth : ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |v x| ≤ L*|x j| := by
    obtain ⟨L,hL,hug⟩ := hgrowth
    refine ⟨L*r,by positivity,?_⟩
    intro x hx
    have hxr : r • x ∈ Metric.ball (0 : KernelSpace n) R := by
      rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      have hn : ‖x‖ < 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
      nlinarith
    have hh := hug (r • x) hxr
    simp only [PiLp.smul_apply,smul_eq_mul,abs_mul,abs_of_pos hr] at hh
    exact hh.trans_eq (by ring)
  have hDv : ∀ x ∈ flatUpperBall j 2, Dv x=fderiv ℝ v x := by
    intro x hx
    have hc := hu.contDiffAt ((isOpen_flatUpperBall j R).mem_nhds (hmapO x hx))
    have hc' : ContDiffAt ℝ 2 u (r • x+(0 : KernelSpace n)) := by simpa only [add_zero] using hc
    have hh := fderiv_comp_dilate_translate_at (0 : KernelSpace n) x r hc'
    simpa only [add_zero,v,Dv,hD _ (hmapO x hx)] using hh.symm
  have hBv : ∀ x ∈ flatUpperBall j 2, Bv x=fderiv ℝ (fderiv ℝ v) x := by
    intro x hx
    have hc := hu.contDiffAt ((isOpen_flatUpperBall j R).mem_nhds (hmapO x hx))
    have hc' : ContDiffAt ℝ 2 u (r • x+(0 : KernelSpace n)) := by simpa only [add_zero] using hc
    have hh := secondFrechet_comp_dilate_translate_at (0 : KernelSpace n) x r hc'
    simpa only [add_zero,v,Bv,hB _ (hmapO x hx)] using hh.symm
  have hBvH : BoundedHolderOn α Bv (flatClosedPatch j 2) := by
    obtain ⟨Q,hQ,hQb,hQH⟩ := hBH
    refine ⟨r^2*Q*(1+r^α),by positivity,?_,?_⟩
    · intro x hx
      rw [show Bv x=r^2 • B (r • x) from rfl,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
      apply (mul_le_mul_of_nonneg_left (hQb _ (hmap x hx)) (sq_nonneg r)).trans
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg r) hQ) (Real.rpow_nonneg hr.le α)]
    · intro x hx y hy
      change ‖r^2 • B (r • x)-r^2 • B (r • y)‖ ≤ _
      rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
      have hh := hQH _ (hmap x hx) _ (hmap y hy)
      rw [hdif] at hh
      have ht := mul_le_mul_of_nonneg_left hh (sq_nonneg r)
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg r) hQ) (Real.rpow_nonneg (norm_nonneg (x-y)) α)]
  obtain ⟨hAv,hAvH⟩ := hcoeff j A hA0 hAH
  have hvEq : ∀ x ∈ flatClosedPatch j 2, matrixContraction (Av x) (bilinearEntryMatrix (Bv x))=fv x := by
    intro x hx
    rw [boundary_matrixContraction_rescale,heq _ (hmap x hx)]
  have hvB : ∀ x ∈ flatClosedPatch j 2, |v x| ≤ U := fun x hx => huB _ (hmap x hx)
  have hDvB : ∀ x ∈ flatClosedPatch j 2, ‖Dv x‖ ≤ r*V := by
    intro x hx
    rw [show Dv x=r • D (r • x) from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (hDB _ (hmap x hx)) hr.le
  have hvH : ∀ x ∈ flatClosedPatch j 2, ∀ y ∈ flatClosedPatch j 2, |v x-v y| ≤ (HU*r^α)*‖x-y‖^α := by
    intro x hx y hy
    have hh := huH _ (hmap x hx) _ (hmap y hy)
    rw [hdif] at hh
    exact hh.trans_eq (by ring)
  have hDvH : ∀ x ∈ flatClosedPatch j 2, ∀ y ∈ flatClosedPatch j 2, ‖Dv x-Dv y‖ ≤ (r*HD*r^α)*‖x-y‖^α := by
    intro x hx y hy
    change ‖r • D (r • x)-r • D (r • y)‖ ≤ _
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    have hh := hDH _ (hmap x hx) _ (hmap y hy)
    rw [hdif] at hh
    exact (mul_le_mul_of_nonneg_left hh hr.le).trans_eq (by ring)
  have hfvB : ∀ x ∈ flatClosedPatch j 2, |fv x| ≤ r^2*F := by
    intro x hx
    rw [show fv x=r^2*f (r • x) from rfl,abs_mul,abs_of_nonneg (sq_nonneg r)]
    exact mul_le_mul_of_nonneg_left (hfB _ (hmap x hx)) (sq_nonneg r)
  have hfvH : ∀ x ∈ flatClosedPatch j 2, ∀ y ∈ flatClosedPatch j 2, |fv x-fv y| ≤ (r^2*H*r^α)*‖x-y‖^α := by
    intro x hx y hy
    change |r^2*f (r • x)-r^2*f (r • y)| ≤ _
    rw [← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg r)]
    have hh := hfH _ (hmap x hx) _ (hmap y hy)
    rw [hdif] at hh
    exact (mul_le_mul_of_nonneg_left hh (sq_nonneg r)).trans_eq (by ring)
  obtain ⟨hVs,hVH⟩ := hunit j v fv Av Dv Bv hv0 hv hvGrowth hDv hBv hBvH (fun x hx => hAs _ (hmap x hx)) hAv
    hAvH hvEq U (r*V) (HU*r^α) (r*HD*r^α) (r^2*F) (r^2*H*r^α)
    hU (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hvB hDvB hvH hDvH hfvB hfvH
  let W := U+V+HU+HD+F+H
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hdata : U+r*V+HU*r^α+r*HD*r^α+r^2*F+r^2*H*r^α ≤ T*W := by
    have h1 : U ≤ W := by dsimp [W]; linarith
    have h2 := mul_le_mul_of_nonneg_left (show V ≤ W by dsimp [W]; linarith) hr.le
    have h3 := mul_le_mul_of_nonneg_right (show HU ≤ W by dsimp [W]; linarith) (Real.rpow_nonneg hr.le α)
    have h4 := mul_le_mul_of_nonneg_left (show HD ≤ W by dsimp [W]; linarith) (show 0 ≤ r*r^α by positivity)
    have h5 := mul_le_mul_of_nonneg_left (show F ≤ W by dsimp [W]; linarith) (sq_nonneg r)
    have h6 := mul_le_mul_of_nonneg_left (show H ≤ W by dsimp [W]; linarith) (show 0 ≤ r^2*r^α by positivity)
    dsimp [T]
    nlinarith
  have hdataC := mul_le_mul_of_nonneg_left hdata hC0.le
  have hInv (x : KernelSpace n) (hx : x ∈ flatClosedPatch j (r/512)) : r⁻¹ • x ∈ flatClosedPatch j (1/512) := by
    constructor
    · rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      have hh := mul_le_mul_of_nonneg_left (flat_patch_norm hx) (inv_pos.mpr hr).le
      have he : r⁻¹*(r/512)=(1:ℝ)/512 := by field_simp
      rwa [he] at hh
    · change 0 ≤ r⁻¹*x j
      exact mul_nonneg (inv_nonneg.mpr hr.le) hx.2
  have hscale (x : KernelSpace n) : Bv (r⁻¹ • x)=r^2 • B x := by
    dsimp [Bv]
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hCsup : C0*T*(r^2)⁻¹ ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg (show 0 ≤ C0*T by positivity) (Real.rpow_nonneg (inv_nonneg.mpr hr.le) α),
      mul_nonneg (show 0 ≤ C0*T*(r^2)⁻¹ by positivity) (Real.rpow_nonneg (inv_nonneg.mpr hr.le) α)]
  have hCH : C0*T*(r^2)⁻¹*(r⁻¹)^α ≤ C := by
    dsimp [C]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (by linarith : (r^2)⁻¹ ≤ 1+(r^2)⁻¹) (by positivity)
    · linarith
    · exact Real.rpow_nonneg (inv_nonneg.mpr hr.le) α
    · positivity
  constructor
  · intro x hx
    have hh := (hVs _ (hInv x hx)).trans hdataC
    rw [hscale,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] at hh
    have ht := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (sq_nonneg r))
    rw [← mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 hr.ne'),one_mul] at ht
    apply ht.trans
    have hb := mul_le_mul_of_nonneg_right hCsup hW
    nlinarith
  · intro x hx y hy
    have hh := (hVH _ (hInv x hx) _ (hInv y hy)).trans
      (mul_le_mul_of_nonneg_right hdataC (Real.rpow_nonneg (norm_nonneg _) α))
    rw [hscale,hscale,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] at hh
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),
      Real.mul_rpow (inv_nonneg.mpr hr.le) (norm_nonneg _)] at hh
    have ht := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (sq_nonneg r))
    rw [← mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 hr.ne'),one_mul] at ht
    apply ht.trans
    have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCH hW) (Real.rpow_nonneg (norm_nonneg (x-y)) α)
    nlinarith

end GaussianTilt.MomentMapSchauder
