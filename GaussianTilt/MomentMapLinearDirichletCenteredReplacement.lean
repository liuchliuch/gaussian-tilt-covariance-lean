import GaussianTilt.MomentMapLinearDirichletCenteredLoadGeometry

/-! # Constructed harmonic replacement with the actual centered forcing rate -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma replacement_square_split (n : ℕ) {lam F δ E : ℝ} (hlam : 0 < lam) :
    ((F+(n:ℝ)^2*δ*E)/lam)^2 ≤ (2/lam^2)*F^2+(2*(n:ℝ)^4/lam^2)*δ^2*E^2 := by
  rw [div_pow]
  calc
    _ ≤ (2*F^2+2*((n:ℝ)^2*δ*E)^2)/lam^2 :=
      div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (F-(n:ℝ)^2*δ*E)]) (sq_nonneg lam)
    _ = _ := by ring

/-- Genuine H₀¹ frozen replacement on a true half-ball, with the local
coefficient error and the dimensionally correct centered load rate.
The correction and its energy estimate are both constructed. -/
theorem exists_centered_halfBall_harmonic_replacement [NeZero n]
    (j : Fin n) {r β F H : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hF : 0 ≤ F) (hH : 0 ≤ H)
    (A B : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    (hBm : ∀ i k, AEStronglyMeasurable (fun x => B x i k) volume)
    {KA KB δ lam : ℝ} (hKA : 0 ≤ KA) (hKB : 0 ≤ KB) (hδ : 0 ≤ δ) (hlam : 0 < lam)
    (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ KA)
    (hBb : ∀ i k, ∀ᵐ x ∂volume, |B x i k| ≤ KB)
    (hDb : ∀ i k, ∀ᵐ x ∂volume, |B x i k-A x i k| ≤ δ)
    (hellB : ∀ᵐ x ∂volume, ∀ z : Fin n → ℝ, lam*(∑ i,(z i)^2) ≤ z ⬝ᵥ (B x *ᵥ z))
    (u : VolumeJet n) (hu : u ∈ weightedSobolev (volume : Measure (CoordinateSpace n)))
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (c : Fin n → ℝ)
    (hf : ∀ᵐ x ∂volume, x ∈ coordinateHalfBall j r → |f x| ≤ F)
    (hG : ∀ k, ∀ᵐ x ∂volume, x ∈ coordinateHalfBall j r → |G k x-c k| ≤ H*r^β)
    (heq : ∀ v : dirichletSobolev (coordinateHalfBall j r),
      variableJetEnergy A hAm hKA hAb u v.1 = variableScalarVectorLoad (coordinateHalfBall j r) f G v) :
    ∃ w : dirichletSobolev (coordinateHalfBall j r),
      (u-w.1) ∈ weightedSobolev (volume : Measure (CoordinateSpace n)) ∧
      (∀ v : dirichletSobolev (coordinateHalfBall j r), variableJetEnergy B hBm hKB hBb (u-w.1) v.1=0) ∧
      dirichletEnergy (coordinateHalfBall j r) w w ≤
        (2*(n:ℝ)^4/lam^2)*δ^2*(∫ x in coordinateHalfBall j r, ∑ i : Fin n,(u i.succ x)^2)+
        ((2/lam^2)*(2*F+(n:ℝ)*H)^2*volume.real (Metric.ball (0 : KernelSpace n) 1))*r^((n:ℝ)+2*β) := by
  let Ω := coordinateHalfBall j r
  have hΩm : MeasurableSet Ω := (isOpen_coordinateHalfBall j r).measurableSet
  have hΩb : Bornology.IsBounded Ω := isBounded_coordinateHalfBall j r
  have hfin : (volume : Measure (CoordinateSpace n)) Ω ≠ ∞ := hΩb.measure_lt_top.ne
  let L := (2*r*F+(n:ℝ)*H*r^β)*Real.sqrt (volume.real Ω)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hΦ : ∀ v : dirichletSobolev Ω, |variableScalarVectorLoad Ω f G v| ≤ L*jetGradientNorm v.1 :=
    variableScalarVectorLoad_abs_le_centered hΩm hΩb hfin j hr.le hF hH
      (fun x hx => coordinateHalfBall_strip j j hx) f G c hf hG
  obtain ⟨w,hw,hharm,hwnorm,hwE⟩ := exists_frozen_harmonic_replacement_local j hr.le
    (fun x hx => coordinateHalfBall_strip j j hx) hΩm A B hAm hBm hKA hKB hδ hlam hL
    hAb hBb hDb hellB u hu (variableScalarVectorLoad Ω f G) hΦ heq
  have hload : L^2 ≤ ((2*F+(n:ℝ)*H)^2*volume.real (Metric.ball (0 : KernelSpace n) 1))*r^((n:ℝ)+2*β) :=
    halfBall_centered_load_coefficient_sq_bound j hr hr1 hF hH hβ hβ1
  have hs := replacement_square_split n (F := L) (δ := δ)
    (E := restrictedJetGradientNorm Ω hΩm u) hlam
  have hforce := mul_le_mul_of_nonneg_left hload (show 0 ≤ 2/lam^2 by positivity)
  refine ⟨w,hw,hharm,?_⟩
  apply (hwE.trans hs).trans
  rw [restrictedJetGradientNorm_sq Ω hΩm u]
  nlinarith only [hforce]

end GaussianTilt.MomentMapLinearDirichlet
