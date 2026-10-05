import GaussianTilt.MomentMapLinearDirichletCenteredReplacement

/-! # Honest localization of frozen coefficient differences to the test domain -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

noncomputable def localFrozenCoefficient (Ω : Set (CoordinateSpace n))
    (A B : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) :
    CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun x => if x ∈ Ω then A x else B x

lemma localFrozenCoefficient_measurable {Ω : Set (CoordinateSpace n)} (hΩ : MeasurableSet Ω)
    (A B : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    (hBm : ∀ i k, AEStronglyMeasurable (fun x => B x i k) volume) :
    ∀ i k, AEStronglyMeasurable (fun x => localFrozenCoefficient Ω A B x i k) volume := by
  classical
  intro i k
  have he : (fun x => localFrozenCoefficient Ω A B x i k) =
      Ω.piecewise (fun x => A x i k) (fun x => B x i k) := by
    funext x
    by_cases hx : x ∈ Ω <;> simp [localFrozenCoefficient,hx]
  rw [he]
  exact AEStronglyMeasurable.piecewise hΩ (hAm i k).restrict (hBm i k).restrict

lemma localFrozenCoefficient_bound {Ω : Set (CoordinateSpace n)}
    (A B : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) {KA KB : ℝ}
    (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ KA)
    (hBb : ∀ i k, ∀ᵐ x ∂volume, |B x i k| ≤ KB) :
    ∀ i k, ∀ᵐ x ∂volume, |localFrozenCoefficient Ω A B x i k| ≤ max KA KB := by
  intro i k
  filter_upwards [hAb i k,hBb i k] with x hx hy
  by_cases hxΩ : x ∈ Ω
  · simpa only [localFrozenCoefficient,if_pos hxΩ] using hx.trans (le_max_left KA KB)
  · simpa only [localFrozenCoefficient,if_neg hxΩ] using hy.trans (le_max_right KA KB)

lemma localFrozenCoefficient_difference {Ω : Set (CoordinateSpace n)}
    (A B : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hDb : ∀ i k, ∀ᵐ x ∂volume, x ∈ Ω → |B x i k-A x i k| ≤ δ) :
    ∀ i k, ∀ᵐ x ∂volume, |B x i k-localFrozenCoefficient Ω A B x i k| ≤ δ := by
  intro i k
  filter_upwards [hDb i k] with x hx
  by_cases hxΩ : x ∈ Ω
  · simpa only [localFrozenCoefficient,if_pos hxΩ] using hx hxΩ
  · simpa only [localFrozenCoefficient,if_neg hxΩ,sub_self,abs_zero] using hδ

/-- Extending A by the frozen coefficient outside Ω leaves the actual
H₀¹ weak equation unchanged, since its genuine test gradients vanish there. -/
theorem variableJetEnergy_localFrozenCoefficient_eq {Ω : Set (CoordinateSpace n)}
    (hΩ : MeasurableSet Ω) (A B : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    (hBm : ∀ i k, AEStronglyMeasurable (fun x => B x i k) volume)
    {KA KB : ℝ} (hKA : 0 ≤ KA) (hKB : 0 ≤ KB)
    (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ KA)
    (hBb : ∀ i k, ∀ᵐ x ∂volume, |B x i k| ≤ KB)
    (u : VolumeJet n) (v : dirichletSobolev Ω) :
    variableJetEnergy (localFrozenCoefficient Ω A B)
      (localFrozenCoefficient_measurable hΩ A B hAm hBm) (le_trans hKA (le_max_left KA KB))
      (localFrozenCoefficient_bound A B hAb hBb) u v.1 = variableJetEnergy A hAm hKA hAb u v.1 := by
  rw [variableJetEnergy_integral,variableJetEnergy_integral]
  apply integral_congr_ae
  have hz : ∀ᵐ x ∂volume, ∀ i : Fin n, x ∉ Ω → v.1 i.succ x=0 :=
    ae_all_iff.mpr (fun i => dirichletGradient_ae_zero_outside hΩ v i)
  filter_upwards [hz] with x hx
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hxΩ : x ∈ Ω
  · simp only [localFrozenCoefficient,if_pos hxΩ]
  · rw [hx i hxΩ,mul_zero,mul_zero]

/-- The actual centered replacement only requires coefficient oscillation inside the half-ball. -/
theorem exists_local_centered_halfBall_harmonic_replacement [NeZero n]
    (j : Fin n) {r β F H : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hF : 0 ≤ F) (hH : 0 ≤ H)
    (A B : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    (hBm : ∀ i k, AEStronglyMeasurable (fun x => B x i k) volume)
    {KA KB δ lam : ℝ} (hKA : 0 ≤ KA) (hKB : 0 ≤ KB) (hδ : 0 ≤ δ) (hlam : 0 < lam)
    (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ KA)
    (hBb : ∀ i k, ∀ᵐ x ∂volume, |B x i k| ≤ KB)
    (hDb : ∀ i k, ∀ᵐ x ∂volume, x ∈ coordinateHalfBall j r → |B x i k-A x i k| ≤ δ)
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
  have hΩ : MeasurableSet Ω := (isOpen_coordinateHalfBall j r).measurableSet
  have hLA := localFrozenCoefficient_measurable hΩ A B hAm hBm
  have hLB := localFrozenCoefficient_bound (Ω := Ω) A B hAb hBb
  have hLD := localFrozenCoefficient_difference (Ω := Ω) A B hδ hDb
  have hLK : 0 ≤ max KA KB := hKA.trans (le_max_left _ _)
  apply exists_centered_halfBall_harmonic_replacement j hr hr1 hβ hβ1 hF hH
    (localFrozenCoefficient Ω A B) B hLA hBm hLK hKB hδ hlam hLB hBb hLD hellB
    u hu f G c hf hG
  intro v
  exact (variableJetEnergy_localFrozenCoefficient_eq hΩ A B hAm hBm hKA hKB hAb hBb u v).trans (heq v)

end GaussianTilt.MomentMapLinearDirichlet
