import GaussianTilt.MomentMapLinearDirichletVariableEnergyBounds
import GaussianTilt.MomentMapLinearDirichletH1ZeroExtension

/-! # Actual domain-restricted derivative energy and localization of the weak pairing -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

def maskL2 (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (u : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) : Lp ℝ 2 (volume : Measure (CoordinateSpace n)) :=
  ((Lp.memLp u).indicator hΩ).toLp (Ω.indicator (fun x => u x))

lemma maskL2_ae (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (u : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    maskL2 Ω hΩ u =ᵐ[volume] Ω.indicator (fun x => u x) :=
  ((Lp.memLp u).indicator hΩ).coeFn_toLp

def maskVolumeJet (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω) (u : VolumeJet n) : VolumeJet n :=
  WithLp.toLp 2 (fun i => maskL2 Ω hΩ (u i))

def restrictedJetGradientNorm (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (u : VolumeJet n) : ℝ := jetGradientNorm (maskVolumeJet Ω hΩ u)

lemma restrictedJetGradientNorm_nonneg (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (u : VolumeJet n) : 0 ≤ restrictedJetGradientNorm Ω hΩ u := jetGradientNorm_nonneg _

lemma norm_maskL2_sq (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (u : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    ‖maskL2 Ω hΩ u‖^2 = ∫ x in Ω, (u x)^2 := by
  rw [maskL2, norm_toLp_sq_eq_integral]
  have he : (fun x => (Ω.indicator (fun x => u x) x)^2) = Ω.indicator (fun x => (u x)^2) := by
    funext x
    by_cases hx : x ∈ Ω <;> simp [hx]
  rw [he, integral_indicator hΩ]

/-- The restricted norm is exactly the local squared weak-gradient integral. -/
theorem restrictedJetGradientNorm_sq (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (u : VolumeJet n) :
    (restrictedJetGradientNorm Ω hΩ u)^2 = ∫ x in Ω, ∑ i : Fin n, (u i.succ x)^2 := by
  rw [restrictedJetGradientNorm, jetGradientNorm_sq]
  change (∑ i : Fin n, ‖maskL2 Ω hΩ (u i.succ)‖^2) = _
  simp_rw [norm_maskL2_sq]
  exact (integral_finset_sum _ (fun i _ => (Lp.memLp (u i.succ)).integrable_sq.restrict)).symm

/-- H₀¹ test gradients genuinely vanish outside Ω, so the original field
can be restricted inside the literal coefficient-energy pairing. -/
theorem variableJetEnergy_restrict_left
    (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K)
    (u : VolumeJet n) (v : dirichletSobolev Ω) :
    variableJetEnergy A hAm hK hAb u v.1 =
      variableJetEnergy A hAm hK hAb (maskVolumeJet Ω hΩ u) v.1 := by
  rw [variableJetEnergy_integral, variableJetEnergy_integral]
  apply integral_congr_ae
  have hz : ∀ᵐ x ∂volume, ∀ i : Fin n, x ∉ Ω → v.1 i.succ x = 0 :=
    ae_all_iff.mpr (fun i => dirichletGradient_ae_zero_outside hΩ v i)
  have hm : ∀ᵐ x ∂volume, ∀ k : Fin n,
      maskL2 Ω hΩ (u k.succ) x = Ω.indicator (fun y => u k.succ y) x :=
    ae_all_iff.mpr (fun k => maskL2_ae Ω hΩ (u k.succ))
  filter_upwards [hz, hm] with x hx hm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  change A x i k * u k.succ x * v.1 i.succ x = A x i k * maskL2 Ω hΩ (u k.succ) x * v.1 i.succ x
  rw [hm k]
  by_cases hxΩ : x ∈ Ω
  · rw [indicator_of_mem hxΩ]
  · rw [hx i hxΩ, mul_zero, mul_zero]

/-- Coefficient perturbations are controlled by the genuine local energy,
not by the ambient global H¹ norm. -/
theorem variableJetEnergy_abs_le_restricted_gradient
    (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K)
    (u : VolumeJet n) (v : dirichletSobolev Ω) :
    |variableJetEnergy A hAm hK hAb u v.1| ≤
      (n:ℝ)^2*K*restrictedJetGradientNorm Ω hΩ u*jetGradientNorm v.1 := by
  rw [variableJetEnergy_restrict_left Ω hΩ A hAm hK hAb u v]
  exact variableJetEnergy_abs_le_gradient A hAm hK hAb _ _

end GaussianTilt.MomentMapLinearDirichlet
