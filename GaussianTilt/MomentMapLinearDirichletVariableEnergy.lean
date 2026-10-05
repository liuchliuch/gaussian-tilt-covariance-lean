import GaussianTilt.MomentMapLinearDirichletWeak
import GaussianTilt.EllipticRegularitySobolevProduct

/-! # Literal measurable-coefficient Dirichlet energy as a bounded bilinear form -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

abbrev VolumeJet (n : ℕ) := SobolevJet (volume : Measure (CoordinateSpace n))

def volumeJetDerivative (i : Fin n) : VolumeJet n →L[ℝ] Lp ℝ 2 (volume : Measure (CoordinateSpace n)) :=
  PiLp.proj 2 (fun _ : Fin (n+1) => Lp ℝ 2 (volume : Measure (CoordinateSpace n))) i.succ

/-- Actual coefficient multiplication on each L² derivative coordinate,
followed by its genuine Hilbert pairing. -/
def variableJetEnergy (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K) :
    VolumeJet n →L[ℝ] VolumeJet n →L[ℝ] ℝ :=
  ∑ i, ∑ k, (innerSL ℝ : Lp ℝ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ] ℝ).bilinearComp
    ((boundedL2Multiplier (hAm i k) hK (hAb i k)).comp (volumeJetDerivative k)) (volumeJetDerivative i)

def variableDirichletEnergy (Ω : Set (CoordinateSpace n))
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K) :
    dirichletSobolev Ω →L[ℝ] dirichletSobolev Ω →L[ℝ] ℝ :=
  (variableJetEnergy A hAm hK hAb).bilinearComp (dirichletSobolev Ω).subtypeL (dirichletSobolev Ω).subtypeL

lemma integrable_variable_energy_entry (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K)
    (u v : VolumeJet n) (i k : Fin n) :
    Integrable (fun x => A x i k * u k.succ x * v i.succ x) volume := by
  have hi := (boundedMultiplier_memLp (hAm i k) (hAb i k) (u k.succ)).integrable_mul (Lp.memLp (v i.succ))
  exact hi

lemma variableJetEnergy_entry (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K)
    (u v : VolumeJet n) (i k : Fin n) :
    inner ℝ (boundedL2Multiplier (hAm i k) hK (hAb i k) (u k.succ)) (v i.succ) =
      ∫ x, A x i k * u k.succ x * v i.succ x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedL2Multiplier_ae (hAm i k) hK (hAb i k) (u k.succ)] with x hx
  simp only [RCLike.inner_apply, conj_trivial, hx]
  ring

/-- The bounded form is exactly the actual divergence energy integral. -/
theorem variableJetEnergy_integral (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K)
    (u v : VolumeJet n) :
    variableJetEnergy A hAm hK hAb u v = ∫ x, ∑ i : Fin n, ∑ k : Fin n,
      A x i k * u k.succ x * v i.succ x := by
  simp only [variableJetEnergy, ContinuousLinearMap.sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.comp_apply, volumeJetDerivative, PiLp.proj_apply, innerSL_apply]
  simp_rw [variableJetEnergy_entry A hAm hK hAb]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun k _ =>
    integrable_variable_energy_entry A hAm hK hAb u v i k))]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_finset_sum _ (fun k _ => integrable_variable_energy_entry A hAm hK hAb u v i k)).symm

lemma dirichletEnergy_integral (Ω : Set (CoordinateSpace n)) (u : dirichletSobolev Ω) :
    dirichletEnergy Ω u u = ∫ x, ∑ i : Fin n, (u.1 i.succ x)^2 := by
  rw [dirichletEnergy_apply]
  simp only [L2.inner_def, RCLike.inner_apply, conj_trivial, ← pow_two]
  exact (integral_finset_sum _ (fun (i : Fin n) _ => (Lp.memLp (u.1 i.succ)).integrable_sq)).symm

/-- Pointwise measurable ellipticity yields the genuine integral coercive
bound on the constructed Sobolev graph. -/
theorem variableDirichletEnergy_lower
    (Ω : Set (CoordinateSpace n)) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K lam : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K)
    (hell : ∀ᵐ x ∂volume, ∀ z : Fin n → ℝ, lam * (∑ i, (z i)^2) ≤ z ⬝ᵥ (A x *ᵥ z))
    (u : dirichletSobolev Ω) :
    lam * dirichletEnergy Ω u u ≤ variableDirichletEnergy Ω A hAm hK hAb u u := by
  change lam * dirichletEnergy Ω u u ≤ variableJetEnergy A hAm hK hAb u.1 u.1
  rw [variableJetEnergy_integral, dirichletEnergy_integral, ← integral_const_mul]
  apply integral_mono_ae
  · exact (integrable_finset_sum _ (fun (i : Fin n) _ => (Lp.memLp (u.1 i.succ)).integrable_sq)).const_mul lam
  · exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun k _ =>
      integrable_variable_energy_entry A hAm hK hAb u.1 u.1 i k))
  · filter_upwards [hell] with x hx
    have h := hx (fun i => u.1 i.succ x)
    convert h using 1
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- The actual variable energy is coercive by ellipticity and the proved
bounded-domain Poincaré estimate. -/
theorem variableDirichletEnergy_isCoercive
    {Ω : Set (CoordinateSpace n)} (i : Fin n) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume)
    {K lam : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ K) (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, ∀ z : Fin n → ℝ, lam * (∑ i, (z i)^2) ≤ z ⬝ᵥ (A x *ᵥ z)) :
    IsCoercive (variableDirichletEnergy Ω A hAm hK hAb) := by
  have hden : 0 < 1+4*R^2 := by positivity
  refine ⟨lam/(1+4*R^2), div_pos hlam hden, ?_⟩
  intro u
  have hb := dirichlet_norm_sq_le_energy i hR hΩ u
  have he := variableDirichletEnergy_lower Ω A hAm hK hAb hell u
  have hs := mul_le_mul_of_nonneg_left hb (div_nonneg hlam.le hden.le)
  have hid : (lam/(1+4*R^2))*((1+4*R^2)*dirichletEnergy Ω u u) = lam*dirichletEnergy Ω u u := by field_simp
  rw [hid] at hs
  nlinarith

end GaussianTilt.MomentMapLinearDirichlet
