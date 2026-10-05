import GaussianTilt.MomentMapLinearDirichletTangentialDifferenceCutoff

/-! # Actual cutoff-energy algebra for rough variable-coefficient jets

The commutator identities below hold for literal L² multipliers and
Sobolev product-rule jets. They require no classical derivative of the
unknown, and no symmetry of the measurable coefficient matrix.
-/
noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma smoothCoreL2Multiply_comm (a b : smoothCompactCore n)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    smoothCoreL2Multiply a (smoothCoreL2Multiply b f) =
      smoothCoreL2Multiply b (smoothCoreL2Multiply a f) := by
  apply Lp.ext
  filter_upwards [smoothCoreL2Multiply_ae a (smoothCoreL2Multiply b f),
    smoothCoreL2Multiply_ae b f,smoothCoreL2Multiply_ae b (smoothCoreL2Multiply a f),
    smoothCoreL2Multiply_ae a f] with x h₁ h₂ h₃ h₄
  rw [h₁,h₂,h₃,h₄]
  ring

lemma norm_smoothCoreL2Multiply_le (a : smoothCompactCore n) {B : ℝ}
    (hb : ∀ x, |a.1 x|≤B) (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    ‖smoothCoreL2Multiply a f‖≤B*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [smoothCoreL2Multiply_ae a f] with x hx
  rw [hx,norm_mul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

lemma jetGradientNorm_le_sum (u : VolumeJet n) :
    jetGradientNorm u ≤ ∑ i : Fin n, ‖u i.succ‖ := by
  apply (sq_le_sq₀ (jetGradientNorm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).mp
  rw [jetGradientNorm_sq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _=>norm_nonneg _)

/-- Multiplication of each L² jet coordinate; unlike the product-rule map,
this auxiliary operator is not asserted to preserve compatible jets. -/
def scalarJetMultiply (a : smoothCompactCore n) : VolumeJet n →L[ℝ] VolumeJet n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1)=>Lp ℝ 2 (volume : Measure (CoordinateSpace n)))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i=>(smoothCoreL2Multiply a).comp
      (PiLp.proj 2 (fun _ : Fin (n+1)=>Lp ℝ 2 (volume : Measure (CoordinateSpace n))) i)))

@[simp] lemma scalarJetMultiply_apply (a : smoothCompactCore n) (u : VolumeJet n) (i : Fin (n+1)) :
    scalarJetMultiply a u i=smoothCoreL2Multiply a (u i) := rfl

/-- The actual cutoff derivative error has zero value coordinate. -/
def cutoffErrorJet (a : smoothCompactCore n) : VolumeJet n →L[ℝ] VolumeJet n :=
  smoothCoreJetMultiply a-scalarJetMultiply a

@[simp] lemma cutoffErrorJet_zero (a : smoothCompactCore n) (u : VolumeJet n) :
    cutoffErrorJet a u 0=0 := by
  change smoothCoreL2Multiply a (u 0)-smoothCoreL2Multiply a (u 0)=0
  exact sub_self _

@[simp] lemma cutoffErrorJet_succ (a : smoothCompactCore n) (u : VolumeJet n) (i : Fin n) :
    cutoffErrorJet a u i.succ=smoothCoreL2Multiply (smoothCompactDerivative i a) (u 0) := by
  change (smoothCoreL2Multiply a (u i.succ)+smoothCoreL2Multiply (smoothCompactDerivative i a) (u 0))-
    smoothCoreL2Multiply a (u i.succ)=_
  abel

lemma smoothCoreJetMultiply_eq (a : smoothCompactCore n) (u : VolumeJet n) :
    smoothCoreJetMultiply a u = scalarJetMultiply a u+cutoffErrorJet a u := by
  simp only [cutoffErrorJet,ContinuousLinearMap.sub_apply]
  abel

lemma cutoffErrorJet_mul (a : smoothCompactCore n) (u : VolumeJet n) :
    cutoffErrorJet a (smoothCoreJetMultiply a u)=scalarJetMultiply a (cutoffErrorJet a u) := by
  apply PiLp.ext
  intro k
  refine Fin.cases ?_ (fun i=>?_) k
  · simp
  · simp only [cutoffErrorJet_succ,smoothCoreJetMultiply_zero,scalarJetMultiply_apply]
    exact smoothCoreL2Multiply_comm _ _ _

lemma smoothCoreJetMultiply_twice (a : smoothCompactCore n) (u : VolumeJet n) :
    smoothCoreJetMultiply a (smoothCoreJetMultiply a u)=
      scalarJetMultiply a (smoothCoreJetMultiply a u)+scalarJetMultiply a (cutoffErrorJet a u) := by
  rw [smoothCoreJetMultiply_eq a (smoothCoreJetMultiply a u),cutoffErrorJet_mul]

lemma jetGradientNorm_cutoffError_le (a : smoothCompactCore n) {D : ℝ}
    (hd : ∀ i x, |coordinateDerivative i a.1 x|≤D) (u : VolumeJet n) :
    jetGradientNorm (cutoffErrorJet a u)≤(n:ℝ)*D*‖u 0‖ := by
  apply (jetGradientNorm_le_sum _).trans
  calc
    _ ≤ ∑ _i : Fin n, D*‖u 0‖ := Finset.sum_le_sum (fun i _=>by
      rw [cutoffErrorJet_succ]
      exact norm_smoothCoreL2Multiply_le _ (hd i) _)
    _ = _ := by simp; ring

lemma jetGradientNorm_smoothCoreJetMultiply_le (a : smoothCompactCore n) {B D : ℝ}
    (hB : 0≤B) (hb : ∀ x, |a.1 x|≤B) (hd : ∀ i x, |coordinateDerivative i a.1 x|≤D)
    (u : VolumeJet n) :
    jetGradientNorm (smoothCoreJetMultiply a u) ≤
      (n:ℝ)*(B*jetGradientNorm u+D*‖u 0‖) := by
  apply (jetGradientNorm_le_sum _).trans
  calc
    _ ≤ ∑ _i : Fin n, (B*jetGradientNorm u+D*‖u 0‖) := Finset.sum_le_sum (fun i _=>by
      rw [smoothCoreJetMultiply_succ]
      apply (norm_add_le _ _).trans
      exact add_le_add ((norm_smoothCoreL2Multiply_le a hb _).trans
        (mul_le_mul_of_nonneg_left (norm_jetDerivative_le_gradient u i) hB))
        (norm_smoothCoreL2Multiply_le _ (hd i) _))
    _ = _ := by simp; ring

/-- Scalar multiplication commutes through the literal variable energy
pairing, including for nonsymmetric measurable coefficients. -/
lemma variableJetEnergy_scalar_transfer
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x=>A x i k) volume)
    {K : ℝ} (hK : 0≤K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k|≤K)
    (a : smoothCompactCore n) (u v : VolumeJet n) :
    variableJetEnergy A hAm hK hAb (scalarJetMultiply a u) v=
      variableJetEnergy A hAm hK hAb u (scalarJetMultiply a v) := by
  rw [variableJetEnergy_integral,variableJetEnergy_integral]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun i : Fin n=>smoothCoreL2Multiply_ae a (u i.succ)),
    ae_all_iff.mpr (fun i : Fin n=>smoothCoreL2Multiply_ae a (v i.succ))] with x hu hv
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simp only [scalarJetMultiply_apply,hu k,hv i]
  ring

/-- Exact η²-test commutator identity on actual rough Sobolev jets. -/
theorem variableJetEnergy_cutoff_identity
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x=>A x i k) volume)
    {K : ℝ} (hK : 0≤K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k|≤K)
    (a : smoothCompactCore n) (u : VolumeJet n) :
    variableJetEnergy A hAm hK hAb (smoothCoreJetMultiply a u) (smoothCoreJetMultiply a u)=
      variableJetEnergy A hAm hK hAb u (smoothCoreJetMultiply a (smoothCoreJetMultiply a u))+
      variableJetEnergy A hAm hK hAb (cutoffErrorJet a u) (smoothCoreJetMultiply a u)-
      variableJetEnergy A hAm hK hAb (smoothCoreJetMultiply a u) (cutoffErrorJet a u)+
      variableJetEnergy A hAm hK hAb (cutoffErrorJet a u) (cutoffErrorJet a u) := by
  let E := variableJetEnergy A hAm hK hAb
  let T := smoothCoreJetMultiply a
  let M := scalarJetMultiply a
  let R := cutoffErrorJet a
  have h₁ : E u (T (T u))=E (M u) (T u)+E (M u) (R u) := by
    rw [show T (T u)=M (T u)+M (R u) from smoothCoreJetMultiply_twice a u,map_add]
    rw [← variableJetEnergy_scalar_transfer A hAm hK hAb a u (T u),
      ← variableJetEnergy_scalar_transfer A hAm hK hAb a u (R u)]
  have h₂ : T u=M u+R u := smoothCoreJetMultiply_eq a u
  change E (T u) (T u)=E u (T (T u))+E (R u) (T u)-E (T u) (R u)+E (R u) (R u)
  rw [h₁,h₂]
  simp only [map_add,ContinuousLinearMap.add_apply]
  ring

end GaussianTilt.MomentMapLinearDirichlet
