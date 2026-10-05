import GaussianTilt.MomentMapLinearDirichletTangentialDifferenceEnergy

/-! # Genuine variable-coefficient cutoff energy bounds

An actual weak load bound, tested on the constructed η²u Sobolev jet,
gives a uniform H¹ bound for ηu. The constants use only the coefficient
ellipticity/bound, the cutoff, the load bound and the L² value norm.
-/
noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma norm_volumeJet_le_value_add_gradient (u : VolumeJet n) :
    ‖u‖≤‖u 0‖+jetGradientNorm u := by
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (jetGradientNorm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succ,← jetGradientNorm_sq]
  nlinarith [norm_nonneg (u 0),jetGradientNorm_nonneg u]

lemma nonneg_quadratic_bound {x lam P Q : ℝ} (_hx : 0≤x) (hlam : 0<lam)
    (hP : 0≤P) (hQ : 0≤Q) (h : lam*x^2≤P*x+Q) :
    x≤1+(P+Q)/lam := by
  by_contra hn
  have hlarge : 1+(P+Q)/lam<x := lt_of_not_ge hn
  have hx1 : 1<x := lt_of_le_of_lt (le_add_of_nonneg_right (div_nonneg (add_nonneg hP hQ) hlam.le)) hlarge
  have hdiv : (P+Q)/lam<x := by linarith
  have hlin : P+Q<x*lam := (div_lt_iff₀ hlam).mp hdiv
  have hmul := mul_lt_mul_of_pos_right hlin (lt_trans zero_lt_one hx1)
  have hQx : Q≤Q*x := by nlinarith
  nlinarith

/-- This constant is deliberately coarse and depends only on the actual
lower-order data. It is independent of any difference-quotient step. -/
def cutoffEnergyBound (n : ℕ) (lam K B D L W : ℝ) : ℝ :=
  B*W+1+((L*(n:ℝ)*B+2*((n:ℝ)^2*K)*((n:ℝ)*D*W))+
    (L*(n:ℝ)*D*(B*W)+((n:ℝ)^2*K)*((n:ℝ)*D*W)^2))/lam

lemma cutoffEnergyBound_nonneg {lam K B D L W : ℝ} (hlam : 0≤lam)
    (hK : 0≤K) (hB : 0≤B) (hD : 0≤D) (hL : 0≤L) (hW : 0≤W) :
    0≤cutoffEnergyBound n lam K B D L W := by unfold cutoffEnergyBound; positivity

/-- The genuine η² Sobolev test yields a quantitative local H¹ bound for
an arbitrary rough jet satisfying the literal weak energy load estimate.
Neither differentiability nor a priori second derivatives are supplied. -/
theorem norm_cutoff_jet_le_of_weak_load_bound {Ω U : Set (CoordinateSpace n)}
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k, AEStronglyMeasurable (fun x=>A x i k) volume)
    {K lam : ℝ} (hK : 0≤K) (hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k|≤K) (hlam : 0<lam)
    (hell : ∀ᵐ x ∂volume, ∀ z : Fin n→ℝ, lam*(∑ i,(z i)^2)≤z ⬝ᵥ (A x *ᵥ z))
    (a : smoothCompactCore n) (ha : tsupport a.1 ∩ Ω⊆U)
    {B D L W : ℝ} (hB : 0≤B) (hD : 0≤D) (hL : 0≤L) (hW : 0≤W)
    (hb : ∀ x, |a.1 x|≤B) (hd : ∀ i x, |coordinateDerivative i a.1 x|≤D)
    (u : dirichletSobolev Ω) (hu : ‖u.1 0‖≤W)
    (hload : ∀ v : dirichletSobolev U,
      |variableJetEnergy A hAm hK hAb u.1 v.1|≤L*jetGradientNorm v.1) :
    ‖smoothCoreJetMultiply a u.1‖≤cutoffEnergyBound n lam K B D L W := by
  let v : dirichletSobolev U := dirichletSmoothMultiply a ha u
  let ψ : dirichletSobolev U := dirichletSmoothMultiply a (fun _ hx=>hx.2) v
  let E := variableJetEnergy A hAm hK hAb
  let R := cutoffErrorJet a u.1
  let G := jetGradientNorm v.1
  let Z := (n:ℝ)*D*W
  let C := (n:ℝ)^2*K
  have hG : 0≤G := jetGradientNorm_nonneg _
  have hZ : 0≤Z := by dsimp [Z]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  have hvval : ‖v.1 0‖≤B*W :=
    (norm_smoothCoreL2Multiply_le a hb _).trans (mul_le_mul_of_nonneg_left hu hB)
  have hR : jetGradientNorm R≤Z := (jetGradientNorm_cutoffError_le a hd u.1).trans
    (mul_le_mul_of_nonneg_left hu (by positivity))
  have hψ : jetGradientNorm ψ.1≤(n:ℝ)*(B*G+D*(B*W)) := by
    apply (jetGradientNorm_smoothCoreJetMultiply_le a hB hb hd v.1).trans
    exact mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_left hvval hD) _) (Nat.cast_nonneg n)
  have hforce : E u.1 ψ.1≤L*((n:ℝ)*(B*G+D*(B*W))) :=
    (le_abs_self _).trans ((hload ψ).trans (mul_le_mul_of_nonneg_left hψ hL))
  have hRV : E R v.1≤C*Z*G := (le_abs_self _).trans
    ((variableJetEnergy_abs_le_gradient A hAm hK hAb R v.1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR hC) hG))
  have hVR : -(E v.1 R)≤C*G*Z := (neg_le_abs _).trans
    ((variableJetEnergy_abs_le_gradient A hAm hK hAb v.1 R).trans
      (mul_le_mul_of_nonneg_left hR (mul_nonneg hC hG)))
  have hRR : E R R≤C*Z^2 := (le_abs_self _).trans
    ((variableJetEnergy_abs_le_gradient A hAm hK hAb R R).trans (by
      have hh := pow_le_pow_left₀ (jetGradientNorm_nonneg R) hR 2
      nlinarith [mul_le_mul_of_nonneg_left hh hC]))
  have hellv : lam*G^2≤E v.1 v.1 := by
    simpa only [dirichletEnergy_eq_gradientNorm_sq] using
      variableDirichletEnergy_lower U A hAm hK hAb hell v
  have hid : E v.1 v.1=E u.1 ψ.1+E R v.1-E v.1 R+E R R :=
    variableJetEnergy_cutoff_identity A hAm hK hAb a u.1
  let P := L*(n:ℝ)*B+2*C*Z
  let Q := L*(n:ℝ)*D*(B*W)+C*Z^2
  have hP : 0≤P := by dsimp [P]; positivity
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hquad : lam*G^2≤P*G+Q := by
    dsimp only [P,Q]
    nlinarith
  have hgrad := nonneg_quadratic_bound hG hlam hP hQ hquad
  have hn := norm_volumeJet_le_value_add_gradient v.1
  change ‖v.1‖≤_
  change ‖v.1‖≤B*W+1+(P+Q)/lam
  linarith

end GaussianTilt.MomentMapLinearDirichlet
