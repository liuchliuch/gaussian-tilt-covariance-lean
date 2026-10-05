import GaussianTilt.MomentMapLinearDirichletInteriorRadiusInterpolation
import GaussianTilt.MomentMapLinearDirichletVariableWeakAffineSubtractionHolder

/-! # Genuine interior Campanato decay from a boundary affine starting error -/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma centered_affine_load_error_bound (A B : Matrix (Fin n) (Fin n) ℝ)
    (g c : Fin n → ℝ) (p : KernelSpace n) {D H d : ℝ} (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hA : ∀ i k, |A i k-B i k| ≤ D*d) (hg : ∀ i, |g i-c i| ≤ H*d) :
    ∀ i, |(g i-∑ k,A i k*p k)-(c i-∑ k,B i k*p k)| ≤ (H+(n:ℝ)*D*‖p‖)*d := by
  intro i
  have he : (g i-∑ k,A i k*p k)-(c i-∑ k,B i k*p k) = (g i-c i)-∑ k,(A i k-B i k)*p k := by
    simp only [sub_mul,Finset.sum_sub_distrib]; ring
  rw [he]
  have hs : |∑ k,(A i k-B i k)*p k| ≤ (n:ℝ)*(D*d)*‖p‖ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ k : Fin n,(D*d)*‖p‖ := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul (hA i k) (PiLp.norm_apply_le p k) (abs_nonneg _) (mul_nonneg hD hd)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
  exact (abs_sub _ _).trans ((add_le_add (hg i) hs).trans_eq (by ring))

lemma ballGradientExcess_le_of_local_affine_gradient {u v : VolumeJet n} (a p : KernelSpace n)
    {r R : ℝ} (hrR : r ≤ R)
    (hgrad : ∀ᵐ x ∂volume,x∈Metric.ball a R → euclideanWeakGradient v x=euclideanWeakGradient u x-p) :
    ballGradientExcess u a r ≤ ballGradientExcess v a r := by
  apply (ballGradientExcess_le_error u a r (p+ballMeanGradient v a r)).trans_eq
  apply setIntegral_congr_ae Metric.isOpen_ball.measurableSet
  filter_upwards [hgrad] with x hx hxr
  rw [hx (Metric.ball_subset_ball hrR hxr)]
  congr 2
  abel

/-- The interior PDE iteration is applied to an actually constructed
compact affine subtraction. Its final constant is uniform in the center
and initial height scale, and its initial error remains a literal integral. -/
theorem exists_affine_start_interior_campanato [NeZero n]
    {lam Λ D β : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ ρ C N : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < C ∧ 0 < N ∧
      ∀ (a p : KernelSpace n) (R M L : ℝ), 0 < R → R ≤ 1 → 0 ≤ M → 0 ≤ L → ‖p‖≤L →
      ∀ (Ω : Set (CoordinateSpace n)) (u : dirichletSobolev Ω), coordinateFullBall a (2*R) ⊆ Ω →
      (∫ x in Metric.ball a R, ‖euclideanWeakGradient u.1 x-p‖^2) ≤ M*R^((n:ℝ)+β) →
      ∀ (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ), B.PosDef →
      (∀ v : KernelSpace n,lam*‖v‖^2≤euclideanQuadratic B v) →
      (∀ v : KernelSpace n,euclideanQuadratic B v≤Λ*‖v‖^2) →
      ∀ hAm : ∀ i k,AEStronglyMeasurable (fun x=>A x i k) volume,
      ∀ KA : ℝ,∀ hKA : 0≤KA,∀ hAb : ∀ i k,∀ᵐ x∂volume,|A x i k|≤KA,
      (∀ i k,∀ᵐ x∂volume,x∈coordinateFullBall a R → |B i k-A x i k|≤D*‖(dirichletCoordinateEquiv n).symm x-a‖^β) →
      ∀ F H : ℝ,0≤F → 0≤H →
      ∀ (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
        (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (c : Fin n→ℝ),
      (∀ᵐ x∂volume,x∈coordinateFullBall a R → |f x|≤F) →
      (∀ k,∀ᵐ x∂volume,x∈coordinateFullBall a R → |G k x-c k|≤H*‖(dirichletCoordinateEquiv n).symm x-a‖^β) →
      (∀ v : dirichletSobolev (coordinateFullBall a R),variableJetEnergy A hAm hKA hAb u.1 v.1=
        variableScalarVectorLoad (coordinateFullBall a R) f G v) →
      ∀ r : ℝ,0<r → r≤ρ*R → ballGradientExcess u.1 a r ≤
        C*(M+N*(2*F+(n:ℝ)*(H+(n:ℝ)*D*L))^2)*r^((n:ℝ)+β) := by
  obtain ⟨ρ,θ,C,N,hρ,hρ1,hθ,hθ2,hC,hN,hIter⟩ := exists_variable_ball_campanato_bound (n := n) hlam hΛ hD hβ hβ1
  let C' := C*θ^(-((n:ℝ)+β))
  have hC' : 0 < C' := mul_pos hC (Real.rpow_pos_of_pos hθ _)
  refine ⟨ρ,C',N,hρ,hρ1,hC',hN,?_⟩
  intro a p R M L hR hR1 hM hL hp Ω u hDomain hInitial A B hB hlo hhi hAm KA hKA hAb hDb F H hF hH f G c hf hG heq
  obtain ⟨v,G',hv0,hvD,hvE,hG',heq'⟩ := exists_dirichlet_affine_subtraction_equation a p hR hDomain A hAm hKA hAb u f G heq
  let H' := H+(n:ℝ)*D*L
  let c' := fun i => c i-∑ k,B i k*p k
  have hH' : 0 ≤ H' := by dsimp [H']; positivity
  have hGbound : ∀ i,∀ᵐ x∂volume,x∈coordinateFullBall a R →
      |G' i x-c' i|≤H'*‖(dirichletCoordinateEquiv n).symm x-a‖^β := by
    intro i
    have hDA := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hDb i))
    have hGG := ae_all_iff.mpr hG
    filter_upwards [hG' i,hDA,hGG] with x hx hdx hgx hxR
    rw [hx hxR]
    have hd : 0 ≤ ‖(dirichletCoordinateEquiv n).symm x-a‖^β := Real.rpow_nonneg (norm_nonneg _) _
    have hb := centered_affine_load_error_bound (A x) B (fun i=>G i x) c p hD hd
      (fun i k => by simpa only [abs_sub_comm] using hdx i k hxR) (fun i=>hgx i hxR) i
    apply hb.trans
    exact mul_le_mul_of_nonneg_right (by dsimp [H']; nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (n:ℝ)*D)]) hd
  have hsub : coordinateFullBall a R ⊆ Ω := (coordinateFullBall_mono (by linarith : R≤2*R)).trans hDomain
  have hGeom := hIter a R hR hR1 Ω v hsub A B hB hlo hhi hAm KA hKA hAb hDb F H' hF hH' f G' c' hf hGbound heq'
  have hInit : ballGradientEnergy v.1 a R ≤ M*R^((n:ℝ)+β) := by
    have he : ballGradientEnergy v.1 a R = ∫ x in Metric.ball a R, ‖euclideanWeakGradient u.1 x-p‖^2 := by
      apply setIntegral_congr_ae Metric.isOpen_ball.measurableSet
      filter_upwards [hvE] with x hx hxr
      rw [hx hxr]
    rwa [he]
  have hAll := ballGradientExcess_all_radii_of_scale_bound v.1 a hR hR1 hρ hθ
    (hθ2.trans_lt (by norm_num)) hC.le hM (by positivity : 0≤N*(2*F+(n:ℝ)*H')^2) hβ.le hInit hGeom
  intro r hr hrr
  have hrR : r≤R := hrr.trans (by nlinarith)
  apply (ballGradientExcess_le_of_local_affine_gradient a p hrR hvE).trans
  exact hAll r hr (by nlinarith)

end GaussianTilt.MomentMapLinearDirichlet
