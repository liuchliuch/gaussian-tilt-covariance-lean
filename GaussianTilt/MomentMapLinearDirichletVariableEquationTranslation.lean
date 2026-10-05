import GaussianTilt.MomentMapLinearDirichletVariableWeakTangentialEquation
import GaussianTilt.MomentMapLinearDirichletEuclideanWeakGradient

/-! # Exact tangential recentering of the scalar/vector weak divergence equation -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma inner_volumeTranslate_adjoint (a : CoordinateSpace n)
    (f g : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    inner ℝ (volumeTranslate a f) g=inner ℝ f (volumeTranslate (-a) g) := by
  have hleft : inner ℝ (volumeTranslate a f) g = ∫ x,f (x+a)*g x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [volumeTranslate_ae a f] with x hx
    simp only [hx,RCLike.inner_apply,conj_trivial]
    ring
  have hright : inner ℝ f (volumeTranslate (-a) g) = ∫ x,f x*g (x-a) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [volumeTranslate_ae (-a) g] with x hx
    simp only [hx,RCLike.inner_apply,conj_trivial,sub_eq_add_neg]
    ring
  rw [hleft,hright]
  have hh := integral_add_right_eq_self (μ := (volume : Measure (CoordinateSpace n))) (fun x=>f x*g (x-a)) a
  simpa only [add_sub_cancel_right] using hh

lemma variableScalarVectorLoad_translate_test {D U : Set (CoordinateSpace n)}
    (a : CoordinateSpace n) (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (v : dirichletSobolev U) (w : dirichletSobolev D) (hw : w.1=volumeTranslateJet (-a) v.1) :
    variableScalarVectorLoad D f G w=
      variableScalarVectorLoad U (volumeTranslate a f) (fun i=>volumeTranslate a (G i)) v := by
  rw [variableScalarVectorLoad_apply,variableScalarVectorLoad_apply]
  change inner ℝ f (w.1 0)+(∑i,inner ℝ (G i) (w.1 i.succ))=
    inner ℝ (volumeTranslate a f) (v.1 0)+(∑i,inner ℝ (volumeTranslate a (G i)) (v.1 i.succ))
  rw [hw]
  simp only [volumeTranslateJet_apply,inner_volumeTranslate_adjoint]

/-- Recenter the actual weak equation, including scalar and vector loads,
through genuine H₀¹ translated tests and Lebesgue invariance. -/
theorem weak_scalar_vector_equation_translate {D U : Set (CoordinateSpace n)}
    (a : CoordinateSpace n) (hshift : (fun x : CoordinateSpace n=>x-a) ⁻¹' U ⊆ D)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ i k,AEStronglyMeasurable (fun x=>A x i k) volume)
    {K : ℝ} (hK : 0 ≤ K) (hAb : ∀ i k,∀ᵐ x∂volume,|A x i k|≤K)
    (u : VolumeJet n) (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (heq : ∀ v : dirichletSobolev D, variableJetEnergy A hAm hK hAb u v.1=variableScalarVectorLoad D f G v) :
    ∀ v : dirichletSobolev U,
      variableJetEnergy (fun x=>A (x+a)) (translated_coefficient_measurable hAm a) hK
        (translated_coefficient_bound hAb a) (volumeTranslateJet a u) v.1=
      variableScalarVectorLoad U (volumeTranslate a f) (fun i=>volumeTranslate a (G i)) v := by
  intro v
  let w : dirichletSobolev D := ⟨volumeTranslateJet (-a) v.1,
    dirichletSobolev_mono (by simpa only [sub_eq_add_neg] using hshift) (volumeTranslateJet_mem_dirichlet (-a) v)⟩
  have hw : w.1=volumeTranslateJet (-a) v.1 := rfl
  have hform : variableJetEnergy (fun x=>A (x+a)) (translated_coefficient_measurable hAm a) hK
      (translated_coefficient_bound hAb a) (volumeTranslateJet a u) v.1 = variableJetEnergy A hAm hK hAb u w.1 := by
    rw [hw,variableJetEnergy_translate_test,variableJetEnergy_integral]
  rw [hform,heq w]
  exact variableScalarVectorLoad_translate_test a f G v w hw

lemma euclideanWeakGradient_volumeTranslate_ae (a : CoordinateSpace n) (u : VolumeJet n) :
    euclideanWeakGradient (volumeTranslateJet a u) =ᵐ[volume]
      (fun x=>euclideanWeakGradient u (x+(dirichletCoordinateEquiv n).symm a)) := by
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have he : ∀ᵐ y ∂(volume : Measure (CoordinateSpace n)), ∀ i : Fin n,
      volumeTranslate a (u i.succ) y=u i.succ (y+a) := ae_all_iff.mpr (fun i=>volumeTranslate_ae a (u i.succ))
  filter_upwards [hμ.quasiMeasurePreserving.ae he] with x hx
  ext i
  change volumeTranslate a (u i.succ) (dirichletCoordinateEquiv n x)=
    u i.succ (dirichletCoordinateEquiv n (x+(dirichletCoordinateEquiv n).symm a))
  rw [map_add,ContinuousLinearEquiv.apply_symm_apply]
  exact hx i

end GaussianTilt.MomentMapLinearDirichlet
