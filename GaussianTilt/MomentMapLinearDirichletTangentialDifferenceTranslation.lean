import GaussianTilt.MomentMapLinearDirichletVariableLoads
import GaussianTilt.MomentMapLinearDirichletLocalization
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # Genuine translations of L² functions and zero-boundary Sobolev jets -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

def volumeTranslate (a : CoordinateSpace n) :
    Lp ℝ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ] Lp ℝ 2 (volume : Measure (CoordinateSpace n)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun x => x+a) (measurePreserving_add_right volume a)).toContinuousLinearMap

lemma volumeTranslate_ae (a : CoordinateSpace n) (u : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    volumeTranslate a u =ᵐ[volume] fun x => u (x+a) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume a)

@[simp] lemma norm_volumeTranslate (a : CoordinateSpace n) (u : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    ‖volumeTranslate a u‖ = ‖u‖ := Lp.norm_compMeasurePreserving u (measurePreserving_add_right volume a)

@[simp] lemma volumeTranslate_zero (u : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    volumeTranslate 0 u=u := by
  apply Lp.ext
  filter_upwards [volumeTranslate_ae 0 u] with x hx
  simpa only [add_zero] using hx

lemma continuous_volumeTranslate (u : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    Continuous (fun a : CoordinateSpace n => volumeTranslate a u) := by
  let g : C(CoordinateSpace n × CoordinateSpace n,CoordinateSpace n) :=
    ⟨fun p => p.2+p.1,continuous_snd.add continuous_fst⟩
  exact continuous_const.compMeasurePreservingLp g.curry.continuous
    (fun a => measurePreserving_add_right volume a) (by norm_num)

/-- Translating a real smooth compact function translates its actual derivatives. -/
def translateSmoothCompactCore (a : CoordinateSpace n) (u : smoothCompactCore n) : smoothCompactCore n :=
  ⟨fun x => u.1 (x+a),u.2.1.comp (contDiff_id.add contDiff_const),u.2.2.comp_homeomorph (Homeomorph.addRight a)⟩

lemma coordinateDerivative_translateSmoothCompactCore (a : CoordinateSpace n) (u : smoothCompactCore n)
    (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (translateSmoothCompactCore a u).1 x = coordinateDerivative i u.1 (x+a) := by
  have hd := ((u.2.1.differentiable (by simp) (x+a)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).add_const a)
  change fderiv ℝ (fun y => u.1 (y+a)) x (Pi.single i 1) = fderiv ℝ u.1 (x+a) (Pi.single i 1)
  simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using
    congrArg (fun L : CoordinateSpace n →L[ℝ] ℝ => L (Pi.single i 1)) hd.fderiv

lemma volumeTranslate_core (a : CoordinateSpace n) (u : smoothCompactCore n) :
    volumeTranslate a (smoothCompactToL2 volume u) = smoothCompactToL2 volume (translateSmoothCompactCore a u) := by
  apply Lp.ext
  have he := (smoothCompactToL2_ae volume u).comp_tendsto
    (measurePreserving_add_right (volume : Measure (CoordinateSpace n)) a).quasiMeasurePreserving.tendsto_ae
  filter_upwards [volumeTranslate_ae a (smoothCompactToL2 volume u),he,
    smoothCompactToL2_ae volume (translateSmoothCompactCore a u)] with x hx hu hv
  exact hx.trans (hu.trans hv.symm)

def volumeTranslateJet (a : CoordinateSpace n) : VolumeJet n →L[ℝ] VolumeJet n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1) => Lp ℝ 2 (volume : Measure (CoordinateSpace n)))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (volumeTranslate a).comp
      (PiLp.proj 2 (fun _ : Fin (n+1) => Lp ℝ 2 (volume : Measure (CoordinateSpace n))) i)))

@[simp] lemma volumeTranslateJet_apply (a : CoordinateSpace n) (u : VolumeJet n) (i : Fin (n+1)) :
    volumeTranslateJet a u i = volumeTranslate a (u i) := rfl

@[simp] lemma norm_volumeTranslateJet (a : CoordinateSpace n) (u : VolumeJet n) :
    ‖volumeTranslateJet a u‖=‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  simp only [volumeTranslateJet_apply,norm_volumeTranslate]

lemma volumeTranslateJet_core (a : CoordinateSpace n) (u : smoothCompactCore n) :
    volumeTranslateJet a (smoothCompactJet volume u) = smoothCompactJet volume (translateSmoothCompactCore a u) := by
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact volumeTranslate_core a u
  · rw [volumeTranslateJet_apply,smoothCompactJet_succ,smoothCompactJet_succ,volumeTranslate_core]
    congr 1
    apply Subtype.ext
    funext x
    exact (coordinateDerivative_translateSmoothCompactCore a u i x).symm

/-- Translation preserves the actual Dirichlet closure on the translated
domain; the statement concerns genuine L² values and weak derivative jets. -/
theorem volumeTranslateJet_mem_dirichlet {Ω : Set (CoordinateSpace n)}
    (a : CoordinateSpace n) (u : dirichletSobolev Ω) :
    volumeTranslateJet a u.1 ∈ dirichletSobolev ((fun x => x+a) ⁻¹' Ω) := by
  let U := (fun x : CoordinateSpace n => x+a) ⁻¹' Ω
  have hclosed : IsClosed ((volumeTranslateJet a) ⁻¹' (dirichletSobolev U : Set (VolumeJet n))) :=
    (LinearMap.range (dirichletJet U)).isClosed_topologicalClosure.preimage (volumeTranslateJet a).continuous
  have hcore : (LinearMap.range (dirichletJet Ω) : Set (VolumeJet n)) ⊆
      (volumeTranslateJet a) ⁻¹' (dirichletSobolev U : Set (VolumeJet n)) := by
    rintro _ ⟨v,rfl⟩
    change volumeTranslateJet a (smoothCompactJet volume v.1) ∈ dirichletSobolev U
    rw [volumeTranslateJet_core]
    apply (LinearMap.range (dirichletJet U)).le_topologicalClosure
    refine ⟨⟨translateSmoothCompactCore a v.1,?_⟩,rfl⟩
    apply closure_minimal _ (show IsClosed ((fun x => x+a) ⁻¹' tsupport v.1.1) from
      (isClosed_tsupport _).preimage (continuous_id.add continuous_const)) |>.trans (preimage_mono v.2)
    intro x hx
    exact subset_tsupport v.1.1 hx
  exact closure_minimal hcore hclosed u.2

/-- Tangential translations preserve the true zero trace on the flat
boundary, with no classical boundary differentiability assumption. -/
theorem volumeTranslateJet_mem_halfspace (q : Fin n) {a : CoordinateSpace n} (ha : a q=0)
    (u : dirichletSobolev {x : CoordinateSpace n | 0 < x q}) :
    volumeTranslateJet a u.1 ∈ dirichletSobolev {x : CoordinateSpace n | 0 < x q} := by
  have he : (fun x : CoordinateSpace n => x+a) ⁻¹' {x | 0 < x q} = {x | 0 < x q} := by
    ext x
    simp only [mem_preimage,mem_setOf_eq,Pi.add_apply,ha,add_zero]
  simpa only [he] using volumeTranslateJet_mem_dirichlet a u

end GaussianTilt.MomentMapLinearDirichlet
