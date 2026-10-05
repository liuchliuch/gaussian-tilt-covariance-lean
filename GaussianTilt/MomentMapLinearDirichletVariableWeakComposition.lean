import GaussianTilt.MomentMapLinearDirichletDistribution
import GaussianTilt.EllipticRegularitySobolevTransport

/-! # Genuine bounded L² pullback from a proved measure-distortion bound

This is the completion-level primitive for nonlinear boundary charts. It
acts on actual almost-everywhere function classes and does not assume a
weak solution has classical derivatives.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet

section Composition
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} {ψ : X → Y} {C : ℝ}

lemma boundedComposition_memLp (hψ : Measurable ψ)
    (hmap : μ.map ψ≤ENNReal.ofReal (C^2) • ν) (f : Lp ℝ 2 ν) :
    MemLp (fun x=>f (ψ x)) 2 μ :=
  ((Lp.memLp f).of_measure_le_smul ENNReal.ofReal_ne_top hmap).comp_of_map hψ.aemeasurable

def boundedCompositionLinear (hψ : Measurable ψ)
    (hmap : μ.map ψ≤ENNReal.ofReal (C^2) • ν) : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (boundedComposition_memLp hψ hmap f).toLp (fun x=>f (ψ x))
  map_add' f g := by
    have hq : Measure.QuasiMeasurePreserving ψ μ ν := ⟨hψ,Measure.absolutelyContinuous_of_le_smul hmap⟩
    apply Lp.ext
    filter_upwards [(boundedComposition_memLp hψ hmap (f+g)).coeFn_toLp,
      (boundedComposition_memLp hψ hmap f).coeFn_toLp,
      (boundedComposition_memLp hψ hmap g).coeFn_toLp,
      (Lp.coeFn_add f g).comp_tendsto hq.tendsto_ae,
      Lp.coeFn_add ((boundedComposition_memLp hψ hmap f).toLp (fun x=>f (ψ x)))
        ((boundedComposition_memLp hψ hmap g).toLp (fun x=>g (ψ x)))] with x hfg hf hg hadd hsum
    simp only [Function.comp_apply,Pi.add_apply] at hadd hsum
    rw [hfg,hsum,hf,hg,hadd]
  map_smul' c f := by
    have hq : Measure.QuasiMeasurePreserving ψ μ ν := ⟨hψ,Measure.absolutelyContinuous_of_le_smul hmap⟩
    apply Lp.ext
    filter_upwards [(boundedComposition_memLp hψ hmap (c • f)).coeFn_toLp,
      (boundedComposition_memLp hψ hmap f).coeFn_toLp,
      (Lp.coeFn_smul c f).comp_tendsto hq.tendsto_ae,
      Lp.coeFn_smul c ((boundedComposition_memLp hψ hmap f).toLp (fun x=>f (ψ x)))] with x hcf hf hsm hsm'
    simp only [Function.comp_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply] at *
    rw [hcf,hsm',hf,hsm]

lemma boundedCompositionLinear_ae (hψ : Measurable ψ)
    (hmap : μ.map ψ≤ENNReal.ofReal (C^2) • ν) (f : Lp ℝ 2 ν) :
    boundedCompositionLinear hψ hmap f =ᵐ[μ] fun x=>f (ψ x) :=
  (boundedComposition_memLp hψ hmap f).coeFn_toLp

lemma norm_boundedCompositionLinear_le (hψ : Measurable ψ) (hC : 0≤C)
    (hmap : μ.map ψ≤ENNReal.ofReal (C^2) • ν) (f : Lp ℝ 2 ν) :
    ‖boundedCompositionLinear hψ hmap f‖≤C*‖f‖ := by
  have hfmap := (Lp.memLp f).of_measure_le_smul ENNReal.ofReal_ne_top hmap
  have hfscale := (Lp.memLp f).smul_measure (c:=ENNReal.ofReal (C^2)) ENNReal.ofReal_ne_top
  have hn : ‖boundedCompositionLinear hψ hmap f‖=(eLpNorm f 2 (μ.map ψ)).toReal := by
    rw [boundedCompositionLinear,LinearMap.coe_mk,AddHom.coe_mk,Lp.norm_toLp]
    exact congrArg ENNReal.toReal (eLpNorm_map_measure hfmap.aestronglyMeasurable hψ.aemeasurable).symm
  rw [hn]
  apply (ENNReal.toReal_mono hfscale.2.ne (eLpNorm_mono_measure f hmap)).trans_eq
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2:ℝ≥0∞)≠∞),smul_eq_mul,
    ENNReal.toReal_mul,← ENNReal.toReal_rpow,ENNReal.toReal_ofReal (sq_nonneg C)]
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat]
  rw [← Real.sqrt_eq_rpow,Real.sqrt_sq_eq_abs,abs_of_nonneg hC,Lp.norm_def]

/-- The actual continuous linear pullback, with a norm bound derived from
measure distortion rather than supplied as an operator premise. -/
def boundedL2Composition (hψ : Measurable ψ) (hC : 0≤C)
    (hmap : μ.map ψ≤ENNReal.ofReal (C^2) • ν) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ :=
  (boundedCompositionLinear hψ hmap).mkContinuous C (norm_boundedCompositionLinear_le hψ hC hmap)

lemma boundedL2Composition_ae (hψ : Measurable ψ) (hC : 0≤C)
    (hmap : μ.map ψ≤ENNReal.ofReal (C^2) • ν) (f : Lp ℝ 2 ν) :
    boundedL2Composition hψ hC hmap f =ᵐ[μ] fun x=>f (ψ x) :=
  boundedCompositionLinear_ae hψ hmap f

end Composition
end GaussianTilt.MomentMapLinearDirichlet
