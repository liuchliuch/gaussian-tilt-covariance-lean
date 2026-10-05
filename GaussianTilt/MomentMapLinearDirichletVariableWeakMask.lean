import GaussianTilt.MomentMapLinearDirichletVariableWeakJacobian

/-! # Actual zero extension and localized L² chart pullback -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
section Mask
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {S : Set X}

lemma zeroExtend_memLp (hS : MeasurableSet S) (f : Lp ℝ 2 (μ.restrict S)) :
    MemLp (S.indicator (fun x=>f x)) 2 μ :=
  (memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)

def zeroExtendL2Linear (hS : MeasurableSet S) : Lp ℝ 2 (μ.restrict S) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (zeroExtend_memLp hS f).toLp (S.indicator (fun x=>f x))
  map_add' f g := by
    have hadd : ∀ᵐ x∂μ, x∈S → (f+g) x=f x+g x :=
      (ae_restrict_iff' hS).mp (Lp.coeFn_add f g)
    apply Lp.ext
    filter_upwards [(zeroExtend_memLp hS (f+g)).coeFn_toLp,
      (zeroExtend_memLp hS f).coeFn_toLp,(zeroExtend_memLp hS g).coeFn_toLp,hadd,
      Lp.coeFn_add ((zeroExtend_memLp hS f).toLp (S.indicator (fun x=>f x)))
        ((zeroExtend_memLp hS g).toLp (S.indicator (fun x=>g x)))] with x hfg hf hg hsum hout
    simp only [Pi.add_apply] at hout
    rw [hfg,hout,hf,hg]
    by_cases hx : x∈S
    · simpa only [indicator_of_mem hx] using hsum hx
    · simp only [indicator_of_notMem hx,zero_add]
  map_smul' c f := by
    have hsm : ∀ᵐ x∂μ, x∈S → (c • f) x=c*f x :=
      (ae_restrict_iff' hS).mp (Lp.coeFn_smul c f)
    apply Lp.ext
    filter_upwards [(zeroExtend_memLp hS (c • f)).coeFn_toLp,
      (zeroExtend_memLp hS f).coeFn_toLp,hsm,
      Lp.coeFn_smul c ((zeroExtend_memLp hS f).toLp (S.indicator (fun x=>f x)))] with x hcf hf hsm hout
    simp only [RingHom.id_apply,Pi.smul_apply,smul_eq_mul] at *
    rw [hcf,hout,hf]
    by_cases hx : x∈S
    · simpa only [indicator_of_mem hx] using hsm hx
    · simp only [indicator_of_notMem hx,mul_zero]

lemma zeroExtendL2Linear_ae (hS : MeasurableSet S) (f : Lp ℝ 2 (μ.restrict S)) :
    zeroExtendL2Linear hS f =ᵐ[μ] S.indicator (fun x=>f x) := (zeroExtend_memLp hS f).coeFn_toLp

lemma norm_zeroExtendL2Linear (hS : MeasurableSet S) (f : Lp ℝ 2 (μ.restrict S)) :
    ‖zeroExtendL2Linear hS f‖=‖f‖ := by
  rw [zeroExtendL2Linear,LinearMap.coe_mk,AddHom.coe_mk,Lp.norm_toLp,
    eLpNorm_indicator_eq_eLpNorm_restrict hS,Lp.norm_def]

def zeroExtendL2 (hS : MeasurableSet S) : Lp ℝ 2 (μ.restrict S) →L[ℝ] Lp ℝ 2 μ :=
  (zeroExtendL2Linear hS).mkContinuous 1 (by intro f; simpa only [one_mul] using (norm_zeroExtendL2Linear hS f).le)

lemma zeroExtendL2_ae (hS : MeasurableSet S) (f : Lp ℝ 2 (μ.restrict S)) :
    zeroExtendL2 hS f =ᵐ[μ] S.indicator (fun x=>f x) := zeroExtendL2Linear_ae hS f

end Mask
section Pullback
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} {S : Set X} {ψ : X → Y} {C : ℝ}

def maskedL2Composition (hS : MeasurableSet S) (hψ : Measurable ψ) (hC : 0≤C)
    (hmap : (μ.restrict S).map ψ≤ENNReal.ofReal (C^2) • ν) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ :=
  (zeroExtendL2 hS).comp (boundedL2Composition hψ hC hmap)

lemma maskedL2Composition_ae (hS : MeasurableSet S) (hψ : Measurable ψ) (hC : 0≤C)
    (hmap : (μ.restrict S).map ψ≤ENNReal.ofReal (C^2) • ν) (f : Lp ℝ 2 ν) :
    maskedL2Composition hS hψ hC hmap f =ᵐ[μ] S.indicator (fun x=>f (ψ x)) := by
  have hc : ∀ᵐ x∂μ, x∈S → boundedL2Composition hψ hC hmap f x=f (ψ x) :=
    (ae_restrict_iff' hS).mp (boundedL2Composition_ae hψ hC hmap f)
  filter_upwards [zeroExtendL2_ae hS (boundedL2Composition hψ hC hmap f),hc] with x hx he
  change zeroExtendL2 hS (boundedL2Composition hψ hC hmap f) x=_
  rw [hx]
  by_cases hxS : x∈S
  · simp only [indicator_of_mem hxS,he hxS]
  · simp only [indicator_of_notMem hxS]

lemma norm_maskedL2Composition_le (hS : MeasurableSet S) (hψ : Measurable ψ) (hC : 0≤C)
    (hmap : (μ.restrict S).map ψ≤ENNReal.ofReal (C^2) • ν) (f : Lp ℝ 2 ν) :
    ‖maskedL2Composition hS hψ hC hmap f‖≤C*‖f‖ := by
  change ‖zeroExtendL2Linear hS (boundedL2Composition hψ hC hmap f)‖≤_
  rw [norm_zeroExtendL2Linear]
  exact norm_boundedCompositionLinear_le hψ hC hmap f

end Pullback
end GaussianTilt.MomentMapLinearDirichlet
