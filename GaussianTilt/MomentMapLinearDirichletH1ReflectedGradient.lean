import GaussianTilt.MomentMapLinearDirichletH1FlatReflection
import GaussianTilt.MomentMapLinearDirichletHarmonicL2Local
import GaussianTilt.MomentMapEllipticFundamentalSolutionHessianGreen

/-! # The actual weak gradient of the odd Sobolev reflection -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def flatReflectionSign (j i : Fin n) : ℝ := if i=j then -1 else 1

lemma flatReflectionSign_sq (j i : Fin n) : flatReflectionSign j i^2=1 := by
  unfold flatReflectionSign
  split_ifs <;> norm_num

lemma kernelDerivative_flatReflection {ψ : KernelSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (j i : Fin n) (x : KernelSpace n) :
    kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) (ψ ∘ flatReflection j) x=
      flatReflectionSign j i*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ (flatReflection j x) := by
  unfold kernelDirectionalDerivative
  change (fderiv ℝ (ψ ∘ (flatReflection j).toContinuousLinearEquiv) x) (EuclideanSpace.basisFun (Fin n) ℝ i)=_
  rw [fderiv_comp x (hψ.differentiable (by simp) _) (flatReflection j).toContinuousLinearEquiv.differentiableAt,
    (flatReflection j).toContinuousLinearEquiv.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    flatReflection_basis,flatReflectionSign]
  split_ifs <;> simp

lemma dirichletSobolev_physical_integration_by_parts {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (i : Fin n) {ψ : KernelSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, u.1 i.succ (dirichletCoordinateEquiv n x)*ψ x)=
      -(∫ x, dirichletValue Ω u (dirichletCoordinateEquiv n x)*
        kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x) := by
  let g : smoothCompactCore n := ⟨ψ ∘ (dirichletCoordinateEquiv n).symm,
    hψ.comp (dirichletCoordinateEquiv n).symm.contDiff,
    hψc.comp_homeomorph (dirichletCoordinateEquiv n).symm.toHomeomorph⟩
  have hh := dirichletSobolev_integration_by_parts u i g
  rw [inner_Lp_smoothCompactToL2,inner_Lp_smoothCompactToL2] at hh
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  rw [← hμ.integral_comp (dirichletCoordinateEquiv n).toHomeomorph.measurableEmbedding
      (fun y => u.1 i.succ y*g.1 y),
    ← hμ.integral_comp (dirichletCoordinateEquiv n).toHomeomorph.measurableEmbedding
      (fun y => u.1 0 y*(smoothCompactDerivative i g).1 y)] at hh
  change (∫ x, u.1 i.succ (dirichletCoordinateEquiv n x)*ψ ((dirichletCoordinateEquiv n).symm (dirichletCoordinateEquiv n x)))=
    -(∫ x, u.1 0 (dirichletCoordinateEquiv n x)*coordinateDerivative i (ψ ∘ (dirichletCoordinateEquiv n).symm) (dirichletCoordinateEquiv n x)) at hh
  simpa only [ContinuousLinearEquiv.symm_apply_apply,coordinateDerivative_toLp_any] using hh

lemma integrable_locally_mul_kernelDerivative {u ψ : KernelSpace n → ℝ}
    (hu : LocallyIntegrable u volume) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (v : KernelSpace n) : Integrable (fun x => u x*kernelDirectionalDerivative v ψ x) volume :=
  hu.integrable_smul_right_of_hasCompactSupport
    ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous (hψc.fderiv_apply (𝕜 := ℝ) v)

def flatReflectedGradient (j i : Fin n) (G : Fin n → KernelSpace n → ℝ) (x : KernelSpace n) : ℝ :=
  G i x-flatReflectionSign j i*G i (flatReflection j x)

lemma flatReflectedGradient_memLp (j i : Fin n) {G : Fin n → KernelSpace n → ℝ}
    (hG : MemLp (G i) 2 volume) : MemLp (flatReflectedGradient j i G) 2 volume :=
  hG.sub ((hG.comp_measurePreserving (flatReflection j).measurePreserving).const_mul _)

lemma flatReflectedGradient_parity (j i : Fin n) (G : Fin n → KernelSpace n → ℝ) (x : KernelSpace n) :
    flatReflectedGradient j i G (flatReflection j x)=
      -flatReflectionSign j i*flatReflectedGradient j i G x := by
  simp only [flatReflectedGradient,flatReflection_involutive j x]
  unfold flatReflectionSign
  split_ifs <;> ring

/-- The true first-order distributional gradient of the odd value
extension is the reflected weak gradient, with the correct normal sign. -/
theorem dirichletSobolev_odd_weak_gradient {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (j i : Fin n) {ψ : KernelSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, flatReflectedGradient j i (fun k y => u.1 k.succ (dirichletCoordinateEquiv n y)) x*ψ x)=
      -(∫ x, flatOddExtension j (fun y => dirichletValue Ω u (dirichletCoordinateEquiv n y)) x*
        kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x) := by
  let U := fun y => dirichletValue Ω u (dirichletCoordinateEquiv n y)
  let G := fun y => u.1 i.succ (dirichletCoordinateEquiv n y)
  let σ := flatReflectionSign j i
  let Dψ := kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have hUL := ((Lp.memLp (dirichletValue Ω u)).comp_measurePreserving hμ).locallyIntegrable (by norm_num)
  have hGL := ((Lp.memLp (u.1 i.succ)).comp_measurePreserving hμ).locallyIntegrable (by norm_num)
  have hψT := hψ.comp (flatReflection j).toContinuousLinearEquiv.contDiff
  have hψTc := hψc.comp_homeomorph (flatReflection j).toHomeomorph
  have hI := dirichletSobolev_physical_integration_by_parts u i hψ hψc
  have hIT := dirichletSobolev_physical_integration_by_parts u i hψT hψTc
  have hGP : Integrable (fun x => G x*ψ x) volume := hGL.integrable_smul_right_of_hasCompactSupport hψ.continuous hψc
  have hGPT : Integrable (fun x => G (flatReflection j x)*ψ x) volume :=
    (((Lp.memLp (u.1 i.succ)).comp_measurePreserving hμ).comp_measurePreserving
      (flatReflection j).measurePreserving).locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport hψ.continuous hψc
  have hUP := integrable_locally_mul_kernelDerivative hUL hψ hψc (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hUPT := integrable_locally_mul_kernelDerivative
    ((((Lp.memLp (dirichletValue Ω u)).comp_measurePreserving hμ).comp_measurePreserving
      (flatReflection j).measurePreserving).locallyIntegrable (by norm_num)) hψ hψc (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hGchange : (∫ x, G (flatReflection j x)*ψ x)=∫ x, G x*ψ (flatReflection j x) := by
    have hh := (flatReflection j).measurePreserving.integral_comp (flatReflection j).toHomeomorph.measurableEmbedding
      (fun x => G (flatReflection j x)*ψ x)
    have hTT (x : KernelSpace n) : flatReflection j (flatReflection j x)=x := flatReflection_involutive j x
    simpa only [hTT] using hh.symm
  have hUchange : (∫ x, U (flatReflection j x)*Dψ x)=∫ x, U x*Dψ (flatReflection j x) := by
    have hh := (flatReflection j).measurePreserving.integral_comp (flatReflection j).toHomeomorph.measurableEmbedding
      (fun x => U (flatReflection j x)*Dψ x)
    have hTT (x : KernelSpace n) : flatReflection j (flatReflection j x)=x := flatReflection_involutive j x
    simpa only [hTT] using hh.symm
  change (∫ x, G x*ψ x)=-(∫ x, U x*Dψ x) at hI
  change (∫ x, G x*ψ (flatReflection j x))=-(∫ x, U x*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) (ψ ∘ flatReflection j) x) at hIT
  simp_rw [kernelDerivative_flatReflection hψ] at hIT
  have hIT' : (∫ x, G x*ψ (flatReflection j x))=-σ*(∫ x, U x*Dψ (flatReflection j x)) := by
    convert hIT using 1
    rw [show (fun x => U x*(flatReflectionSign j i*Dψ (flatReflection j x)))=
      (fun x => σ*(U x*Dψ (flatReflection j x))) from by funext x; dsimp [σ]; ring,integral_const_mul]
    ring
  change Integrable (fun x => U x*Dψ x) volume at hUP
  change Integrable (fun x => U (flatReflection j x)*Dψ x) volume at hUPT
  change (∫ x, (G x-σ*G (flatReflection j x))*ψ x)=-(∫ x, (U x-U (flatReflection j x))*Dψ x)
  simp only [sub_mul,mul_assoc]
  rw [integral_sub hGP (hGPT.const_mul σ),integral_const_mul,
    integral_sub hUP hUPT,hGchange,hUchange,hI,hIT']
  have hs : σ^2=1 := flatReflectionSign_sq j i
  nlinarith [congrArg (fun a => a*(∫ x, U x*Dψ (flatReflection j x))) hs]

end GaussianTilt.MomentMapLinearDirichlet
