import GaussianTilt.MomentMapSchauderLocalPatch

/-! # Pointwise reconstruction and true local higher-jet identities -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000
open Set Filter Function
open scoped ContDiff Topology
namespace GaussianTilt.MomentMapSchauder
universe u

lemma contDiffAt_clm_of_apply {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : D → E →L[ℝ] F} {x : D} {m : WithTop ℕ∞}
    (hf : ∀ v : E, ContDiffAt ℝ m (fun y => f y v) x) : ContDiffAt ℝ m f x := by
  let d := Module.finrank ℝ E
  have hd : d=Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[ℝ] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contDiffAt.comp x (contDiffAt_pi.mpr (fun i => hf _))

theorem contDiffAt_multilinear_of_apply {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (k : ℕ) {m : WithTop ℕ∞} {x : G}
    {f : G → ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F}
    (hf : ∀ v : Fin k → E, ContDiffAt ℝ m (fun y => f y v) x) : ContDiffAt ℝ m f x := by
  induction k with
  | zero =>
    let L := continuousMultilinearCurryFin0 ℝ E F
    have hh : ContDiffAt ℝ m (fun y => L (f y)) x := by convert hf (fun _ => (0 : E)) using 1
    convert L.symm.contDiff.contDiffAt.comp x hh using 1
    funext y
    exact (L.symm_apply_apply (f y)).symm
  | succ k ih =>
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) F
    have hh : ContDiffAt ℝ m (fun y => L (f y)) x := by
      apply contDiffAt_clm_of_apply
      intro e
      apply ih
      intro v
      exact hf (Fin.cons e v)
    convert L.symm.contDiff.contDiffAt.comp x hh using 1
    funext y
    exact (L.symm_apply_apply (f y)).symm

theorem contDiffAt_of_contDiffAt_iteratedFDeriv {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k m : ℕ) {f : E → F} (hf : ContDiff ℝ (k : WithTop ℕ∞) f) {x : E}
    (htop : ContDiffAt ℝ (m : WithTop ℕ∞) (iteratedFDeriv ℝ k f) x) :
    ContDiffAt ℝ (↑(k+m) : WithTop ℕ∞) f x := by
  induction k generalizing F with
  | zero =>
    let L := continuousMultilinearCurryFin0 ℝ E F
    have hh := L.contDiff.contDiffAt.comp x htop
    convert hh using 1
    simp
  | succ k ih =>
    have hDf : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
    let L := continuousMultilinearCurryRightEquiv' ℝ k E F
    have hDtop : ContDiffAt ℝ (m : WithTop ℕ∞) (iteratedFDeriv ℝ k (fderiv ℝ f)) x := by
      have hh := L.contDiff.contDiffAt.comp x htop
      convert hh using 1
      funext y
      dsimp only [Function.comp_apply]
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
      exact (L.apply_symm_apply _).symm
    have hD := ih hDf hDtop
    have hd : Differentiable ℝ f := hf.differentiable (by exact_mod_cast (show 1 ≤ k+1 by omega))
    have hh : ContDiffAt ℝ (↑((k+m)+1) : WithTop ℕ∞) f x := by
      rw [Nat.cast_add, Nat.cast_one, contDiffAt_succ_iff_hasFDerivAt]
      exact ⟨fderiv ℝ f, ⟨univ, Filter.univ_mem, fun y _ => (hd y).hasFDerivAt⟩, hD⟩
    convert hh using 1 <;> congr 1 <;> omega

open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma scalarDerivativeJet_cons_three_at (k : ℕ) {φ : KernelSpace n → ℝ} {x : KernelSpace n}
    (hφ : ContDiffAt ℝ (↑(k+4) : WithTop ℕ∞) φ x)
    (w : Fin (k+1) → KernelSpace n) (a b c : KernelSpace n) :
    iteratedFDeriv ℝ (k+4) φ x (Fin.cons a (Fin.cons b (Fin.cons c w)))=
      fderiv ℝ (fderiv ℝ (fderiv ℝ (scalarDerivativeJet (k+1) φ w))) x a b c := by
  obtain ⟨u, hu, he⟩ := exists_global_contDiff_eventuallyEq (k+4) hφ
  have hjet : scalarDerivativeJet (k+1) u w =ᶠ[𝓝 x] scalarDerivativeJet (k+1) φ w := by
    filter_upwards [he.iteratedFDeriv ℝ (k+1)] with y hy
    exact congrArg (fun B => B w) hy
  have htop := (he.iteratedFDeriv ℝ (k+4)).self_of_nhds
  have hthird : fderiv ℝ (fderiv ℝ (fderiv ℝ (scalarDerivativeJet (k+1) u w))) x=
      fderiv ℝ (fderiv ℝ (fderiv ℝ (scalarDerivativeJet (k+1) φ w))) x := hjet.fderiv.fderiv.fderiv_eq
  have hh := scalarDerivativeJet_cons_three k hu w a b c x
  rw [htop, hthird] at hh
  exact hh

end GaussianTilt.MomentMapSchauder
