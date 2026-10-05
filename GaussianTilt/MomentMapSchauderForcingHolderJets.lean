import GaussianTilt.MomentMapSchauderHolderJets
import GaussianTilt.MomentMapSchauderSourceIteratedEquation

/-! # Hölder jets of the literal recursively differentiated forcing -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2000000
open Set Matrix
open scoped ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ} {α : ℝ} {S : Set (KernelSpace n)}

lemma holderJetOn_secondFrechet_entry {m : ℕ} {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ (↑(m+2) : WithTop ℕ∞) u) (hj : HolderJetOn α (m+2) u S)
    (a b : KernelSpace n) : HolderJetOn α m (fun x => fderiv ℝ (fderiv ℝ u) x a b) S := by
  have hDu : ContDiff ℝ (↑(m+1) : WithTop ℕ∞) (fderiv ℝ u) :=
    hu.fderiv_right (by norm_num [Nat.cast_add, add_assoc])
  have hD2u : ContDiff ℝ (m : WithTop ℕ∞) (fderiv ℝ (fderiv ℝ u)) := hDu.fderiv_right (by simp)
  have hjDu : HolderJetOn α (m+1) (fderiv ℝ u) S := by
    apply HolderJetOn.fderiv
    convert hj using 1 <;> omega
  exact hjDu.fderiv.linear_map hD2u ((ContinuousLinearMap.apply ℝ ℝ b).comp
    (ContinuousLinearMap.apply ℝ (KernelSpace n →L[ℝ] ℝ) a))

lemma holderJetOn_scalarDerivativeJet (k m : ℕ) {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ (↑(m+k) : WithTop ℕ∞) u) (hj : HolderJetOn α (m+k) u S)
    (v : Fin k → KernelSpace n) : HolderJetOn α m (scalarDerivativeJet k u v) S :=
  (hj.iteratedFDeriv hu).linear_map
    (hu.iteratedFDeriv_right (by simp only [Nat.cast_add, le_refl]))
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => KernelSpace n) ℝ v)

lemma holderJetOn_ellipticDerivativeError {m : ℕ} {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ (↑(m+2) : WithTop ℕ∞) u) (huj : HolderJetOn α (m+2) u S)
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ (↑(m+1) : WithTop ℕ∞) (fun x => A x i j))
    (hAj : ∀ i j, HolderJetOn α (m+1) (fun x => A x i j) S)
    (hS : IsCompact S) (hSc : Convex ℝ S) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (v : KernelSpace n) : HolderJetOn α m (ellipticDerivativeError A u v) S := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hc (i j : Fin n) : ContDiff ℝ (m : WithTop ℕ∞)
      (fun x => fderiv ℝ (fun y => A y i j) x v*fderiv ℝ (fderiv ℝ u) x (e i) (e j)) :=
    (contDiff_kernelDirectionalDerivative (by simpa only [Nat.cast_add, Nat.cast_one] using hA i j) v).mul
      (contDiff_secondFrechet_entry (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hu) (e i) (e j))
  have hh (i j : Fin n) : HolderJetOn α m
      (fun x => fderiv ℝ (fun y => A y i j) x v*fderiv ℝ (fderiv ℝ u) x (e i) (e j)) S := by
    apply HolderJetOn.mul
      (contDiff_kernelDirectionalDerivative (by simpa only [Nat.cast_add, Nat.cast_one] using hA i j) v)
      (contDiff_secondFrechet_entry (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hu) (e i) (e j))
      ((hAj i j).directional (hA i j) v) (holderJetOn_secondFrechet_entry hu huj (e i) (e j))
      hS hSc hα hα1
  exact HolderJetOn.finset_sum Finset.univ (fun i _ => ContDiff.sum (fun j _ => hc i j))
    (fun i _ => HolderJetOn.finset_sum Finset.univ (fun j _ => hc i j) (fun j _ => hh i j))

/-- The actual recursively differentiated forcing has Hölder jets from the
stated source/coefficient/forcing jets. This is a genuine closure proof for
the full forcing recursion, not a Hölder-modulus assumption for its output. -/
theorem holderJetOn_iteratedEllipticForcing (k m : ℕ)
    {u f : KernelSpace n → ℝ} (hu : ContDiff ℝ (↑(k+m+1) : WithTop ℕ∞) u)
    (huj : HolderJetOn α (k+m+1) u S)
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ (↑(k+m) : WithTop ℕ∞) (fun x => A x i j))
    (hAj : ∀ i j, HolderJetOn α (k+m) (fun x => A x i j) S)
    (hf : ContDiff ℝ (↑(k+m) : WithTop ℕ∞) f) (hfj : HolderJetOn α (k+m) f S)
    (hS : IsCompact S) (hSc : Convex ℝ S) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (v : Fin k → KernelSpace n) : HolderJetOn α m (iteratedEllipticForcing A u f k v) S := by
  induction k generalizing m with
  | zero => simpa only [iteratedEllipticForcing, zero_add] using hfj
  | succ k ih =>
    have hu' : ContDiff ℝ (↑(k+(m+1)+1) : WithTop ℕ∞) u := by convert hu using 1 <;> congr 1 <;> omega
    have huj' : HolderJetOn α (k+(m+1)+1) u S := by convert huj using 1 <;> omega
    have hA' : ∀ i j, ContDiff ℝ (↑(k+(m+1)) : WithTop ℕ∞) (fun x => A x i j) := by
      intro i j
      convert hA i j using 1 <;> congr 1 <;> omega
    have hAj' : ∀ i j, HolderJetOn α (k+(m+1)) (fun x => A x i j) S := by
      intro i j
      convert hAj i j using 1 <;> omega
    have hf' : ContDiff ℝ (↑(k+(m+1)) : WithTop ℕ∞) f := by convert hf using 1 <;> congr 1 <;> omega
    have hfj' : HolderJetOn α (k+(m+1)) f S := by convert hfj using 1 <;> omega
    have hp : ContDiff ℝ (↑(m+1) : WithTop ℕ∞) (iteratedEllipticForcing A u f k (Fin.tail v)) :=
      contDiff_iteratedEllipticForcing k (m+1) hu' hA' hf' (Fin.tail v)
    have hpj := ih (m+1) hu' huj' hA' hAj' hf' hfj' (Fin.tail v)
    have hjc : ContDiff ℝ (↑(m+2) : WithTop ℕ∞) (scalarDerivativeJet k u (Fin.tail v)) :=
      contDiff_scalarDerivativeJet k (m+2) (by convert hu using 1 <;> congr 1 <;> omega) (Fin.tail v)
    have hjj : HolderJetOn α (m+2) (scalarDerivativeJet k u (Fin.tail v)) S :=
      holderJetOn_scalarDerivativeJet k (m+2) (by convert hu using 1 <;> congr 1 <;> omega)
        (by convert huj using 1 <;> omega) (Fin.tail v)
    have hAs : ∀ i j, ContDiff ℝ (↑(m+1) : WithTop ℕ∞) (fun x => A x i j) :=
      fun i j => (hA i j).of_le (by exact_mod_cast (show m+1 ≤ k+1+m by omega))
    have hAjs : ∀ i j, HolderJetOn α (m+1) (fun x => A x i j) S :=
      fun i j => (hAj i j).mono_order (by omega)
    exact HolderJetOn.sub
      (contDiff_kernelDirectionalDerivative (by simpa only [Nat.cast_add, Nat.cast_one] using hp) (v 0))
      (contDiff_ellipticDerivativeError hjc hAs (v 0))
      (hpj.directional hp (v 0))
      (holderJetOn_ellipticDerivativeError hjc hjj hAs hAjs hS hSc hα hα1 (v 0))

end GaussianTilt.MomentMapSchauder
