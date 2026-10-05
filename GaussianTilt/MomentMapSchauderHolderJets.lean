import GaussianTilt.MomentMapSchauderHolderComposition

/-! # Actual Hölder jet algebra and differentiation -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2000000
open Set
open scoped ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma HolderJetOn.zero_of {α : ℝ} {f : E → F} {S : Set E} (hf : BoundedHolderOn α f S) :
    HolderJetOn α 0 f S := by
  intro j hj
  have hj0 : j=0 := Nat.eq_zero_of_le_zero hj
  subst j
  exact hf.map (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma HolderJetOn.value {α : ℝ} {k : ℕ} {f : E → F} {S : Set E} (hf : HolderJetOn α k f S) :
    BoundedHolderOn α f S := by
  have hh := (hf 0 (Nat.zero_le k)).map
    (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap
  apply hh.congr
  intro x hx
  exact (continuousMultilinearCurryFin0 ℝ E F).apply_symm_apply (f x)

lemma HolderJetOn.add {α : ℝ} {k : ℕ} {f g : E → F} {S : Set E}
    (hf : ContDiff ℝ (k : WithTop ℕ∞) f) (hg : ContDiff ℝ (k : WithTop ℕ∞) g)
    (hfj : HolderJetOn α k f S) (hgj : HolderJetOn α k g S) :
    HolderJetOn α k (fun x => f x+g x) S := by
  intro j hj
  apply ((hfj j hj).add (hgj j hj)).congr
  intro x hx
  exact (iteratedFDeriv_add_apply' (hf.contDiffAt.of_le (by exact_mod_cast hj))
    (hg.contDiffAt.of_le (by exact_mod_cast hj))).symm

lemma HolderJetOn.neg {α : ℝ} {k : ℕ} {f : E → F} {S : Set E}
    (hf : ContDiff ℝ (k : WithTop ℕ∞) f) (hfj : HolderJetOn α k f S) :
    HolderJetOn α k (fun x => -f x) S :=
  hfj.linear_map hf (-ContinuousLinearMap.id ℝ F)

lemma HolderJetOn.sub {α : ℝ} {k : ℕ} {f g : E → F} {S : Set E}
    (hf : ContDiff ℝ (k : WithTop ℕ∞) f) (hg : ContDiff ℝ (k : WithTop ℕ∞) g)
    (hfj : HolderJetOn α k f S) (hgj : HolderJetOn α k g S) :
    HolderJetOn α k (fun x => f x-g x) S := by
  simpa only [sub_eq_add_neg] using hfj.add hf hg.neg (hgj.neg hg)

lemma HolderJetOn.prod {α : ℝ} {k : ℕ} {f : E → F} {g : E → G} {S : Set E}
    (hf : ContDiff ℝ (k : WithTop ℕ∞) f) (hg : ContDiff ℝ (k : WithTop ℕ∞) g)
    (hfj : HolderJetOn α k f S) (hgj : HolderJetOn α k g S) :
    HolderJetOn α k (fun x => (f x,g x)) S := by
  intro j hj
  have hpair := (hfj j hj).prod (hgj j hj)
  have hh := hpair.map (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin j => E) F G).toContinuousLinearEquiv.toContinuousLinearMap
  apply hh.congr
  intro x hx
  apply ContinuousMultilinearMap.ext
  intro v
  apply Prod.ext
  · have he := (ContinuousLinearMap.fst ℝ F G).iteratedFDeriv_comp_left (x := x)
      (hf.prodMk hg).contDiffAt (i := j) (by exact_mod_cast hj)
    exact congrArg (fun M => M v) he
  · have he := (ContinuousLinearMap.snd ℝ F G).iteratedFDeriv_comp_left (x := x)
      (hf.prodMk hg).contDiffAt (i := j) (by exact_mod_cast hj)
    exact congrArg (fun M => M v) he

lemma HolderJetOn.pi {α : ℝ} {k : ℕ} {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    {f : ∀ i, E → V i} {S : Set E}
    (hf : ∀ i, ContDiff ℝ (k : WithTop ℕ∞) (f i)) (hfj : ∀ i, HolderJetOn α k (f i) S) :
    HolderJetOn α k (fun x i => f i x) S := by
  intro j hj
  have hp := BoundedHolderOn.pi (fun i => hfj i j hj)
  have hh := hp.map (ContinuousMultilinearMap.piₗᵢ ℝ (fun _ : Fin j => E)).toContinuousLinearEquiv.toContinuousLinearMap
  apply hh.congr
  intro x hx
  apply ContinuousMultilinearMap.ext
  intro v
  funext i
  let L : (∀ i, V i) →L[ℝ] V i := ContinuousLinearMap.proj i
  have he := L.iteratedFDeriv_comp_left (x := x) (contDiff_pi.mpr hf).contDiffAt (i := j) (by exact_mod_cast hj)
  exact congrArg (fun M => M v) he

lemma HolderJetOn.finset_sum {α : ℝ} {k : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → E → F} {S : Set E}
    (hf : ∀ i ∈ s, ContDiff ℝ (k : WithTop ℕ∞) (f i))
    (hfj : ∀ i ∈ s, HolderJetOn α k (f i) S) :
    HolderJetOn α k (fun x => ∑ i ∈ s, f i x) S := by
  intro j hj
  have hh := BoundedHolderOn.finset_sum s (fun i hi => hfj i hi j hj)
  apply hh.congr
  intro x hx
  simpa only [Finset.sum_apply] using congrFun
    (iteratedFDeriv_sum (fun i hi => (hf i hi).of_le (by exact_mod_cast hj))).symm x

lemma HolderJetOn.smul {α : ℝ} {k : ℕ} {a : E → ℝ} {f : E → F} {S : Set E}
    (ha : ContDiff ℝ (k : WithTop ℕ∞) a) (hf : ContDiff ℝ (k : WithTop ℕ∞) f)
    (haj : HolderJetOn α k a S) (hfj : HolderJetOn α k f S)
    (hS : IsCompact S) (hSc : Convex ℝ S) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    HolderJetOn α k (fun x => a x • f x) S := by
  by_cases hk : k=0
  · subst k
    exact HolderJetOn.zero_of (haj.value.smul hfj.value)
  · have hk1 : (1 : WithTop ℕ∞) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
    have houter : ContDiff ℝ (↑(k+1) : WithTop ℕ∞) (fun p : ℝ × F => p.1 • p.2) :=
      contDiff_fst.smul contDiff_snd
    exact holderJetOn_comp_smooth (ha.prodMk hf) ((ha.prodMk hf).of_le hk1)
      (fun _ => houter.contDiffAt) hS hSc hα hα1 (haj.prod ha hf hfj)

lemma HolderJetOn.mul {α : ℝ} {k : ℕ} {f g : E → ℝ} {S : Set E}
    (hf : ContDiff ℝ (k : WithTop ℕ∞) f) (hg : ContDiff ℝ (k : WithTop ℕ∞) g)
    (hfj : HolderJetOn α k f S) (hgj : HolderJetOn α k g S)
    (hS : IsCompact S) (hSc : Convex ℝ S) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    HolderJetOn α k (fun x => f x*g x) S :=
  hfj.smul hf hg hgj hS hSc hα hα1

lemma HolderJetOn.directional {α : ℝ} {k : ℕ} {f : E → F} {S : Set E}
    (hf : ContDiff ℝ (↑(k+1) : WithTop ℕ∞) f) (hfj : HolderJetOn α (k+1) f S) (v : E) :
    HolderJetOn α k (fun x => _root_.fderiv ℝ f x v) S := by
  have hDf : ContDiff ℝ (k : WithTop ℕ∞) (_root_.fderiv ℝ f) := hf.fderiv_right (by simp)
  exact hfj.fderiv.linear_map hDf (ContinuousLinearMap.apply ℝ F v)

/-- Iterating actual derivatives lowers the Hölder jet order by exactly
the number of differentiations; currying is handled by genuine isometries. -/
theorem HolderJetOn.iteratedFDeriv {α : ℝ} {k m : ℕ} {f : E → F} {S : Set E}
    (hf : ContDiff ℝ (↑(k+m) : WithTop ℕ∞) f) (hfj : HolderJetOn α (k+m) f S) :
    HolderJetOn α k (_root_.iteratedFDeriv ℝ m f) S := by
  induction m generalizing k with
  | zero =>
    simpa only [Nat.add_zero, iteratedFDeriv_zero_eq_comp] using
      hfj.linear_map hf (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
  | succ m ih =>
    have hc : ContDiff ℝ (↑((k+1)+m) : WithTop ℕ∞) f := by convert hf using 1 <;> congr 1 <;> omega
    have hj : HolderJetOn α ((k+1)+m) f S := by convert hfj using 1 <;> omega
    have hprev := ih hc hj
    have hprevC : ContDiff ℝ (↑(k+1) : WithTop ℕ∞) (_root_.iteratedFDeriv ℝ m f) :=
      hc.iteratedFDeriv_right (i := m) (by simp only [Nat.cast_add, le_refl])
    have hD : ContDiff ℝ (k : WithTop ℕ∞) (_root_.fderiv ℝ (_root_.iteratedFDeriv ℝ m f)) :=
      hprevC.fderiv_right (by simp)
    have hh := hprev.fderiv.linear_map hD
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact hh

end GaussianTilt.MomentMapSchauder
