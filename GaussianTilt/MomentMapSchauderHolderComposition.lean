import GaussianTilt.MomentMapSchauderBoundedHolder

/-! # Hölder control of actual higher composition jets via Faà di Bruno -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000
open Set
open scoped BigOperators ContDiff
namespace GaussianTilt.MomentMapSchauder
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Bounded Hölder control for all actual derivative fields up to a finite
order. Smoothness is stated separately when a chain rule requires it. -/
def HolderJetOn (α : ℝ) (k : ℕ) (f : E → F) (S : Set E) : Prop :=
  ∀ j : ℕ, j ≤ k → BoundedHolderOn α (iteratedFDeriv ℝ j f) S

lemma HolderJetOn.mono_order {α : ℝ} {k m : ℕ} {f : E → F} {S : Set E}
    (hf : HolderJetOn α k f S) (hm : m ≤ k) : HolderJetOn α m f S :=
  fun j hj => hf j (hj.trans hm)

lemma HolderJetOn.mono_set {α : ℝ} {k : ℕ} {f : E → F} {S T : Set E}
    (hf : HolderJetOn α k f S) (hT : T ⊆ S) : HolderJetOn α k f T :=
  fun j hj => (hf j hj).mono hT

/-- Lower derivative fields have Hölder bounds by actual C¹ regularity;
only the top derivative Hölder modulus needs to be supplied. -/
theorem holderJetOn_of_top {α : ℝ} {k : ℕ} {f : E → F}
    (hf : ContDiff ℝ (k : WithTop ℕ∞) f) {S : Set E} (hS : IsCompact S) (hSc : Convex ℝ S)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (htop : BoundedHolderOn α (iteratedFDeriv ℝ k f) S) :
    HolderJetOn α k f S := by
  intro j hj
  rcases eq_or_lt_of_le hj with rfl | hjk
  · exact htop
  · apply boundedHolderOn_of_contDiff _ hS hSc hα hα1
    apply hf.iteratedFDeriv_right
    exact_mod_cast (show 1+j ≤ k by omega)

/-- Every Faà di Bruno summand is a fixed continuous linear-to-multilinear
map of the actual inner and outer jets. Thus their proven Hölder estimates
transfer to the true iterated derivative of the composition. -/
theorem boundedHolderOn_iteratedFDeriv_comp {α : ℝ} {k : ℕ} {f : E → F} {g : F → G}
    {S : Set E} (hf : ∀ x ∈ S, ContDiffAt ℝ (k : WithTop ℕ∞) f x)
    (hg : ∀ x ∈ S, ContDiffAt ℝ (k : WithTop ℕ∞) g (f x))
    (hinner : HolderJetOn α k f S)
    (houter : ∀ j : ℕ, j ≤ k → BoundedHolderOn α (fun x => iteratedFDeriv ℝ j g (f x)) S) :
    BoundedHolderOn α (iteratedFDeriv ℝ k (g ∘ f)) S := by
  classical
  have hterm (c : OrderedFinpartition k) :
      BoundedHolderOn α (fun x => (ftaylorSeries ℝ g (f x)).compAlongOrderedFinpartition
        (ftaylorSeries ℝ f x) c) S := by
    have ho := (houter c.length c.length_le).map (c.compAlongOrderedFinpartitionL ℝ E F G)
    have hi := BoundedHolderOn.pi (fun i : Fin c.length => hinner (c.partSize i) (c.partSize_le i))
    exact ho.multilinear_apply hi
  have hsum := BoundedHolderOn.finset_sum Finset.univ (fun c _ => hterm c)
  apply hsum.congr
  intro x hx
  rw [iteratedFDeriv_comp (hg x hx) (hf x hx) le_rfl]
  rfl

/-- Smooth outer derivative fields, evaluated along an actual C¹ inner
map, have local Hölder bounds. Together with Faà di Bruno this proves full
finite-order Hölder propagation for smooth nonlinearities. -/
theorem holderJetOn_comp_smooth {α : ℝ} {k : ℕ} {f : E → F} {g : F → G}
    (hf : ContDiff ℝ (k : WithTop ℕ∞) f) (hf₁ : ContDiff ℝ 1 f)
    (hg : ∀ x, ContDiffAt ℝ (↑(k+1) : WithTop ℕ∞) g (f x))
    {S : Set E} (hS : IsCompact S) (hSc : Convex ℝ S)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hjets : HolderJetOn α k f S) :
    HolderJetOn α k (g ∘ f) S := by
  intro j hj
  apply boundedHolderOn_iteratedFDeriv_comp
    (fun x _ => hf.contDiffAt.of_le (by exact_mod_cast hj))
    (fun x _ => (hg x).of_le (by exact_mod_cast (show j ≤ k+1 by omega)))
    (hjets.mono_order hj)
  intro m hm
  apply boundedHolderOn_of_contDiff _ hS hSc hα hα1
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact ((hg x).iteratedFDeriv_right (by exact_mod_cast (show 1+m ≤ k+1 by omega))).comp x hf₁.contDiffAt

/-- Taking a true derivative shifts the Hölder jet order, through the
standard right-currying linear isometry. -/
theorem HolderJetOn.fderiv {α : ℝ} {k : ℕ} {f : E → F} {S : Set E}
    (hf : HolderJetOn α (k+1) f S) : HolderJetOn α k (fderiv ℝ f) S := by
  intro j hj
  let L := continuousMultilinearCurryRightEquiv' ℝ j E F
  have hh := (hf (j+1) (by omega)).map L.toContinuousLinearEquiv.toContinuousLinearMap
  apply hh.congr
  intro x hx
  dsimp only
  rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
  exact L.apply_symm_apply _

/-- Fixed linear operations preserve actual Hölder jets. -/
theorem HolderJetOn.linear_map {α : ℝ} {k : ℕ} {f : E → F} {S : Set E}
    (hf : ContDiff ℝ (k : WithTop ℕ∞) f) (hjets : HolderJetOn α k f S) (L : F →L[ℝ] G) :
    HolderJetOn α k (L ∘ f) S := by
  intro j hj
  have hh := (hjets j hj).map (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin j => E) F G L)
  apply hh.congr
  intro x hx
  exact (L.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast hj)).symm

end GaussianTilt.MomentMapSchauder
