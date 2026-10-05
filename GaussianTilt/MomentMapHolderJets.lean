import GaussianTilt.MomentMapHolderSegments

/-! # Complete Hölder jet spaces with genuine FTC compatibility

The function, first-derivative field and second-derivative field live in
constructed Hölder Banach spaces. Actual segment integral identities form
closed linear constraints; zero boundary data are a further closed kernel.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev JetAmbient (S : Set E) (α : ℝ) :=
  Space S F α × Space S (E →L[ℝ] F) α × Space S (E →L[ℝ] E →L[ℝ] F) α

def jetValueProjection (S : Set E) (α : ℝ) : JetAmbient E F S α →L[ℝ] Space S F α :=
  ContinuousLinearMap.fst ℝ _ _

def jetFirstProjection (S : Set E) (α : ℝ) : JetAmbient E F S α →L[ℝ] Space S (E →L[ℝ] F) α :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

def jetSecondProjection (S : Set E) (α : ℝ) : JetAmbient E F S α →L[ℝ] Space S (E →L[ℝ] E →L[ℝ] F) α :=
  (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

def jetDefectZero {S : Set E} (hS : Convex ℝ S) (α : ℝ) (x y : S) : JetAmbient E F S α →L[ℝ] F :=
  ((eval S F α y - eval S F α x).comp (jetValueProjection E F S α)) -
    (segmentIntegral hS α x y).comp (jetFirstProjection E F S α)

def jetDefectOne {S : Set E} (hS : Convex ℝ S) (α : ℝ) (x y : S) : JetAmbient E F S α →L[ℝ] (E →L[ℝ] F) :=
  ((eval S (E →L[ℝ] F) α y - eval S (E →L[ℝ] F) α x).comp (jetFirstProjection E F S α)) -
    (segmentIntegral hS α x y).comp (jetSecondProjection E F S α)

def jetGraph {S : Set E} (hS : Convex ℝ S) (α : ℝ) : Submodule ℝ (JetAmbient E F S α) :=
  (⨅ p : S × S, LinearMap.ker (jetDefectZero E F hS α p.1 p.2).toLinearMap) ⊓
  (⨅ p : S × S, LinearMap.ker (jetDefectOne E F hS α p.1 p.2).toLinearMap)

lemma isClosed_commonKernel {V W I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (L : I → V →L[ℝ] W) :
    IsClosed ((⨅ i, LinearMap.ker (L i).toLinearMap : Submodule ℝ V) : Set V) := by
  have he : ((⨅ i, LinearMap.ker (L i).toLinearMap : Submodule ℝ V) : Set V) =
      ⋂ i, {v | L i v = 0} := by
    ext v
    simp only [mem_iInter, mem_setOf_eq]
    change (v ∈ (⨅ i, LinearMap.ker (L i).toLinearMap : Submodule ℝ V)) ↔ _
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  rw [he]
  exact isClosed_iInter (fun i => isClosed_eq (L i).continuous continuous_const)

lemma isClosed_jetGraph {S : Set E} (hS : Convex ℝ S) (α : ℝ) :
    IsClosed (jetGraph E F hS α : Set (JetAmbient E F S α)) := by
  rw [jetGraph, Submodule.coe_inf]
  exact (isClosed_commonKernel (fun p : S × S => jetDefectZero E F hS α p.1 p.2)).inter
    (isClosed_commonKernel (fun p : S × S => jetDefectOne E F hS α p.1 p.2))

def Jet {S : Set E} (hS : Convex ℝ S) (α : ℝ) := ↥(jetGraph E F hS α)

instance instNormedAddCommGroupJet {S : Set E} (hS : Convex ℝ S) (α : ℝ) :
    NormedAddCommGroup (Jet E F hS α) := inferInstanceAs (NormedAddCommGroup ↥(jetGraph E F hS α))

instance instNormedSpaceJet {S : Set E} (hS : Convex ℝ S) (α : ℝ) :
    NormedSpace ℝ (Jet E F hS α) := inferInstanceAs (NormedSpace ℝ ↥(jetGraph E F hS α))

instance completeSpace_jet [CompleteSpace F] {S : Set E} (hS : Convex ℝ S) (α : ℝ) :
    CompleteSpace (Jet E F hS α) := (isClosed_jetGraph E F hS α).completeSpace_coe

def jetValue {S : Set E} (hS : Convex ℝ S) (α : ℝ) : Jet E F hS α →L[ℝ] Space S F α :=
  (jetValueProjection E F S α).comp (jetGraph E F hS α).subtypeL

def jetFirst {S : Set E} (hS : Convex ℝ S) (α : ℝ) : Jet E F hS α →L[ℝ] Space S (E →L[ℝ] F) α :=
  (jetFirstProjection E F S α).comp (jetGraph E F hS α).subtypeL

def jetSecond {S : Set E} (hS : Convex ℝ S) (α : ℝ) : Jet E F hS α →L[ℝ] Space S (E →L[ℝ] E →L[ℝ] F) α :=
  (jetSecondProjection E F S α).comp (jetGraph E F hS α).subtypeL

/-- Membership means the literal fundamental-theorem-of-calculus identities,
not a formal independent derivative field. -/
theorem jet_ftc {S : Set E} (hS : Convex ℝ S) (α : ℝ) (j : Jet E F hS α) (x y : S) :
    value S F α (jetValue E F hS α j) y - value S F α (jetValue E F hS α j) x =
      segmentIntegral hS α x y (jetFirst E F hS α j) ∧
    value S (E →L[ℝ] F) α (jetFirst E F hS α j) y - value S (E →L[ℝ] F) α (jetFirst E F hS α j) x =
      segmentIntegral hS α x y (jetSecond E F hS α j) := by
  have hj := j.2
  simp only [jetGraph, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hj
  have h₀ := hj.1 (x, y)
  have h₁ := hj.2 (x, y)
  change value S F α (jetValue E F hS α j) y - value S F α (jetValue E F hS α j) x -
    segmentIntegral hS α x y (jetFirst E F hS α j) = 0 at h₀
  change value S (E →L[ℝ] F) α (jetFirst E F hS α j) y - value S (E →L[ℝ] F) α (jetFirst E F hS α j) x -
    segmentIntegral hS α x y (jetSecond E F hS α j) = 0 at h₁
  exact ⟨sub_eq_zero.mp h₀, sub_eq_zero.mp h₁⟩

def zeroBoundary {S : Set E} (hS : Convex ℝ S) (α : ℝ) : Submodule ℝ (Jet E F hS α) :=
  ⨅ x : {x : S // (x : E) ∈ frontier S},
    LinearMap.ker ((eval S F α x.1).comp (jetValue E F hS α)).toLinearMap

lemma isClosed_zeroBoundary {S : Set E} (hS : Convex ℝ S) (α : ℝ) :
    IsClosed (zeroBoundary E F hS α : Set (Jet E F hS α)) :=
  isClosed_commonKernel (fun x : {x : S // (x : E) ∈ frontier S} =>
    (eval S F α x.1).comp (jetValue E F hS α))

instance completeSpace_zeroBoundary [CompleteSpace F] {S : Set E} (hS : Convex ℝ S) (α : ℝ) :
    CompleteSpace (zeroBoundary E F hS α) := (isClosed_zeroBoundary E F hS α).completeSpace_coe

end GaussianTilt.HolderSpace
