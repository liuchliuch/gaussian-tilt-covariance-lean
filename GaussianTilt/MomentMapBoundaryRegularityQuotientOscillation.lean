import GaussianTilt.MomentMapBoundaryRegularityFlatSystem
import GaussianTilt.MomentMapRegularityForcedHolderIteration

/-! # The literal boundary quotient oscillation -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def boundaryQuotientValues (u : CoordinateSpace n → ℝ) (j : Fin n) (r : ℝ) : Set ℝ :=
  {q | ∃ x : CoordinateSpace n, ‖(coordinateEquiv n).symm x‖ ≤ r ∧ 0 < x j ∧ u x/x j=q}

def boundaryQuotientOscillation (u : CoordinateSpace n → ℝ) (j : Fin n) (r : ℝ) : ℝ :=
  sSup (boundaryQuotientValues u j r)-sInf (boundaryQuotientValues u j r)

lemma boundaryQuotientValues_nonempty (u : CoordinateSpace n → ℝ) (j : Fin n)
    {r : ℝ} (hr : 0 < r) : (boundaryQuotientValues u j r).Nonempty := by
  let x : CoordinateSpace n := Pi.single j (r/2)
  refine ⟨u x/x j,x,?_,?_,rfl⟩
  · rw [euclidean_coordinate_single_norm,abs_of_pos (half_pos hr)]
    linarith
  · simpa only [x,Pi.single_eq_same] using half_pos hr

lemma boundaryQuotientValues_mono (u : CoordinateSpace n → ℝ) (j : Fin n)
    {r R : ℝ} (hrR : r ≤ R) : boundaryQuotientValues u j r ⊆ boundaryQuotientValues u j R := by
  rintro q ⟨x,hx,hj,hq⟩
  exact ⟨x,hx.trans hrR,hj,hq⟩

lemma boundaryQuotientValues_abs_bound {u : CoordinateSpace n → ℝ} {j : Fin n} {B r : ℝ}
    (hr1 : r ≤ 1)
    (hb : ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |u x| ≤ B*x j) :
    ∀ q ∈ boundaryQuotientValues u j r, |q| ≤ B := by
  rintro q ⟨x,hx,hj,rfl⟩
  rw [abs_div,abs_of_pos hj]
  exact (div_le_iff₀ hj).mpr (hb x (hx.trans hr1) hj.le)

lemma boundaryQuotientValues_bounded {u : CoordinateSpace n → ℝ} {j : Fin n} {B r : ℝ}
    (hr1 : r ≤ 1)
    (hb : ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |u x| ≤ B*x j) :
    BddBelow (boundaryQuotientValues u j r) ∧ BddAbove (boundaryQuotientValues u j r) := by
  have h := boundaryQuotientValues_abs_bound hr1 hb
  exact ⟨⟨-B,fun q hq => (abs_le.mp (h q hq)).1⟩,⟨B,fun q hq => (abs_le.mp (h q hq)).2⟩⟩

lemma boundaryQuotient_ball_bounds {u : CoordinateSpace n → ℝ} {j : Fin n} {B r : ℝ}
    (hr1 : r ≤ 1)
    (hb : ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |u x| ≤ B*x j) :
    ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ r → 0 ≤ x j →
      sInf (boundaryQuotientValues u j r)*x j ≤ u x ∧
      u x ≤ sSup (boundaryQuotientValues u j r)*x j := by
  have hbd := boundaryQuotientValues_bounded hr1 hb
  intro x hx hj
  by_cases hp : 0 < x j
  · have hval : u x/x j ∈ boundaryQuotientValues u j r := ⟨x,hx,hp,rfl⟩
    exact ⟨(le_div_iff₀ hp).mp (csInf_le hbd.1 hval),
      (div_le_iff₀ hp).mp (le_csSup hbd.2 hval)⟩
  · have hz : x j=0 := by linarith
    have hu0 : u x=0 := by
      have hh := hb x (hx.trans hr1) hj
      rw [hz,mul_zero] at hh
      exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    simp only [hz,hu0,mul_zero,le_refl,and_self]

lemma boundaryQuotientOscillation_nonneg {u : CoordinateSpace n → ℝ} {j : Fin n} {B r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hb : ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |u x| ≤ B*x j) :
    0 ≤ boundaryQuotientOscillation u j r := by
  have hbd := boundaryQuotientValues_bounded hr1 hb
  exact sub_nonneg.mpr (csInf_le_csSup hbd.1 hbd.2 (boundaryQuotientValues_nonempty u j hr))

lemma boundaryQuotientOscillation_mono {u : CoordinateSpace n → ℝ} {j : Fin n} {B : ℝ}
    (hb : ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |u x| ≤ B*x j) :
    MonotoneOn (boundaryQuotientOscillation u j) (Ioc (0:ℝ) 1) := by
  intro r hr R hR hrR
  have hbd := boundaryQuotientValues_bounded hR.2 hb
  have hs := boundaryQuotientValues_mono u j hrR
  have hn := boundaryQuotientValues_nonempty u j hr.1
  have hu := csSup_le_csSup hbd.2 hn hs
  have hl := csInf_le_csInf hbd.1 hn hs
  unfold boundaryQuotientOscillation
  linarith

lemma boundaryQuotientOscillation_le_interval {u : CoordinateSpace n → ℝ} {j : Fin n}
    {r a b : ℝ} (hr : 0 < r)
    (hb : ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ r → 0 ≤ x j → a*x j ≤ u x ∧ u x ≤ b*x j) :
    boundaryQuotientOscillation u j r ≤ b-a := by
  have hn := boundaryQuotientValues_nonempty u j hr
  have hu : sSup (boundaryQuotientValues u j r) ≤ b := by
    apply csSup_le hn
    rintro q ⟨x,hx,hj,rfl⟩
    exact (div_le_iff₀ hj).mpr (hb x hx hj.le).2
  have hl : a ≤ sInf (boundaryQuotientValues u j r) := by
    apply le_csInf hn
    rintro q ⟨x,hx,hj,rfl⟩
    exact (le_div_iff₀ hj).mpr (hb x hx hj.le).1
  unfold boundaryQuotientOscillation
  linarith

end GaussianTilt.MomentMapRegularity
