import GaussianTilt.MomentMapDirectionalDerivatives
import GaussianTilt.LetwinIntegration

/-! # Almost-everywhere coordinate differentiability of convex potentials

The scalar exceptional-set theorem and the proved measurability of the
one-sided directional derivatives justify Fubini on every coordinate slice.
The resulting full-measure set has every coordinate partial derivative.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

def unitCoordinate (i : Fin n) : E n := WithLp.toLp 2 (Pi.single i 1)

lemma insertNth_toLp_add (i : Fin (n + 1)) (y : Fin n → ℝ) (t s : ℝ) :
    (WithLp.toLp 2 (i.insertNth (t + s) y) : E (n + 1)) =
      WithLp.toLp 2 (i.insertNth t y) + s • unitCoordinate i := by
  ext j
  obtain rfl | ⟨j, rfl⟩ := i.eq_self_or_eq_succAbove j
  · simp [unitCoordinate]
  · simp [unitCoordinate, Fin.succAbove_ne]

lemma slice_convex {φ : E (n + 1) → ℝ} (hφ : ConvexOn ℝ univ φ)
    (i : Fin (n + 1)) (y : Fin n → ℝ) :
    ConvexOn ℝ univ (fun t : ℝ => φ (WithLp.toLp 2 (i.insertNth t y))) := by
  have h := convex_affineLine hφ (unitCoordinate i) (WithLp.toLp 2 (i.insertNth 0 y))
  have heq : (fun t : ℝ => φ (WithLp.toLp 2 (i.insertNth t y))) =
      affineLine φ (unitCoordinate i) (WithLp.toLp 2 (i.insertNth 0 y)) := by
    funext t
    rw [← zero_add t, insertNth_toLp_add]
    simp [affineLine]
  rw [heq]
  exact h

lemma slice_directional_differentiable {φ : E (n + 1) → ℝ}
    (i : Fin (n + 1)) (y : Fin n → ℝ) {t : ℝ}
    (h : DifferentiableAt ℝ (fun s : ℝ => φ (WithLp.toLp 2 (i.insertNth s y))) t) :
    DifferentiableAt ℝ (affineLine φ (unitCoordinate i) (WithLp.toLp 2 (i.insertNth t y))) 0 := by
  have hg : DifferentiableAt ℝ (fun s : ℝ => t + s) 0 :=
    (differentiable_const t).differentiableAt.add differentiableAt_id
  have h' : DifferentiableAt ℝ (fun s : ℝ => φ (WithLp.toLp 2 (i.insertNth s y))) (t + 0) := by
    simpa using h
  have hc := h'.comp 0 hg
  have heq : affineLine φ (unitCoordinate i) (WithLp.toLp 2 (i.insertNth t y)) =
      fun s : ℝ => φ (WithLp.toLp 2 (i.insertNth (t + s) y)) := by
    funext s
    rw [insertNth_toLp_add]
    rfl
  rw [heq]
  simpa only [Function.comp_def, add_zero] using hc

theorem convex_ae_coordinate_differentiable_succ {φ : E (n + 1) → ℝ}
    (hφ : ConvexOn ℝ univ φ) (i : Fin (n + 1)) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ (affineLine φ (unitCoordinate i) x) 0 := by
  let e₀ := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have he₀ : MeasurePreserving e₀ :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  let e : (Fin n → ℝ) × ℝ → E (n + 1) := fun p => WithLp.toLp 2 (i.insertNth p.2 p.1)
  have he : MeasurePreserving e ((volume : Measure (Fin n → ℝ)).prod volume) volume := by
    have h := (PiLp.volume_preserving_toLp (Fin (n + 1))).comp (he₀.comp
      (Measure.measurePreserving_swap (μ := (volume : Measure (Fin n → ℝ))) (ν := (volume : Measure ℝ))))
    simpa only [Measure.volume_eq_prod, e₀, e, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply] using h
  have hgood := measurableSet_differentiable_affineLine hφ (unitCoordinate i)
  have hprod : ∀ᵐ p ∂((volume : Measure (Fin n → ℝ)).prod volume),
      DifferentiableAt ℝ (affineLine φ (unitCoordinate i) (e p)) 0 := by
    apply (Measure.ae_prod_iff_ae_ae (he.measurable hgood)).mpr
    apply ae_of_all
    intro y
    filter_upwards [convex_ae_differentiable_real (slice_convex hφ i y)] with t ht
    exact slice_directional_differentiable i y ht
  rw [← he.map_eq]
  exact (ae_map_iff he.measurable.aemeasurable hgood).mpr hprod

theorem convex_ae_coordinate_differentiable {φ : E n → ℝ}
    (hφ : ConvexOn ℝ univ φ) (i : Fin n) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ (affineLine φ (unitCoordinate i) x) 0 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact convex_ae_coordinate_differentiable_succ hφ i

theorem convex_ae_all_coordinates_differentiable {φ : E n → ℝ}
    (hφ : ConvexOn ℝ univ φ) :
    ∀ᵐ x ∂volume, ∀ i : Fin n, DifferentiableAt ℝ (affineLine φ (unitCoordinate i) x) 0 := by
  rw [ae_all_iff]
  exact convex_ae_coordinate_differentiable hφ

end GaussianTilt.MomentMapCoercivity
