import GaussianTilt.MomentMapLinearDirichletVariableWeakEuclideanCoefficients

/-! # Genuine closed half-ball geometry for the weak boundary patches -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapElliptic
variable {n : ℕ}
set_option maxHeartbeats 1600000

def coordinateClosedHalfBall (j:Fin n) (R:ℝ) : Set (CoordinateSpace n) :=
  rawChartClosedBall R ∩ {x:CoordinateSpace n|0≤x j}

lemma isCompact_coordinateClosedHalfBall (j:Fin n) (R:ℝ) : IsCompact (coordinateClosedHalfBall j R) :=
  (isCompact_rawChartClosedBall R).inter_right (isClosed_le continuous_const (continuous_apply j))

lemma convex_coordinateClosedHalfBall (j:Fin n) (R:ℝ) : Convex ℝ (coordinateClosedHalfBall j R) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_rawChartClosedBall R hx.1 hy.1 ha hb hab,?_⟩
  change 0≤a*x j+b*y j
  exact add_nonneg (mul_nonneg ha hx.2) (mul_nonneg hb hy.2)

lemma interior_coordinateClosedHalfBall (j:Fin n) {R:ℝ} (hR:0<R) :
    interior (coordinateClosedHalfBall j R)=coordinateHalfBall j R := by
  have hH:interior {x:CoordinateSpace n|0≤x j}={x|0<x j} := by
    let f:CoordinateSpace n→L[ℝ]ℝ := ContinuousLinearMap.proj j
    change interior (f ⁻¹' Ici (0:ℝ))=f ⁻¹' Ioi 0
    rw [f.interior_preimage,interior_Ici]
    intro b
    exact ⟨fun _=>b,rfl⟩
  have hB:interior (rawChartClosedBall (n:=n) R)=rawChartBall R := by
    have he := (coordinateEquiv n).symm.toHomeomorph.preimage_interior (Metric.closedBall (0:E n) R)
    rw [interior_closedBall _ hR.ne'] at he
    simpa only [rawChartClosedBall,rawChartBall,Metric.closedBall,Metric.ball,dist_zero_right,preimage_setOf_eq] using he.symm
  rw [coordinateClosedHalfBall,interior_inter,hH,hB]
  rfl

lemma coordinateHalfBall_nonempty (j:Fin n) {R:ℝ} (hR:0<R) : (coordinateHalfBall j R).Nonempty := by
  refine ⟨Pi.single j (R/2),?_,?_⟩
  · change ‖(coordinateEquiv n).symm (Pi.single j (R/2))‖<R
    rw [euclidean_coordinate_single_norm,abs_of_pos (by positivity : 0<R/2)]
    linarith
  · change 0<(Pi.single j (R/2):CoordinateSpace n) j
    simp only [Pi.single_eq_same]
    positivity

lemma interior_coordinateClosedHalfBall_nonempty (j:Fin n) {R:ℝ} (hR:0<R) :
    (interior (coordinateClosedHalfBall j R)).Nonempty := by
  rw [interior_coordinateClosedHalfBall j hR]
  exact coordinateHalfBall_nonempty j hR

lemma coordinateHalfBall_subset_closed (j:Fin n) (R:ℝ) :
    coordinateHalfBall j R⊆coordinateClosedHalfBall j R := fun x hx=>⟨hx.1.le,hx.2.le⟩

lemma coordinateClosedHalfBall_mono (j:Fin n) {r R:ℝ} (h:r≤R) :
    coordinateClosedHalfBall j r⊆coordinateClosedHalfBall j R := by
  intro x hx
  exact ⟨hx.1.trans h,hx.2⟩

lemma coordinateHalfBall_radius_mono (j:Fin n) {r R:ℝ} (h:r≤R) :
    coordinateHalfBall j r⊆coordinateHalfBall j R := by
  intro x hx
  exact ⟨hx.1.trans_le h,hx.2⟩

lemma coordinateClosedHalfBall_preimage (j:Fin n) (R:ℝ) :
    (dirichletCoordinateEquiv n) ⁻¹' coordinateClosedHalfBall j R=
      Metric.closedBall (0:KernelSpace n) R ∩ {x|0≤x j} := by
  ext x
  simp only [mem_preimage,coordinateClosedHalfBall,mem_inter_iff,rawChartClosedBall,mem_setOf_eq,
    Metric.mem_closedBall,dist_zero_right]
  rfl

lemma coordinateClosedHalfBall_eq_preimage (j:Fin n) (R:ℝ) :
    coordinateClosedHalfBall j R=(dirichletCoordinateEquiv n).symm ⁻¹'
      (Metric.closedBall (0:KernelSpace n) R ∩ {x|0≤x j}) := by
  ext x
  simp only [coordinateClosedHalfBall,rawChartClosedBall,mem_inter_iff,mem_setOf_eq,mem_preimage,
    Metric.mem_closedBall,dist_zero_right]
  rfl

lemma coordinateHalfBall_eq_preimage_upper (j:Fin n) (R:ℝ) :
    coordinateHalfBall j R=(dirichletCoordinateEquiv n).symm ⁻¹' upperCampanatoBall j 0 R := by
  ext x
  simp only [coordinateHalfBall,upperCampanatoBall,mem_inter_iff,mem_setOf_eq,mem_preimage,
    Metric.mem_ball,dist_zero_right]
  rfl

end GaussianTilt.MomentMapLinearDirichlet
