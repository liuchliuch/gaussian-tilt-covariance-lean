import GaussianTilt.MomentMapClassicalDirichletMixedBounds

/-!
# Constructed local barriers for mixed boundary derivatives

The tangent-field forcing is absorbed by an actual defining-function and
quadratic barrier. A one-sided derivative limit turns the pointwise estimate
into a boundary normal-derivative estimate.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- An explicit barrier absorbs a trace-weighted source on a compact patch. -/
theorem mixed_derivative_patch_barrier [NeZero n]
    {P : Set (CoordinateSpace n)} (hP : IsCompact P)
    {T w q : CoordinateSpace n → ℝ} (hTc : ContinuousOn T P)
    (hwc : ContinuousOn w P) (hqc : ContinuousOn q P)
    (hT : ∀ x ∈ interior P, ContDiffAt ℝ 2 T x)
    (hw : ∀ x ∈ interior P, ContDiffAt ℝ 2 w x)
    (hq : ∀ x ∈ interior P, ContDiffAt ℝ 2 q x)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ x ∈ interior P, (A x).PosDef)
    {M K κ : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hκ : 0 < κ)
    (hLT : ∀ x ∈ interior P, |linearizedMA (A x) T x| ≤ M * (A x).trace)
    (hLw : ∀ x ∈ interior P, κ * (A x).trace ≤ linearizedMA (A x) w x)
    (hLq : ∀ x ∈ interior P, linearizedMA (A x) q x ≤ (A x).trace)
    (hbT : ∀ x ∈ frontier P, |T x| ≤ K * q x)
    (hbw : ∀ x ∈ frontier P, w x ≤ 0) :
    ∀ x ∈ P, |T x| ≤ K * q x - ((K + M) / κ) * w x := by
  let B := (K + M) / κ
  have hB : 0 ≤ B := div_nonneg (add_nonneg hK hM) hκ.le
  have hBκ : B * κ = K + M := div_mul_cancel₀ _ hκ.ne'
  let ψ : CoordinateSpace n → ℝ := fun x => K * q x - B * w x
  have hψc : ContinuousOn ψ P := (continuousOn_const.mul hqc).sub (continuousOn_const.mul hwc)
  have hψd (x : CoordinateSpace n) (hx : x ∈ interior P) : ContDiffAt ℝ 2 ψ x :=
    (contDiffAt_const.mul (hq x hx)).sub (contDiffAt_const.mul (hw x hx))
  have hLψ (x : CoordinateSpace n) (hx : x ∈ interior P) :
      linearizedMA (A x) ψ x ≤ -M * (A x).trace := by
    rw [linearizedMA_sub_at _ (contDiffAt_const.mul (hq x hx)) (contDiffAt_const.mul (hw x hx)),
      linearizedMA_const_mul_at _ (hq x hx), linearizedMA_const_mul_at _ (hw x hx)]
    have hq' := mul_le_mul_of_nonneg_left (hLq x hx) hK
    have hw' := mul_le_mul_of_nonneg_left (hLw x hx) hB
    nlinarith [congrArg (fun z => z * (A x).trace) hBκ]
  have hbound (s : ℝ) (hs : |s| ≤ 1) : ∀ x ∈ P, s * T x - ψ x ≤ 0 := by
    apply classical_dirichlet_maximum_principle hP ((continuousOn_const.mul hTc).sub hψc)
      (fun x hx => (contDiffAt_const.mul (hT x hx)).sub (hψd x hx)) hA
    · intro x hx
      rw [linearizedMA_sub_at _ (contDiffAt_const.mul (hT x hx)) (hψd x hx),
        linearizedMA_const_mul_at _ (hT x hx)]
      have hb : |s * linearizedMA (A x) T x| ≤ M * (A x).trace := by
        rw [abs_mul]
        exact (mul_le_mul hs (hLT x hx) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      nlinarith [neg_abs_le (s * linearizedMA (A x) T x), hLψ x hx]
    · intro x hx
      have hsT : s * T x ≤ |T x| := by
        calc
          _ ≤ |s * T x| := le_abs_self _
          _ = |s| * |T x| := abs_mul _ _
          _ ≤ 1 * |T x| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
          _ = _ := one_mul _
      have hb := hbT x hx
      have hwx := hbw x hx
      dsimp [ψ]
      nlinarith
  intro x hx
  have hp := hbound 1 (by norm_num) x hx
  have hm := hbound (-1) (by norm_num) x hx
  change |T x| ≤ ψ x
  apply abs_le.mpr
  constructor <;> nlinarith

/-- One-sided pointwise domination gives an actual derivative bound at a
common zero. The positive parameter makes division preserve the order. -/
lemma abs_deriv_le_of_right_domination {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfg : ∀ᶠ t : ℝ in 𝓝[>] 0, |f t| ≤ g t) : |a| ≤ b := by
  have hft : Tendsto (fun t : ℝ => f t / t) (𝓝[>] 0) (𝓝 a) := by
    simpa [hf0, div_eq_mul_inv, mul_comm] using hf.tendsto_slope_zero_right
  have hgt : Tendsto (fun t : ℝ => g t / t) (𝓝[>] 0) (𝓝 b) := by
    simpa [hg0, div_eq_mul_inv, mul_comm] using hg.tendsto_slope_zero_right
  apply le_of_tendsto_of_tendsto hft.abs hgt
  filter_upwards [hfg, self_mem_nhdsWithin] with t ht ht0
  rw [abs_div, show |t| = t from abs_of_pos ht0]
  exact div_le_div_of_nonneg_right ht ht0.le

/-- The patch barrier yields the true normal derivative of the tangential
field at a boundary point. Only the actual inward path is assumed; for a
regular defining function it follows from its nonzero normal derivative. -/
theorem mixed_derivative_boundary_slope_bound
    {P : Set (CoordinateSpace n)} {T w q : CoordinateSpace n → ℝ}
    {x e : CoordinateSpace n} {K B : ℝ}
    (hT : DifferentiableAt ℝ T x) (hw : DifferentiableAt ℝ w x) (hq : DifferentiableAt ℝ q x)
    (hT0 : T x = 0) (hw0 : w x = 0) (hq0 : q x = 0)
    (hDq : fderiv ℝ q x e = 0)
    (hpath : ∀ᶠ t : ℝ in 𝓝[>] 0, x - t • e ∈ P)
    (hbound : ∀ y ∈ P, |T y| ≤ K * q y - B * w y) :
    |fderiv ℝ T x e| ≤ B * fderiv ℝ w x e := by
  have hl : HasDerivAt (fun t : ℝ => x - t • e) (-e) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) x).sub ((hasDerivAt_id (0 : ℝ)).smul_const e)
  have hTd := (show HasFDerivAt T (fderiv ℝ T x) (x - (0 : ℝ) • e) by
    simpa using hT.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hl
  have hwd := (show HasFDerivAt w (fderiv ℝ w x) (x - (0 : ℝ) • e) by
    simpa using hw.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hl
  have hqd := (show HasFDerivAt q (fderiv ℝ q x) (x - (0 : ℝ) • e) by
    simpa using hq.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hl
  have hψd := (hqd.const_mul K).sub (hwd.const_mul B)
  have hb := abs_deriv_le_of_right_domination hTd hψd
    (by simpa using hT0) (by simp [hq0, hw0])
    (hpath.mono (fun t ht => hbound _ ht))
  simpa only [map_neg, hDq, neg_zero, mul_zero, zero_sub, neg_mul, mul_neg, neg_neg, abs_neg] using hb

/-- A transverse defining derivative supplies the actual inward path into
a small closed sublevel patch, rather than postulating a boundary chart path. -/
theorem eventually_in_defining_patch {w q : CoordinateSpace n → ℝ}
    {x e : CoordinateSpace n} (hw : DifferentiableAt ℝ w x) (hq : ContinuousAt q x)
    (hw0 : w x = 0) (hwe : 0 < fderiv ℝ w x e) {r : ℝ} (hqr : q x < r) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, x - t • e ∈ {y | w y ≤ 0} ∩ {y | q y ≤ r} := by
  have hl : HasDerivAt (fun t : ℝ => x - t • e) (-e) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) x).sub ((hasDerivAt_id (0 : ℝ)).smul_const e)
  have hwd := (show HasFDerivAt w (fderiv ℝ w x) (x - (0 : ℝ) • e) by
    simpa using hw.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hl
  have hs : Tendsto (fun t : ℝ => w (x - t • e) / t) (𝓝[>] 0)
      (𝓝 (-fderiv ℝ w x e)) := by
    simpa [hw0, div_eq_mul_inv, mul_comm] using hwd.tendsto_slope_zero_right
  have hneg : ∀ᶠ t : ℝ in 𝓝[>] 0, w (x - t • e) / t < 0 :=
    hs.eventually (eventually_lt_nhds (neg_neg_of_pos hwe))
  have hqc : ContinuousAt (fun t : ℝ => q (x - t • e)) 0 := by
    exact (show ContinuousAt q (x - (0 : ℝ) • e) by simpa using hq).comp
      (f := fun t : ℝ => x - t • e) hl.continuousAt
  have hqnear : ∀ᶠ t : ℝ in 𝓝 0, q (x - t • e) < r :=
    hqc.eventually (eventually_lt_nhds (by simpa using hqr))
  filter_upwards [hneg, self_mem_nhdsWithin, nhdsWithin_le_nhds hqnear] with t hwt ht hqt
  refine ⟨?_, hqt.le⟩
  have h := (div_lt_iff₀ ht).mp hwt
  simpa only [zero_mul] using h.le

end GaussianTilt.MomentMapRegularity
