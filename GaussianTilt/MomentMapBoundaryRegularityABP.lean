import GaussianTilt.MomentMapBoundaryRegularityContact

/-!
# A genuine smooth ABP inequality

The coefficient field need not be continuous. Only a uniform lower
ellipticity bound is used. The tested function need not be convex: its
lower contact set supplies precisely the positive Hessians needed for the
determinant estimate and the area inequality.
-/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped Topology BigOperators ContDiff Gradient ENNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma posSemidef_diagonal_nonneg {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosSemidef) (i : Fin n) : 0 ≤ H i i := by
  have h := hH.2 (Pi.single i 1)
  simpa only [star_trivial, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
    single_dotProduct, Matrix.col_apply, one_mul] using h

lemma posSemidef_diagonal_le_trace {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosSemidef) (i : Fin n) : H i i ≤ H.trace := by
  exact Finset.single_le_sum (fun j _ => posSemidef_diagonal_nonneg hH j) (Finset.mem_univ i)

/-- A coarse determinant-versus-trace bound, derived from positivity and
the permutation formula. Sharp arithmetic-geometric means are unnecessary. -/
lemma posSemidef_det_le_factorial_trace {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosSemidef) : H.det ≤ (n.factorial : ℝ) * H.trace ^ n := by
  have he := abs_entry_le_of_posSemidef_diagonal_bound hH
    (posSemidef_diagonal_le_trace hH)
  have hd := Matrix.det_le (A := H) (abv := AbsoluteValue.abs) he
  simpa only [AbsoluteValue.abs_apply, abs_of_nonneg hH.det_nonneg,
    Fintype.card_fin, nsmul_eq_mul] using hd

/-- Uniform ellipticity gives the genuine determinant bound at a lower
contact point. No bound on individual Hessian entries is assumed. -/
lemma contact_determinant_bound {A H : Matrix (Fin n) (Fin n) ℝ}
    {lam f : ℝ} (hlam : 0 < lam) (hA : (A - lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hH : H.PosSemidef) (hLf : (A * H).trace ≤ f) :
    H.det ≤ (n.factorial : ℝ) * (max f 0 / lam)^n := by
  have hp := trace_mul_nonneg_of_posSemidef _ _ hA hH
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul] at hp
  have ht : H.trace ≤ max f 0 / lam := by
    apply (le_div_iff₀ hlam).mpr
    nlinarith [le_max_left f 0]
  exact (posSemidef_det_le_factorial_trace hH).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH.trace_nonneg ht n) (Nat.cast_nonneg _))

/-- ABP in its direct slope-volume form. The right side only sees the
positive part of the actual forcing on the lower contact set. -/
theorem smooth_abp_contact_bound {S : Set (E n)} {u : E n → ℝ}
    (hS : IsCompact S) (hu : ContDiff ℝ ∞ u) {x : E n} (hx : x ∈ S)
    {D lam : ℝ} (hD : 0 < D) (hdiam : Metric.diam S ≤ D) (hlam : 0 < lam)
    (hneg : u x < 0) (hb : ∀ y ∈ frontier S, 0 ≤ u y)
    {A : E n → Matrix (Fin n) (Fin n) ℝ} {f : E n → ℝ}
    (hA : ∀ y ∈ lowerContactSet S u, (A y - lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hL : ∀ y ∈ lowerContactSet S u,
      linearizedMA (A y) (coordinatePullback u) (coordinateEquiv n y) ≤ f y) :
    volume (Metric.ball (0 : E n) (-u x / D)) ≤
      ∫⁻ y in lowerContactSet S u, ENNReal.ofReal ((n.factorial : ℝ) * (max (f y) 0 / lam)^n) := by
  calc
    _ ≤ volume (gradient u '' lowerContactSet S u) :=
      measure_mono (ball_subset_gradient_lowerContactSet hS hu hx hD hdiam hneg hb)
    _ ≤ ∫⁻ y in lowerContactSet S u,
        ENNReal.ofReal (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).det :=
      gradient_lowerContactSet_volume_le hu
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_lowerContactSet hu)] with y hy
      exact ENNReal.ofReal_le_ofReal (contact_determinant_bound hlam (hA y hy)
        (hessian_posSemidef_of_lower_contact hu hy) (hL y hy))

/-- The usual domain-integral ABP estimate follows by enlarging the contact
set. Neither convexity of the domain nor convexity of the function is needed. -/
theorem smooth_abp_bound {S : Set (E n)} {u : E n → ℝ}
    (hS : IsCompact S) (hu : ContDiff ℝ ∞ u) {x : E n} (hx : x ∈ S)
    {D lam : ℝ} (hD : 0 < D) (hdiam : Metric.diam S ≤ D) (hlam : 0 < lam)
    (hneg : u x < 0) (hb : ∀ y ∈ frontier S, 0 ≤ u y)
    {A : E n → Matrix (Fin n) (Fin n) ℝ} {f : E n → ℝ}
    (hA : ∀ y ∈ interior S, (A y - lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hL : ∀ y ∈ interior S,
      linearizedMA (A y) (coordinatePullback u) (coordinateEquiv n y) ≤ f y) :
    volume (Metric.ball (0 : E n) (-u x / D)) ≤
      ∫⁻ y in S, ENNReal.ofReal ((n.factorial : ℝ) * (max (f y) 0 / lam)^n) := by
  exact (smooth_abp_contact_bound hS hu hx hD hdiam hlam hneg hb
    (fun y hy => hA y hy.1) (fun y hy => hL y hy.1)).trans
      (lintegral_mono_set (fun _ hy => interior_subset hy.1))

end GaussianTilt.MomentMapRegularity
