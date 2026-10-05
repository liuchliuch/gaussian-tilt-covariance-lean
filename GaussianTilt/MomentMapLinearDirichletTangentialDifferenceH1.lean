import GaussianTilt.MomentMapLinearDirichletTangentialDifferenceLimit
import GaussianTilt.MomentMapLinearDirichletTangentialDifferenceGeometry
import GaussianTilt.MomentMapLinearDirichletVariableWeakTangentialLoad

/-! # Genuine boundary H¹ regularity of tangential weak derivatives

The hypotheses are only an actual weak divergence equation, bounded
uniformly elliptic coefficients that are locally Lipschitz, and the
original H₀¹ jet. All tangential quotient energies and their H¹ limits
are constructed, including the zero flat trace of the derivative.
-/
noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- The real weak equation supplies the step-uniform load bound, so the
actual localized tangential weak derivative belongs to H₀¹. -/
theorem exists_tangential_h1_cutoff_of_weak_equation
    (q i : Fin n) (hi : i≠q) {r R : ℝ} (hrR : r<R)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ p k, AEStronglyMeasurable (fun x=>A x p k) volume)
    {K lam : ℝ} (hK : 0≤K) (hAb : ∀ p k, ∀ᵐ x ∂volume, |A x p k|≤K) (hlam : 0<lam)
    (hell : ∀ᵐ x ∂volume, ∀ z : Fin n→ℝ, lam*(∑ k,(z k)^2)≤z ⬝ᵥ (A x *ᵥ z))
    {L : ℝ≥0} (hLip : LipschitzOnWith L A (rawChartClosedBall R))
    (a : smoothCompactCore n) (ha : tsupport a.1⊆rawChartBall r)
    {B D : ℝ} (hB : 0≤B) (hD : 0≤D)
    (hb : ∀ x, |a.1 x|≤B) (hd : ∀ k x, |coordinateDerivative k a.1 x|≤D)
    (u : dirichletSobolev {x : CoordinateSpace n | 0<x q})
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (hweak : ∀ v : dirichletSobolev (coordinateHalfBall q R),
      variableJetEnergy A hAm hK hAb u.1 v.1=inner ℝ f (dirichletValue (coordinateHalfBall q R) v)) :
    ∃ v : dirichletSobolev (coordinateHalfBall q r),
      dirichletValue (coordinateHalfBall q r) v=smoothCoreL2Multiply a (u.1 i.succ) ∧
      ‖v‖≤cutoffEnergyBound n lam K B D (‖f‖+(n:ℝ)^2*(L:ℝ)*jetGradientNorm u.1) ‖u.1 i.succ‖ := by
  have hU : coordinateHalfBall q r⊆coordinateHalfBall q R := fun x hx=>⟨hx.1.trans hrR,hx.2⟩
  apply exists_tangential_cutoff_derivative_of_quotient_load_bound
    (U := coordinateHalfBall q r) (L := ‖f‖+(n:ℝ)^2*(L:ℝ)*jetGradientNorm u.1)
    q i hi A hAm hK hAb hlam hell a
    (fun x hx=>⟨ha hx.1,hx.2⟩) hB hD
    (add_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg _) L.coe_nonneg) (jetGradientNorm_nonneg _)))
    hb hd u (sub_pos.mpr hrR)
  intro h hh0 hh v
  exact weak_divergence_difference_quotient_load_bound (isOpen_coordinateHalfBall q r).measurableSet hU i h
    (tangential_halfBall_shift_subset q i hi hh) A hAm hK L.coe_nonneg hAb
    (fun x hx p k=>local_matrix_difference_quotient_bound hLip hrR (abs_pos.mp hh0) hh hx.1 i p k)
    u.1 f hweak v

/-- On any strictly smaller half-ball the original tangential weak
derivative is the actual value of a constructed H₀¹ jet. All cutoffs,
quotient tests, uniform energies and Hilbert weak limits are proved. -/
theorem exists_tangential_h1_on_halfBall
    (q i : Fin n) (hi : i≠q) {r₀ r R R₀ : ℝ} (hr₀r : r₀<r) (hrR : r<R)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ p k, AEStronglyMeasurable (fun x=>A x p k) volume)
    {K lam : ℝ} (hK : 0≤K) (hAb : ∀ p k, ∀ᵐ x ∂volume, |A x p k|≤K) (hlam : 0<lam)
    (hell : ∀ᵐ x ∂volume, ∀ z : Fin n→ℝ, lam*(∑ k,(z k)^2)≤z ⬝ᵥ (A x *ᵥ z))
    {L : ℝ≥0} (hLip : LipschitzOnWith L A (rawChartClosedBall R))
    (u : dirichletSobolev (coordinateHalfBall q R₀))
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (hweak : ∀ v : dirichletSobolev (coordinateHalfBall q R),
      variableJetEnergy A hAm hK hAb u.1 v.1=inner ℝ f (dirichletValue (coordinateHalfBall q R) v)) :
    ∃ v : dirichletSobolev (coordinateHalfBall q r),
      ∀ᵐ x ∂volume, x∈rawChartClosedBall r₀ →
        dirichletValue (coordinateHalfBall q r) v x=u.1 i.succ x := by
  have hbounded : Bornology.IsBounded (rawChartBall (n:=n) r) :=
    (isCompact_rawChartClosedBall (n:=n) r).isBounded.subset (fun x hx=>(show ‖(coordinateEquiv n).symm x‖<r from hx).le)
  have hcompact : IsCompact (rawChartClosedBall (n:=n) r₀) := isCompact_rawChartClosedBall r₀
  have hinside : rawChartClosedBall (n:=n) r₀⊆rawChartBall r := fun x hx=>(show ‖(coordinateEquiv n).symm x‖≤r₀ from hx).trans_lt hr₀r
  obtain ⟨a,ha,hone⟩ := exists_smooth_interior_cutoff (isOpen_rawChartBall r) hbounded hcompact hinside
  obtain ⟨B,hB⟩ := a.2.2.exists_bound_of_continuous a.2.1.continuous
  obtain ⟨D,hD⟩ := (a.2.2.fderiv ℝ).exists_bound_of_continuous (a.2.1.continuous_fderiv (by simp))
  have hB0 : 0≤B := (norm_nonneg _).trans (hB 0)
  have hD0 : 0≤D := (norm_nonneg _).trans (hD 0)
  have hd (k : Fin n) (x : CoordinateSpace n) : |coordinateDerivative k a.1 x|≤D := by
    have hh := (fderiv ℝ a.1 x).le_opNorm (Pi.single k 1)
    simp only [Pi.norm_single,norm_one,mul_one,Real.norm_eq_abs] at hh
    exact hh.trans (hD x)
  let u' : dirichletSobolev {x : CoordinateSpace n | 0<x q} := dirichletInclusion (fun _ hx=>hx.2) u
  obtain ⟨v,hv,_⟩ := exists_tangential_h1_cutoff_of_weak_equation q i hi hrR A hAm hK hAb hlam hell hLip
    a ha hB0 hD0 hB hd u' f hweak
  refine ⟨v,?_⟩
  rw [hv]
  filter_upwards [smoothCoreL2Multiply_ae a (u'.1 i.succ)] with x hx hxball
  change smoothCoreL2Multiply a (u'.1 i.succ) x=u'.1 i.succ x
  rw [hx,hone hxball]
  simp only [Pi.one_apply,one_mul]

end GaussianTilt.MomentMapLinearDirichlet
