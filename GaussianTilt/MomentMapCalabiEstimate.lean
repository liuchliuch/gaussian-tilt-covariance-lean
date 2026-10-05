import GaussianTilt.MomentMapCalabiFifthReduction
import GaussianTilt.MomentMapCalabiNormalization
import GaussianTilt.MomentMapRegularityConstantDensityCalabiSymmetry

/-! # The genuine Calabi differential inequality

Actual differentiation of det Hess=1, the five-factor Leibniz rule, finite
reindexing, tensor square completion and exact affine metric transfer are
assembled here. No differential inequality is assumed.
-/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The true identity-Hessian Calabi inequality, including all differentiated
PDE and tensor contraction inputs. -/
theorem calabiAdjugateEnergy_inequality_at_identity (hn : 0 < n)
    {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1)
    (hI : coordinateHessian u x = 1) :
    calabiAdjugateEnergy u x ^ 2 / (2 * n) ≤ linearizedMA 1 (calabiAdjugateEnergy u) x := by
  let T := coordinateThirdDerivative u x
  let Q := coordinateFourthDerivative u x
  let P := fun a b c l => coordinateFifthDerivative u x a b c l l
  have hT : calabiTensorSymm T := calabiTensorSymm_actual hu x
  have hQcycle : ∀ a b c l, Q a b c l = Q l a b c := by
    intro a b c l
    dsimp [Q]
    rw [coordinateFourthDerivative_swap34 hu x a b c l,
      coordinateFourthDerivative_swap23 hu x a b l c,
      coordinateFourthDerivative_swap12 hu x a l b c]
  have hQ : ∀ a b, (∑ l, Q a b l l) = ∑ i, ∑ j, T a i j * T b i j :=
    fun a b => constant_density_fourth_contraction hu hMA hI a b
  have hP : ∀ a b c, (∑ l, P a b c l) =
      (∑ i, ∑ j, (Q a b i j * T c i j + Q a c i j * T b i j + Q b c i j * T a i j)) -
        2 * ∑ i, ∑ j, ∑ k, T a i j * T b j k * T c k i :=
    fun a b c => constant_density_fifth_contraction hu hMA hI a b c
  have hSlice (l : Fin n) : (show Matrix (Fin n) (Fin n) ℝ from fun a b => coordinateThirdDerivative u x a b l) = calabiSlice T l := by
    ext a b
    exact (calabiTensorSymm_cycle hT l a b).symm
  have hlap := linearized_calabiAdjugateEnergy_at_identity hu hMA hI
  dsimp only at hlap
  simp_rw [hSlice] at hlap
  change linearizedMA 1 (calabiAdjugateEnergy u) x =
    (∑ l, (3 * calabiContraction ((2 : ℝ) • (calabiSlice T l * calabiSlice T l) -
        (show Matrix (Fin n) (Fin n) ℝ from fun a b => Q a b l l)) 1 1 T T +
      6 * calabiContraction (-calabiSlice T l) (-calabiSlice T l) 1 T T +
      12 * calabiContraction (-calabiSlice T l) 1 1 (fun a b c => Q a b c l) T +
      2 * calabiContraction 1 1 1 (fun a b c => P a b c l) T +
      2 * calabiContraction 1 1 1 (fun a b c => Q a b c l) (fun a b c => Q a b c l))) at hlap
  rw [calabi_five_term_reduction T Q P hT hQcycle hQ hP] at hlap
  have he : calabiAdjugateEnergy u x = calabiCubicNorm T := by
    unfold calabiAdjugateEnergy
    rw [hI, Matrix.adjugate_one, cubicMetricEnergy_identity]
  rw [he, hlap]
  simpa only [Fintype.card_fin] using calabi_normalized_tensor_inequality T Q hT.2
    (coordinateFourthDerivative_swap23 hu x) (coordinateFourthDerivative_swap34 hu x)
    (by simpa using hn)

/-- Calabi's actual differential estimate in an arbitrary positive Hessian
metric, without normalization or derivative identities as premises. -/
theorem calabiAdjugateEnergy_differential_inequality (hn : 0 < n)
    {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) (x : CoordinateSpace n)
    (hH : (coordinateHessian u x).PosDef)
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1) :
    calabiAdjugateEnergy u x ^ 2 / (2 * n) ≤
      linearizedMA (coordinateHessian u x)⁻¹ (calabiAdjugateEnergy u) x := by
  apply calabi_inequality_of_identity_hessian hn ?_ hu x hH hMA
  intro v hv y hI hMA
  exact calabiAdjugateEnergy_inequality_at_identity hn hv hMA hI

/-- The same inequality for the literal inverse-Hessian cubic energy. -/
theorem calabiEnergy_differential_inequality (hn : 0 < n)
    {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) (x : CoordinateSpace n)
    (hH : (coordinateHessian u x).PosDef)
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1) :
    calabiEnergy u x ^ 2 / (2 * n) ≤
      linearizedMA (coordinateHessian u x)⁻¹ (calabiEnergy u) x := by
  have he : calabiEnergy u =ᶠ[𝓝 x] calabiAdjugateEnergy u := by
    filter_upwards [hMA] with y hy
    unfold calabiEnergy calabiAdjugateEnergy cubicMetricEnergy
    rw [matrix_inv_eq_adjugate_of_det_one hy]
  have hval := he.self_of_nhds
  have hhess := coordinateHessian_congr_nhds he
  unfold linearizedMA
  rw [hval, hhess]
  exact calabiAdjugateEnergy_differential_inequality hn hu x hH hMA

end GaussianTilt.MomentMapRegularity
