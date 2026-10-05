import GaussianTilt.MomentMapCalabiMetric
import GaussianTilt.MomentMapRegularityAffineHessian
import GaussianTilt.LetwinStein
import GaussianTilt.MomentMapRegularityConstantDensityEquation

/-! # Actual affine derivative transfer for Calabi's energy -/
noncomputable section
open Matrix Filter Set
open scoped BigOperators ContDiff Topology
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateHessian_comp_matrix {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) (R : Matrix (Fin n) (Fin n) ℝ) (x : CoordinateSpace n) :
    coordinateHessian (u ∘ coordinateMatrixMap R) x = Rᵀ * coordinateHessian u (R *ᵥ x) * R := by
  ext i j
  rw [coordinateHessian_comp_linear hu]
  simp only [coordinateMatrixMap_apply, Matrix.mulVec_single_one, Matrix.col,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma coordinateThirdDerivative_comp_matrix {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (R : Matrix (Fin n) (Fin n) ℝ) (x : CoordinateSpace n) :
    coordinateThirdDerivative (u ∘ coordinateMatrixMap R) x =
      cubicTransform R (coordinateThirdDerivative u (R *ᵥ x)) := by
  funext i j k
  change coordinateDerivative k (fun y => coordinateHessian (u ∘ coordinateMatrixMap R) y i j) x = _
  have hfun : (fun y => coordinateHessian (u ∘ coordinateMatrixMap R) y i j) =
      (fun y => ∑ a, ∑ b, (R a i * R b j) * coordinateHessian u (coordinateMatrixMap R y) a b) := by
    funext y
    rw [coordinateHessian_comp_linear (contDiff_infty.mp hu 2)]
    simp only [coordinateMatrixMap_apply, Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply]
  rw [hfun]
  have hs (a b : Fin n) : Differentiable ℝ (fun y => coordinateHessian u (coordinateMatrixMap R y) a b) :=
    (smooth_coordinateHessian hu a b).differentiable (by simp) |>.comp (coordinateMatrixMap R).differentiable
  rw [coordinateDerivative_sum _ (fun a => Differentiable.fun_sum (fun b _ => (hs a b).const_mul _))]
  unfold cubicTransform
  apply Finset.sum_congr rfl
  intro a _
  rw [coordinateDerivative_sum _ (fun b => (hs a b).const_mul _)]
  apply Finset.sum_congr rfl
  intro b _
  rw [coordinateDerivative_const_mul (hs a b)]
  change (R a i * R b j) * coordinateDerivative k ((fun y => coordinateHessian u y a b) ∘ coordinateMatrixMap R) x = _
  rw [coordinateDerivative_comp_matrix ((smooth_coordinateHessian hu a b).differentiable (by simp))]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, coordinateGradient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  unfold coordinateThirdDerivative
  ring

lemma inverse_congruence_cancel (H R : Matrix (Fin n) (Fin n) ℝ) (hR : R.det ≠ 0) :
    R * (Rᵀ * H * R)⁻¹ * Rᵀ = H⁻¹ := by
  have hR' : IsUnit R.det := isUnit_iff_ne_zero.mpr hR
  have hRt' : IsUnit Rᵀ.det := by simpa using hR'
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  calc
    R * (R⁻¹ * (H⁻¹ * Rᵀ⁻¹)) * Rᵀ = (R * R⁻¹) * H⁻¹ * (Rᵀ⁻¹ * Rᵀ) := by noncomm_ring
    _ = _ := by rw [Matrix.mul_nonsing_inv R hR', Matrix.nonsing_inv_mul Rᵀ hRt']; simp

/-- The actual sixfold third-derivative energy is transported under any
invertible source matrix, with no tensor transformation premise. -/
theorem actual_cubicMetricEnergy_comp_matrix {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.det ≠ 0) (x : CoordinateSpace n) :
    cubicMetricEnergy (coordinateHessian (u ∘ coordinateMatrixMap R) x)⁻¹
      (coordinateThirdDerivative (u ∘ coordinateMatrixMap R) x) =
    cubicMetricEnergy (coordinateHessian u (R *ᵥ x))⁻¹ (coordinateThirdDerivative u (R *ᵥ x)) := by
  rw [coordinateHessian_comp_matrix (contDiff_infty.mp hu 2), coordinateThirdDerivative_comp_matrix hu]
  exact cubicMetricEnergy_affine_invariant _ _ _ _ (inverse_congruence_cancel _ R hR)

lemma linearizedMA_comp_matrix {f : CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (A B R : Matrix (Fin n) (Fin n) ℝ)
    (hmetric : R * B * Rᵀ = A) (x : CoordinateSpace n) :
    linearizedMA B (f ∘ coordinateMatrixMap R) x = linearizedMA A f (R *ᵥ x) := by
  unfold linearizedMA
  rw [coordinateHessian_comp_matrix hf]
  have he : B * (Rᵀ * coordinateHessian f (R *ᵥ x) * R) =
      (B * Rᵀ * coordinateHessian f (R *ᵥ x)) * R := by noncomm_ring
  rw [he, Matrix.trace_mul_comm]
  congr 1
  rw [show R * (B * Rᵀ * coordinateHessian f (R *ᵥ x)) =
    (R * B * Rᵀ) * coordinateHessian f (R *ᵥ x) by noncomm_ring, hmetric]

lemma adjugate_congruence_cancel (H R : Matrix (Fin n) (Fin n) ℝ) (hR : R.det = 1) :
    R * (Rᵀ * H * R).adjugate * Rᵀ = H.adjugate := by
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
  calc
    R * (R.adjugate * (H.adjugate * Rᵀ.adjugate)) * Rᵀ =
        (R * R.adjugate) * H.adjugate * (Rᵀ.adjugate * Rᵀ) := by noncomm_ring
    _ = _ := by rw [Matrix.mul_adjugate, Matrix.adjugate_mul, Matrix.det_transpose, hR]; simp

/-- The smooth adjugate representative has the same exact affine invariance
under unimodular changes, even where the Hessian may be singular. -/
theorem adjugate_cubicMetricEnergy_comp_matrix {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.det = 1) (x : CoordinateSpace n) :
    cubicMetricEnergy (coordinateHessian (u ∘ coordinateMatrixMap R) x).adjugate
      (coordinateThirdDerivative (u ∘ coordinateMatrixMap R) x) =
    cubicMetricEnergy (coordinateHessian u (R *ᵥ x)).adjugate (coordinateThirdDerivative u (R *ᵥ x)) := by
  rw [coordinateHessian_comp_matrix (contDiff_infty.mp hu 2), coordinateThirdDerivative_comp_matrix hu]
  exact cubicMetricEnergy_affine_invariant _ _ _ _ (adjugate_congruence_cancel _ R hR)

def calabiAdjugateEnergy (u : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  cubicMetricEnergy (coordinateHessian u x).adjugate (coordinateThirdDerivative u x)

lemma contDiff_calabiAdjugateEnergy {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (calabiAdjugateEnergy u) := by
  have hA (a b : Fin n) : ContDiff ℝ ∞ (fun x => (coordinateHessian u x).adjugate a b) :=
    contDiff_matrix_adjugate (smooth_coordinateHessian hu) a b
  have hT (a b c : Fin n) : ContDiff ℝ ∞ (fun x => coordinateThirdDerivative u x a b c) :=
    smooth_coordinateDerivative (smooth_coordinateHessian hu a b) c
  unfold calabiAdjugateEnergy cubicMetricEnergy
  apply ContDiff.sum
  intro a _
  apply ContDiff.sum
  intro b _
  apply ContDiff.sum
  intro c _
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  apply ContDiff.sum
  intro k _
  exact ((((hA a i).mul (hA b j)).mul (hA c k)).mul (hT a b c)).mul (hT i j k)

lemma calabiAdjugateEnergy_comp_matrix {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.det = 1) :
    calabiAdjugateEnergy (u ∘ coordinateMatrixMap R) = calabiAdjugateEnergy u ∘ coordinateMatrixMap R := by
  funext x
  exact adjugate_cubicMetricEnergy_comp_matrix hu R hR x

lemma coordinateHessian_congr_nhds {f g : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (h : f =ᶠ[𝓝 x] g) : coordinateHessian f x = coordinateHessian g x := by
  ext i j
  have hd : coordinateDerivative i f =ᶠ[𝓝 x] coordinateDerivative i g := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun D : CoordinateSpace n →L[ℝ] ℝ => D (Pi.single i 1)) hy
  exact coordinateDerivative_congr_nhds hd j

/-- The smooth adjugate energy transports its actual second derivatives
under every determinant-one source change. -/
theorem linearized_calabiAdjugateEnergy_comp_matrix {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A B R : Matrix (Fin n) (Fin n) ℝ)
    (hR : R.det = 1) (hmetric : R * B * Rᵀ = A) (x : CoordinateSpace n) :
    linearizedMA B (calabiAdjugateEnergy (u ∘ coordinateMatrixMap R)) x =
      linearizedMA A (calabiAdjugateEnergy u) (R *ᵥ x) := by
  rw [calabiAdjugateEnergy_comp_matrix hu R hR]
  exact linearizedMA_comp_matrix (contDiff_infty.mp (contDiff_calabiAdjugateEnergy hu) 2) A B R hmetric x

lemma inverseRoot_det_one {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hdet : H.det = 1) : (Whitening.inverseRoot H).det = 1 := by
  have hr := (Whitening.root_posDef hH).det_pos
  have he := congrArg Matrix.det (Whitening.root_mul_root hH.posSemidef)
  rw [Matrix.det_mul, hdet] at he
  have hrd : (Whitening.root H).det = 1 := by nlinarith
  unfold Whitening.inverseRoot
  rw [Matrix.det_nonsing_inv, hrd]
  simp

/-- The actual inverse square root normalizes the Hessian and preserves
unit density; no determinant normalization is postulated. -/
theorem inverseRoot_normalizes_unit_hessian {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hdet : H.det = 1) :
    (Whitening.inverseRoot H).det = 1 ∧
      (Whitening.inverseRoot H)ᵀ * H * Whitening.inverseRoot H = 1 ∧
      Whitening.inverseRoot H * (Whitening.inverseRoot H)ᵀ = H⁻¹ := by
  refine ⟨inverseRoot_det_one hH hdet, ?_, ?_⟩
  · simpa only [(Whitening.inverseRoot_symm hH).eq] using Whitening.inverseRoot_covariance hH
  · rw [(Whitening.inverseRoot_symm hH).eq]
    unfold Whitening.inverseRoot
    rw [← Matrix.mul_inv_rev, Whitening.root_mul_root hH.posSemidef]

end GaussianTilt.MomentMapRegularity
