import GaussianTilt.LetwinMomentLaw

/-! # The genuine smooth positive-Hessian gradient map -/
noncomputable section
open MeasureTheory Matrix Set
open scoped BigOperators ContDiff Topology
namespace GaussianTilt.Letwin

lemma contDiff_coordinateGradient {n : ℕ} {φ : CoordinateSpace n → ℝ}
    {m k : WithTop ℕ∞} (hφ : ContDiff ℝ k φ) (hm : m+1≤k) :
    ContDiff ℝ m (coordinateGradient φ) :=
  contDiff_pi.mpr (fun i => contDiff_coordinateDerivative hφ hm i)

lemma hasFDerivAt_coordinateGradient {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (x : CoordinateSpace n) :
    HasFDerivAt (coordinateGradient φ) (coordinateMatrixMap (coordinateHessian φ x)) x := by
  have hd (i : Fin n) : Differentiable ℝ (coordinateDerivative i φ) :=
    (contDiff_coordinateDerivative hφ (m := 1) (by norm_num) i).differentiable le_rfl
  have hgrad : Differentiable ℝ (coordinateGradient φ) := differentiable_pi.mpr hd
  convert (hgrad x).hasFDerivAt using 1
  ext v i
  change (coordinateMatrixMap (coordinateHessian φ x)) v i =
    (fderiv ℝ (fun y j => coordinateDerivative j φ y) x) v i
  rw [fderiv_pi (fun i => hd i x)]
  simp only [ContinuousLinearMap.pi_apply, coordinateMatrixMap_apply]
  rw [fderiv_apply_eq_sum_coordinates]
  simp only [Matrix.mulVec, dotProduct, coordinateHessian, mul_comm]

lemma det_coordinateMatrixMap {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (coordinateMatrixMap M).det=M.det := by
  exact LinearMap.det_toLin' M

/-- Positive Hessian makes the gradient globally injective. The proof uses
strict increase of the derivative along the actual line joining two points. -/
theorem coordinateGradient_injective_of_posDef {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hH : ∀ x, (coordinateHessian φ x).PosDef) :
    Function.Injective (coordinateGradient φ) := by
  intro x y hxy
  by_contra hne
  let d := y-x
  have hd : d≠0 := sub_ne_zero.mpr (Ne.symm hne)
  let F := fun t : ℝ => φ (x+t•d)
  have hstrict : StrictMono (deriv F) := by
    apply strictMono_of_deriv_pos
    intro t
    rw [second_deriv_affine_line_comp hφ x d t,
      secondFDeriv_eq_hessianQuadratic hφ.contDiffAt]
    simpa only [matrixQuadratic, star_trivial] using (hH (x+t•d)).2 d hd
  have hend : deriv F 0=deriv F 1 := by
    rw [deriv_affine_line_comp (hφ.differentiable (by norm_num)),
      deriv_affine_line_comp (hφ.differentiable (by norm_num))]
    simp only [zero_smul, add_zero, one_smul]
    have he : x+d=y := by dsimp [d]; abel
    rw [he, fderiv_apply_eq_sum_coordinates, fderiv_apply_eq_sum_coordinates]
    change (∑ i, d i*coordinateGradient φ x i) = ∑ i, d i*coordinateGradient φ y i
    rw [hxy]
  have hlt := hstrict (show (0 : ℝ)<1 by norm_num)
  exact (ne_of_lt hlt) hend

lemma hasFDerivAt_coordinateGradient_equiv {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (x : CoordinateSpace n) (hH : (coordinateHessian φ x).PosDef) :
    HasFDerivAt (coordinateGradient φ)
      (coordinateMatrixEquiv (coordinateHessian φ x) hH.det_pos.ne').toContinuousLinearMap x := by
  convert hasFDerivAt_coordinateGradient hφ x using 1

/-- The inverse function theorem is applied to the actual gradient and its
actual Hessian, producing a genuine local homeomorphism at every source point. -/
theorem coordinateGradient_localDiffeomorphism {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hH : ∀ x, (coordinateHessian φ x).PosDef) (x : CoordinateSpace n) :
    ∃ e : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n),
      x∈e.source ∧ (e : CoordinateSpace n → CoordinateSpace n)=coordinateGradient φ := by
  have hg : ContDiff ℝ 1 (coordinateGradient φ) := contDiff_coordinateGradient hφ (by norm_num)
  have hd := hasFDerivAt_coordinateGradient_equiv hφ x (hH x)
  exact ⟨hg.contDiffAt.toOpenPartialHomeomorph _ hd le_rfl,
    hg.contDiffAt.mem_toOpenPartialHomeomorph_source hd le_rfl, rfl⟩

/-- Global openness follows from the pointwise inverse function theorem. -/
theorem coordinateGradient_isOpenMap {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hH : ∀ x, (coordinateHessian φ x).PosDef) :
    IsOpenMap (coordinateGradient φ) := by
  have hg : ContDiff ℝ 1 (coordinateGradient φ) := contDiff_coordinateGradient hφ (by norm_num)
  exact isOpenMap_of_hasStrictFDerivAt_equiv (fun x =>
    hg.contDiffAt.hasStrictFDerivAt' (hasFDerivAt_coordinateGradient_equiv hφ x (hH x)) le_rfl)

lemma coordinateGradient_range_open {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hH : ∀ x, (coordinateHessian φ x).PosDef) :
    IsOpen (Set.range (coordinateGradient φ)) := by
  simpa only [image_univ] using coordinateGradient_isOpenMap hφ hH Set.univ isOpen_univ

/-- Smoothness and injectivity yield the genuine measurable embedding needed
for Jacobian change of variables and equality of pullback densities. -/
lemma coordinateGradient_measurableEmbedding {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hH : ∀ x, (coordinateHessian φ x).PosDef) :
    MeasurableEmbedding (coordinateGradient φ) := by
  exact (continuous_coordinateGradient (hφ.of_le (by norm_num))).measurableEmbedding
    (coordinateGradient_injective_of_posDef hφ hH)

/-- For a smooth positive-Hessian potential, the constructed local inverse
is genuinely smooth on its open target. -/
theorem coordinateGradient_localSmoothDiffeomorphism {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hH : ∀ x, (coordinateHessian φ x).PosDef) (x : CoordinateSpace n) :
    ∃ e : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n),
      x∈e.source ∧ (e : CoordinateSpace n → CoordinateSpace n)=coordinateGradient φ ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  have hφ2 := contDiff_infty.mp hφ 2
  have hg : ContDiff ℝ ∞ (coordinateGradient φ) :=
    contDiff_pi.mpr (fun i => smooth_coordinateDerivative hφ i)
  obtain ⟨e,hx,he⟩ := coordinateGradient_localDiffeomorphism hφ2 hH x
  refine ⟨e,hx,he,?_⟩
  intro y hy
  apply (e.contDiffAt_symm (f₀' := coordinateMatrixEquiv (coordinateHessian φ (e.symm y))
    (hH (e.symm y)).det_pos.ne') hy ?_ ?_).contDiffWithinAt
  · rw [he]
    exact hasFDerivAt_coordinateGradient_equiv hφ2 _ (hH _)
  · rw [he]
    exact hg.contDiffAt

/-- Strict convexity already gives gradient injectivity before positive
Hessian eigenvalues have been established. -/
theorem coordinateGradient_injective_of_strictConvex {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : Differentiable ℝ φ) (hc : StrictConvexOn ℝ univ φ) :
    Function.Injective (coordinateGradient φ) := by
  intro x y hxy
  by_contra hne
  let d := y-x
  have hd : d≠0 := sub_ne_zero.mpr (Ne.symm hne)
  have hlineinj : Function.Injective (fun t : ℝ => x+t•d) := by
    intro s t hst
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hd
    have he := congrFun hst i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at he
    exact mul_right_cancel₀ hi (add_left_cancel he)
  let F := fun t : ℝ => φ (x+t•d)
  have hFc : StrictConvexOn ℝ univ F := by
    refine ⟨convex_univ,?_⟩
    intro s _ t _ hst a b ha hb hab
    have he : a•(x+s•d)+b•(x+t•d)=x+(a*s+b*t)•d := by
      calc
        _ = (a+b)•x+(a*s+b*t)•d := by module
        _ = _ := by rw [hab,one_smul]
    have h := hc.2 (mem_univ _) (mem_univ _) (fun h => hst (hlineinj h)) ha hb hab
    simpa only [he,smul_eq_mul,F] using h
  have hFd : Differentiable ℝ F := hφ.comp (by fun_prop)
  have hstrict : StrictMono (deriv F) := by
    exact strictMonoOn_univ.mp (hFc.strictMonoOn_deriv (fun t _ => hFd t))
  have hend : deriv F 0=deriv F 1 := by
    rw [deriv_affine_line_comp hφ, deriv_affine_line_comp hφ]
    simp only [zero_smul,add_zero,one_smul]
    have he : x+d=y := by dsimp [d]; abel
    rw [he,fderiv_apply_eq_sum_coordinates,fderiv_apply_eq_sum_coordinates]
    change (∑ i, d i*coordinateGradient φ x i)=∑ i, d i*coordinateGradient φ y i
    rw [hxy]
  exact (ne_of_lt (hstrict (show (0 : ℝ)<1 by norm_num))) hend

end GaussianTilt.Letwin
