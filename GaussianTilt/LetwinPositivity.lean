import GaussianTilt.LetwinBochner

/-! # Positivity in the moment-map Hessian identity -/
noncomputable section
open Matrix MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.Letwin

lemma coordinateHessian_eq_secondFDerivAt {n : ℕ} {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : ContDiffAt ℝ 2 f x) (i j : Fin n) :
    coordinateHessian f x i j =
      fderiv ℝ (fderiv ℝ f) x (Pi.single j 1) (Pi.single i 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  change (fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x) (Pi.single j 1) = _
  rw [fderiv_clm_apply hd (differentiableAt_const (Pi.single i 1))]
  simp

lemma coordinateHessian_isSymm_at {n : ℕ} {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : ContDiffAt ℝ 2 f x) : (coordinateHessian f x).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, coordinateHessian_eq_secondFDerivAt hf]
  exact hf.isSymmSndFDerivAt (by simp) _ _

lemma secondFDeriv_eq_hessianQuadratic {n : ℕ} {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : ContDiffAt ℝ 2 f x) (v : CoordinateSpace n) :
    fderiv ℝ (fderiv ℝ f) x v v = matrixQuadratic (coordinateHessian f x) v := by
  have hv : (∑ i, v i • (Pi.single i 1 : CoordinateSpace n)) = v := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [← hv]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  simp only [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum,
    coordinateHessian_eq_secondFDerivAt hf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hf.isSymmSndFDerivAt (by simp) (Pi.single i 1) (Pi.single j 1)]
  ring

/-- A convex C² potential has nonnegative second derivative along every line,
proved on an arbitrary open convex domain using monotonicity of its scalar
line derivative. -/
theorem hessianQuadratic_nonneg_of_convex {n : ℕ} {f : CoordinateSpace n → ℝ}
    {U : Set (CoordinateSpace n)} (hU : IsOpen U) (hc : ConvexOn ℝ U f)
    (hf : ContDiffOn ℝ 2 f U) {x : CoordinateSpace n} (hx : x ∈ U) (v : CoordinateSpace n) :
    0 ≤ matrixQuadratic (coordinateHessian f x) v := by
  let l : ℝ →ᵃ[ℝ] CoordinateSpace n := AffineMap.lineMap x (x + v)
  let D : Set ℝ := l ⁻¹' U
  have hl (t : ℝ) : HasDerivAt (l : ℝ → CoordinateSpace n) v t := by
    simpa [l] using (AffineMap.hasDerivAt_lineMap (a := x) (b := x + v) (x := t))
  have hl0 : l 0 = x := by simp [l]
  have hD : IsOpen D := hU.preimage (continuous_iff_continuousAt.mpr (fun t => (hl t).continuousAt))
  have hD0 : D ∈ 𝓝 (0 : ℝ) := hD.mem_nhds (by simpa [D, hl0] using hx)
  have hfc : ConvexOn ℝ D (f ∘ l) := hc.comp_affineMap l
  have hfd (t : ℝ) (ht : t ∈ D) : DifferentiableAt ℝ f (l t) :=
    (hf.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)
  have hmono : MonotoneOn (deriv (f ∘ l)) D :=
    hfc.monotoneOn_deriv (fun t ht => (hfd t ht).comp t (hl t).differentiableAt)
  have hnonneg : 0 ≤ deriv (deriv (f ∘ l)) 0 := by
    have h := hmono.derivWithin_nonneg (x := (0 : ℝ))
    rwa [derivWithin_of_mem_nhds hD0] at h
  have hfx : ContDiffAt ℝ 2 f x := hf.contDiffAt (hU.mem_nhds hx)
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hfx.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  have hDf' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (l 0) := by
    simpa only [hl0] using hDf.hasFDerivAt
  have hB : HasDerivAt (fun t => fderiv ℝ f (l t)) (fderiv ℝ (fderiv ℝ f) x v) 0 := by
    simpa only [hl0] using (hDf'.comp_hasDerivAt 0 (hl 0))
  have hG : HasDerivAt (fun t => fderiv ℝ f (l t) v)
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    simpa using hB.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have heq : deriv (f ∘ l) =ᶠ[𝓝 (0 : ℝ)] (fun t => fderiv ℝ f (l t) v) := by
    filter_upwards [hD0] with t ht
    exact ((hfd t ht).hasFDerivAt.comp_hasDerivAt t (hl t)).deriv
  have hactual := hG.congr_of_eventuallyEq heq
  rw [hactual.deriv, secondFDeriv_eq_hessianQuadratic hfx] at hnonneg
  exact hnonneg

/-- Hessian positivity is derived from actual convexity, rather than made an
extra matrix assumption. -/
theorem coordinateHessian_posSemidef_of_convex {n : ℕ} {f : CoordinateSpace n → ℝ}
    {U : Set (CoordinateSpace n)} (hU : IsOpen U) (hc : ConvexOn ℝ U f)
    (hf : ContDiffOn ℝ 2 f U) {x : CoordinateSpace n} (hx : x ∈ U) :
    (coordinateHessian f x).PosSemidef := by
  constructor
  · have hs := coordinateHessian_isSymm_at (hf.contDiffAt (hU.mem_nhds hx))
    simpa only [Matrix.IsSymm, Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hs
  · intro v
    simpa only [star_trivial, matrixQuadratic] using hessianQuadratic_nonneg_of_convex hU hc hf hx v

section MatrixGram
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
lemma matrix_hs_gram_posSemidef (F : κ → Matrix ι ι ℝ) :
    Matrix.PosSemidef (fun i j : κ => ∑ a, ∑ b, F i a b * F j a b) := by
  let D : Matrix (ι × ι) κ ℝ := fun p i => F i p.1 p.2
  have h := Matrix.posSemidef_conjTranspose_mul_self D
  convert h using 1
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, D, Fintype.sum_prod_type]

open scoped MatrixOrder in
/-- The normalized third-derivative remainder is a genuine weighted Gram
matrix. Its positivity follows from a proved square-root factorization. -/
theorem weighted_trace_gram_posSemidef (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (T : κ → Matrix ι ι ℝ) (hT : ∀ i, (T i).IsSymm) :
    Matrix.PosSemidef (fun i j : κ => Matrix.trace (A * T j * A * T i)) := by
  let R := CFC.sqrt A
  have hRp : R.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hR : R.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hRp.isHermitian
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  let F := fun i => R * T i * R
  have hF (i : κ) : (F i).IsSymm := by
    dsimp [F]
    change (R * T i * R).transpose = _
    simp only [Matrix.transpose_mul, hR.eq, (hT i).eq]
    rw [Matrix.mul_assoc]
  have htrace (i j : κ) : Matrix.trace (F j * F i) = Matrix.trace (A * T j * A * T i) := by
    calc
      Matrix.trace (F j * F i) = Matrix.trace (R * (T j * (R * R) * T i * R)) := by
        dsimp [F]
        congr 1
        noncomm_ring
      _ = Matrix.trace ((T j * (R * R) * T i * R) * R) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((T j * A * T i) * A) := by
        rw [show (T j * (R * R) * T i * R) * R = (T j * (R * R) * T i) * (R * R) by noncomm_ring, hRR]
      _ = Matrix.trace (A * (T j * A * T i)) := Matrix.trace_mul_comm _ _
      _ = _ := by congr 1; noncomm_ring
  have heq : (fun i j => Matrix.trace (A * T j * A * T i) : Matrix κ κ ℝ) =
      (fun i j => ∑ a, ∑ b, F i a b * F j a b) := by
    ext i j
    rw [← htrace i j]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [(hF i).apply a b]
    ring
  rw [heq]
  exact matrix_hs_gram_posSemidef F

open scoped MatrixOrder in
lemma trace_mul_nonneg_of_posSemidef (M N : Matrix ι ι ℝ) (hM : M.PosSemidef) (hN : N.PosSemidef) :
    0 ≤ Matrix.trace (M * N) := by
  let R := CFC.sqrt M
  have hR : R.PosSemidef := (CFC.sqrt_nonneg M).posSemidef
  have h := hN.mul_mul_conjTranspose_same R
  rw [hR.isHermitian.eq] at h
  have ht := h.trace_nonneg
  rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self M hM.nonneg] at ht
  exact ht

end MatrixGram

lemma matrixCoordinateDerivative_hessian_isSymm {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (i : Fin n) (x : CoordinateSpace n) :
    (matrixCoordinateDerivative (coordinateHessian φ) i x).IsSymm := by
  ext a b
  change coordinateDerivative i (fun y => coordinateHessian φ y b a) x =
    coordinateDerivative i (fun y => coordinateHessian φ y a b) x
  have heq : (fun y => coordinateHessian φ y b a) = (fun y => coordinateHessian φ y a b) :=
    funext fun y => (coordinateHessian_isSymm hφ y).apply a b
  rw [heq]

/-- The two positive-semidefinite remainders claimed in Letwin Lemma 2.4.
The sign of the V term is derived from convexity on its actual open domain. -/
theorem mongeAmpere_hessian_remainders_posSemidef {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) {x : CoordinateSpace n} (hH : (coordinateHessian φ x).PosSemidef)
    {U : Set (CoordinateSpace n)} (hU : IsOpen U) (hVc : ConvexOn ℝ U V)
    (hV : ContDiffOn ℝ 2 V U) (hx : coordinateGradient φ x ∈ U) :
    (coordinateHessian φ x * coordinateHessian V (coordinateGradient φ x) * coordinateHessian φ x).PosSemidef ∧
      Matrix.PosSemidef (fun i j : Fin n => Matrix.trace (inverseHessian φ x * matrixCoordinateDerivative (coordinateHessian φ) j x *
        inverseHessian φ x * matrixCoordinateDerivative (coordinateHessian φ) i x)) := by
  constructor
  · have h := (coordinateHessian_posSemidef_of_convex hU hVc hV hx).mul_mul_conjTranspose_same
      (coordinateHessian φ x)
    rwa [hH.isHermitian.eq] at h
  · exact weighted_trace_gram_posSemidef (inverseHessian φ x) hH.inv
      (fun i => matrixCoordinateDerivative (coordinateHessian φ) i x)
      (fun i => matrixCoordinateDerivative_hessian_isSymm hφ i x)

end GaussianTilt.Letwin
