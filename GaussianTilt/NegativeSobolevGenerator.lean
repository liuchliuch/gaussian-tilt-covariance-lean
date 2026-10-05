import GaussianTilt.NegativeSobolevClosable
import GaussianTilt.NegativeSobolevPairing

/-! # The actual weighted generator as an L² core operator -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

lemma weightedLaplacian_add {n : ℕ} (φ : CoordinateSpace n → ℝ)
    {f g : CoordinateSpace n → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    weightedLaplacian φ (f + g) = weightedLaplacian φ f + weightedLaplacian φ g := by
  have hd (i : Fin n) : coordinateDerivative i (f+g) = coordinateDerivative i f + coordinateDerivative i g :=
    funext (coordinateDerivative_add (hf.differentiable (by simp)) (hg.differentiable (by simp)) i)
  funext x
  simp only [weightedLaplacian_apply, hd, Pi.add_apply]
  have hdd (i : Fin n) : coordinateDerivative i (coordinateDerivative i f + coordinateDerivative i g) x =
      coordinateDerivative i (coordinateDerivative i f) x + coordinateDerivative i (coordinateDerivative i g) x :=
    coordinateDerivative_add ((smooth_coordinateDerivative hf i).differentiable (by simp))
      ((smooth_coordinateDerivative hg i).differentiable (by simp)) i x
  simp_rw [hdd]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma weightedLaplacian_smul {n : ℕ} (φ : CoordinateSpace n → ℝ)
    {f : CoordinateSpace n → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    weightedLaplacian φ (c • f) = c • weightedLaplacian φ f := by
  have hd {g : CoordinateSpace n → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin n) :
      coordinateDerivative i (c • g) = c • coordinateDerivative i g := by
    funext x
    unfold coordinateDerivative
    rw [((hg.differentiable (by simp) x).hasFDerivAt.const_smul c).fderiv]
    simp
  funext x
  simp only [weightedLaplacian_apply, hd hf, hd (smooth_coordinateDerivative hf _), Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual smooth weighted Laplacian preserves the compact smooth core. -/
def smoothCompactWeightedLaplacian {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : smoothCompactCore n →ₗ[ℝ] smoothCompactCore n where
  toFun f := ⟨weightedLaplacian φ f.1, smooth_weightedLaplacian hφ f.2.1,
    weightedLaplacian_hasCompactSupport φ f.2.2⟩
  map_add' f g := Subtype.ext (weightedLaplacian_add φ f.2.1 g.2.1)
  map_smul' c f := Subtype.ext (weightedLaplacian_smul φ f.2.1 c)

/-- The actual core generator with codomain the actual weighted L² space. -/
def weightedLaplacianToL2 {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ) :
    smoothCompactCore n →ₗ[ℝ] Lp ℝ 2 (potentialMeasure φ) :=
  (smoothCompactToL2 (potentialMeasure φ)).comp (smoothCompactWeightedLaplacian hφ)

/-- The actual L² constant one. -/
def l2One {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasure μ] : Lp ℝ 2 μ :=
  (memLp_const (1 : ℝ)).toLp (fun _ => 1)

lemma l2One_ae {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasure μ] :
    l2One μ =ᵐ[μ] fun _ => 1 := (memLp_const (1 : ℝ)).coeFn_toLp

/-- The mean-zero L² Hilbert subspace, defined as the orthogonal complement
of the actual constant function. -/
def meanZeroL2 {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasure μ] :
    Submodule ℝ (Lp ℝ 2 μ) := (ℝ ∙ l2One μ)ᗮ

lemma mem_meanZeroL2_iff {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasure μ]
    (f : Lp ℝ 2 μ) : f ∈ meanZeroL2 μ ↔ (∫ x, f x ∂μ) = 0 := by
  rw [meanZeroL2, Submodule.mem_orthogonal_singleton_iff_inner_right, L2.inner_def]
  have heq : (∫ x, inner ℝ (l2One μ x) (f x) ∂μ) = ∫ x, f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [l2One_ae μ] with x hx
    simp [hx, RCLike.inner_apply]
  rw [heq]

/-- Compactly supported generator images have zero mean, proved by Green's
formula with the constant test. -/
theorem integral_weightedLaplacian_zero {n : ℕ} {φ u : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    (∫ x, weightedLaplacian φ u x ∂potentialMeasure φ) = 0 := by
  have h := integral_divergenceDiffusion_mul_compact_left (A := fun _ => 1)
    (g := fun _ => (1 : ℝ)) (contDiff_infty.mp hφ 1) (fun _ _ => contDiff_const)
    (contDiff_infty.mp hu 2) contDiff_const huc
  simpa [weightedLaplacian, diffusionGamma_one, coordinateDerivative] using h

/-- The actual weighted generator range is contained in mean-zero L². -/
theorem weightedLaplacianToL2_range_le {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ) :
    LinearMap.range (weightedLaplacianToL2 hφ) ≤ meanZeroL2 (potentialMeasure φ) := by
  rintro _ ⟨u, rfl⟩
  rw [mem_meanZeroL2_iff]
  have hae := smoothCompactToL2_ae (potentialMeasure φ) (smoothCompactWeightedLaplacian hφ u)
  change (∫ x, smoothCompactToL2 (potentialMeasure φ) (smoothCompactWeightedLaplacian hφ u) x ∂potentialMeasure φ) = 0
  rw [integral_congr_ae hae]
  exact integral_weightedLaplacian_zero hφ u.2.1 u.2.2

/-- The range closure still consists of mean-zero functions. -/
theorem weightedLaplacianToL2_closure_le {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ) :
    (LinearMap.range (weightedLaplacianToL2 hφ)).topologicalClosure ≤
      meanZeroL2 (potentialMeasure φ) :=
  (LinearMap.range (weightedLaplacianToL2 hφ)).topologicalClosure_minimal (weightedLaplacianToL2_range_le hφ)
    (Submodule.isClosed_orthogonal _)

end GaussianTilt.Letwin
