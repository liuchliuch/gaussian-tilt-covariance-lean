import GaussianTilt.MomentMapHolderAlgebra
import GaussianTilt.MomentMapHolderLinear
import GaussianTilt.LetwinMatrixCalculus

/-! # The actual smooth determinant operator on Hölder matrix fields -/
noncomputable section
open Set Matrix
open scoped Topology BoundedContinuousFunction ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.HolderSpace
variable (X : Type*) [MetricSpace X]

/-- Constants are genuine Hölder graph elements, including the multiplicative unit. -/
def constant (α c : ℝ) : Space X ℝ α :=
  ofBounded X ℝ α (BoundedContinuousFunction.const X c) 0 (by intro x y; simp)

@[simp] lemma value_constant (α c : ℝ) (x : X) : value X ℝ α (constant X α c) x = c := rfl

def listProduct {ι : Type*} (α : ℝ) : List ι → (ι → Space X ℝ α) → Space X ℝ α
  | [], _ => constant X α 1
  | i :: l, f => product X α (f i) (listProduct α l f)

lemma value_listProduct {ι : Type*} (α : ℝ) (l : List ι) (f : ι → Space X ℝ α) (x : X) :
    value X ℝ α (listProduct X α l f) x = (l.map (fun i => value X ℝ α (f i) x)).prod := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [listProduct, value_product, BoundedContinuousFunction.mul_apply, ih, List.map_cons, List.prod_cons]

lemma contDiff_listProduct {ι Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (α : ℝ) (l : List ι) (f : ι → Z → Space X ℝ α)
    (hf : ∀ i ∈ l, ContDiff ℝ ∞ (f i)) :
    ContDiff ℝ ∞ (fun z => listProduct X α l (fun i => f i z)) := by
  induction l with
  | nil => exact contDiff_const
  | cons i l ih =>
      have h₁ := hf i (by simp)
      have h₂ := ih (fun j hj => hf j (by simp [hj]))
      exact (productCLM X α).isBoundedBilinearMap.contDiff.comp (h₁.prodMk h₂)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Literal pointwise determinant, constructed using bounded multiplication
on the true Hölder space. -/
def determinant (α : ℝ) (A : ι → ι → Space X ℝ α) : Space X ℝ α :=
  ∑ σ : Equiv.Perm ι, ((σ.sign : ℤ) : ℝ) •
    listProduct X α Finset.univ.toList (fun i => A (σ i) i)

lemma value_determinant (α : ℝ) (A : ι → ι → Space X ℝ α) (x : X) :
    value X ℝ α (determinant X α A) x = (show Matrix ι ι ℝ from fun i j => value X ℝ α (A i j) x).det := by
  simp only [determinant, map_sum, map_smul, BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.smul_apply, value_listProduct, smul_eq_mul, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  simpa only [Finset.toList_toFinset] using
    (List.prod_toFinset (fun i => value X ℝ α (A (σ i) i) x) (Finset.nodup_toList Finset.univ)).symm

/-- The nonlinear determinant map is genuinely C∞ between the constructed
Banach spaces, not merely pointwise differentiable. -/
theorem contDiff_determinant (α : ℝ) :
    ContDiff ℝ ∞ (determinant X α : (ι → ι → Space X ℝ α) → Space X ℝ α) := by
  unfold determinant
  apply ContDiff.sum
  intro σ _
  apply ContDiff.const_smul
  apply contDiff_listProduct X α Finset.univ.toList (fun (i : ι) (A : ι → ι → Space X ℝ α) => A (σ i) i)
  intro i _
  fun_prop

/-- The Banach-space derivative is the actual pointwise Jacobi linearization.
This identifies it with the classical elliptic operator used in continuation. -/
theorem determinant_fderiv_apply_value (α : ℝ)
    (A B : ι → ι → Space X ℝ α) (x : X) :
    value X ℝ α (fderiv ℝ (determinant X α) A B) x =
      Matrix.trace ((show Matrix ι ι ℝ from fun i j => value X ℝ α (A i j) x).adjugate *
        (show Matrix ι ι ℝ from fun i j => value X ℝ α (B i j) x)) := by
  let A₀ : Matrix ι ι ℝ := fun i j => value X ℝ α (A i j) x
  let B₀ : Matrix ι ι ℝ := fun i j => value X ℝ α (B i j) x
  have hline : HasDerivAt (fun t : ℝ => A + t • B) B 0 := by
    simpa only [Pi.add_apply, zero_add, one_smul] using (hasDerivAt_const (0 : ℝ) A).add ((hasDerivAt_id (0 : ℝ)).smul_const B)
  have hd : HasFDerivAt (determinant X α) (fderiv ℝ (determinant X α) A) (A + (0 : ℝ) • B) := by
    simpa using ((contDiff_infty.mp (contDiff_determinant X α) 1).differentiable le_rfl A).hasFDerivAt
  have heval := (eval X ℝ α x).hasFDerivAt.comp_hasDerivAt 0 (hd.comp_hasDerivAt 0 hline)
  change HasDerivAt (fun t : ℝ => value X ℝ α (determinant X α (A + t • B)) x)
    (value X ℝ α (fderiv ℝ (determinant X α) A B) x) 0 at heval
  have heq : (fun t : ℝ => value X ℝ α (determinant X α (A + t • B)) x) =
      (fun t : ℝ => (A₀ + t • B₀).det) := by
    funext t
    rw [value_determinant]
    congr 1
  rw [heq] at heval
  have hmatrix : HasDerivAt (fun t : ℝ => A₀ + t • B₀) B₀ 0 := by
    simpa only [Pi.add_apply, zero_add, one_smul] using (hasDerivAt_const (0 : ℝ) A₀).add ((hasDerivAt_id (0 : ℝ)).smul_const B₀)
  have hdet : HasFDerivAt Matrix.det (fderiv ℝ Matrix.det A₀) (A₀ + (0 : ℝ) • B₀) := by
    have hs : ContDiff ℝ 1 (Matrix.det : Matrix ι ι ℝ → ℝ) := (GaussianTilt.Letwin.determinantMultilinear (ι := ι)).contDiff
    simpa using (hs.differentiable le_rfl A₀).hasFDerivAt
  have hr := hdet.comp_hasDerivAt 0 hmatrix
  rw [GaussianTilt.Letwin.fderiv_determinant_apply] at hr
  exact heval.unique hr

end GaussianTilt.HolderSpace
