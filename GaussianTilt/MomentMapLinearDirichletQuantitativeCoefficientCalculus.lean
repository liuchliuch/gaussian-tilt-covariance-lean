import GaussianTilt.MomentMapLinearDirichletQuantitativeCoefficientAlgebra

/-! # Local coefficient chain rules and height-weighted bounds -/
noncomputable section
set_option maxHeartbeats 2000000
open Matrix Set Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateDerivative_sum_at {ι : Type*} [Fintype ι]
    (f : ι → CoordinateSpace n → ℝ) {x : CoordinateSpace n}
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) (k : Fin n) :
    coordinateDerivative k (fun y => ∑ i, f i y) x = ∑ i, coordinateDerivative k (f i) x := by
  unfold coordinateDerivative
  rw [fderiv_fun_sum (fun i _ => hf i)]
  simp

lemma matrixCoordinateDerivative_mul_at
    {H K : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {x : CoordinateSpace n}
    (hH : ∀ a b, DifferentiableAt ℝ (fun y => H y a b) x)
    (hK : ∀ a b, DifferentiableAt ℝ (fun y => K y a b) x) (k : Fin n) :
    matrixCoordinateDerivative (fun y => H y*K y) k x =
      matrixCoordinateDerivative H k x*K x+H x*matrixCoordinateDerivative K k x := by
  ext a b
  simp only [matrixCoordinateDerivative,Matrix.mul_apply,Matrix.add_apply]
  rw [coordinateDerivative_sum_at (fun j y => H y a j*K y j b)
    (fun j => (hH a j).mul (hK j b))]
  simp only [coordinateDerivative_mul_at (hH _ _) (hK _ _),Finset.sum_add_distrib]

lemma differentiableAt_matrix_mul_entries
    {H K : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {x : CoordinateSpace n}
    (hH : ∀ a b, DifferentiableAt ℝ (fun y => H y a b) x)
    (hK : ∀ a b, DifferentiableAt ℝ (fun y => K y a b) x) :
    ∀ a b, DifferentiableAt ℝ (fun y => (H y*K y) a b) x := by
  intro a b
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum (fun j _ => (hH a j).mul (hK j b))

lemma coordinateDerivative_comp_at {f : CoordinateSpace n → ℝ}
    {X : CoordinateSpace n → CoordinateSpace n} {y : CoordinateSpace n}
    (hf : DifferentiableAt ℝ f (X y)) (hX : DifferentiableAt ℝ X y) (k : Fin n) :
    coordinateDerivative k (fun z => f (X z)) y =
      fderiv ℝ f (X y) (fderiv ℝ X y (Pi.single k 1)) := by
  unfold coordinateDerivative
  change (fderiv ℝ (f ∘ X) y) (Pi.single k 1) = _
  rw [fderiv_comp y hf hX]
  rfl

lemma weighted_coordinateDerivative_comp_bound {f : CoordinateSpace n → ℝ}
    {X : CoordinateSpace n → CoordinateSpace n} {y : CoordinateSpace n}
    (hf : DifferentiableAt ℝ f (X y)) (hX : DifferentiableAt ℝ X y)
    {r K C : ℝ} (hr : 0 ≤ r) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hdf : ∀ l, r*|coordinateDerivative l f (X y)| ≤ K)
    (hdX : ‖fderiv ℝ X y‖ ≤ C) (k : Fin n) :
    r*|coordinateDerivative k (fun z => f (X z)) y| ≤ (n:ℝ)*K*C := by
  let v := fderiv ℝ X y (Pi.single k 1)
  have hv : ‖v‖ ≤ C := by
    calc
      _ ≤ ‖fderiv ℝ X y‖*‖(Pi.single k 1 : CoordinateSpace n)‖ := (fderiv ℝ X y).le_opNorm _
      _ = ‖fderiv ℝ X y‖ := by rw [Pi.norm_single,norm_one,mul_one]
      _ ≤ C := hdX
  rw [coordinateDerivative_comp_at hf hX,fderiv_apply_eq_sum_coordinates]
  calc
    _ ≤ r*(∑ l, |v l*coordinateDerivative l f (X y)|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hr
    _ = ∑ l, |v l| *(r*|coordinateDerivative l f (X y)|) := by
      simp only [Finset.mul_sum,abs_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ ≤ ∑ _l : Fin n, C*K := by
      apply Finset.sum_le_sum
      intro l _
      have hvl : |v l| ≤ C := (norm_le_pi_norm v l).trans hv
      exact mul_le_mul hvl (hdf l) (by positivity) hC
    _ = _ := by simp; ring

lemma matrixCoordinateDerivative_congruence_at
    {J A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {y : CoordinateSpace n}
    (hJ : ∀ a b, DifferentiableAt ℝ (fun z => J z a b) y)
    (hA : ∀ a b, DifferentiableAt ℝ (fun z => A z a b) y) (k : Fin n) :
    matrixCoordinateDerivative (fun z => J z*A z*(J z)ᵀ) k y =
      matrixCoordinateDerivative J k y*A y*(J y)ᵀ+
      J y*matrixCoordinateDerivative A k y*(J y)ᵀ+
      J y*A y*(matrixCoordinateDerivative J k y)ᵀ := by
  rw [matrixCoordinateDerivative_mul_at (H := fun z => J z*A z) (K := fun z => (J z)ᵀ)
      (differentiableAt_matrix_mul_entries hJ hA) (fun a b => hJ b a),
    matrixCoordinateDerivative_mul_at hJ hA,Matrix.add_mul]
  rfl

/-- The actual local Leibniz rule, with the boundary height carried through
all three differentiated factors. -/
theorem weighted_matrix_congruence_derivative_bound
    {J A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {y : CoordinateSpace n}
    (hJ : ∀ a b, DifferentiableAt ℝ (fun z => J z a b) y)
    (hA : ∀ a b, DifferentiableAt ℝ (fun z => A z a b) y)
    {t C Λ K : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hC : 0 ≤ C) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K)
    (hJb : ∀ a b, |J y a b| ≤ C)
    (hDJ : ∀ k a b, |matrixCoordinateDerivative J k y a b| ≤ C)
    (hAb : ∀ a b, |A y a b| ≤ Λ)
    (hDA : ∀ k a b, t*|matrixCoordinateDerivative A k y a b| ≤ K) (k i j : Fin n) :
    t*|matrixCoordinateDerivative (fun z => J z*A z*(J z)ᵀ) k y i j| ≤
      (n:ℝ)^2*C^2*(2*Λ+K) := by
  rw [matrixCoordinateDerivative_congruence_at hJ hA]
  have h1 := matrix_triple_entry_bound (matrixCoordinateDerivative J k y) (A y) (J y)ᵀ
    hC hΛ hC (hDJ k) hAb (fun a b => hJb b a) i j
  have h3 := matrix_triple_entry_bound (J y) (A y) (matrixCoordinateDerivative J k y)ᵀ
    hC hΛ hC hJb hAb (fun a b => hDJ k b a) i j
  have h2 := matrix_triple_entry_bound (J y) (t • matrixCoordinateDerivative A k y) (J y)ᵀ
    hC hK hC hJb (fun a b => by simpa only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg ht] using hDA k a b)
    (fun a b => hJb b a) i j
  simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg ht] at h2
  have h1t := mul_le_mul_of_nonneg_left h1 ht
  have h3t := mul_le_mul_of_nonneg_left h3 ht
  have htC : t*((n:ℝ)^2*C*Λ*C) ≤ (n:ℝ)^2*C*Λ*C := mul_le_of_le_one_left (by positivity) ht1
  have htri := abs_add_le ((matrixCoordinateDerivative J k y*A y*(J y)ᵀ) i j+
    (J y*matrixCoordinateDerivative A k y*(J y)ᵀ) i j) ((J y*A y*(matrixCoordinateDerivative J k y)ᵀ) i j)
  have htri2 := abs_add_le ((matrixCoordinateDerivative J k y*A y*(J y)ᵀ) i j)
    ((J y*matrixCoordinateDerivative A k y*(J y)ᵀ) i j)
  simp only [Matrix.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left htri ht,mul_le_mul_of_nonneg_left htri2 ht]

end GaussianTilt.MomentMapLinearDirichlet
