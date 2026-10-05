import GaussianTilt.MomentMapRegularityConstantDensityCalabi
import GaussianTilt.MomentMapCalabiAffine

/-! # Actual product differentiation of the Calabi cubic contraction -/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def calabiTensorSymm (T : Fin n → Fin n → Fin n → ℝ) : Prop :=
  (∀ i j k, T i j k = T j i k) ∧ (∀ i j k, T i j k = T i k j)

def calabiContraction (A B C : Matrix (Fin n) (Fin n) ℝ)
    (T U : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, ∑ r : Fin n × Fin n,
    A p.1 p.2 * B q.1 q.2 * C r.1 r.2 * T p.1 q.1 r.1 * U p.2 q.2 r.2

lemma calabiContraction_swap12 (A B C : Matrix (Fin n) (Fin n) ℝ)
    (T U : Fin n → Fin n → Fin n → ℝ) (hT : calabiTensorSymm T) (hU : calabiTensorSymm U) :
    calabiContraction A B C T U = calabiContraction B A C T U := by
  unfold calabiContraction
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  rw [hT.1 q.1 p.1 r.1, hU.1 q.2 p.2 r.2]
  ring

lemma calabiContraction_swap23 (A B C : Matrix (Fin n) (Fin n) ℝ)
    (T U : Fin n → Fin n → Fin n → ℝ) (hT : calabiTensorSymm T) (hU : calabiTensorSymm U) :
    calabiContraction A B C T U = calabiContraction A C B T U := by
  unfold calabiContraction
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  rw [hT.2 p.1 r.1 q.1, hU.2 p.2 r.2 q.2]
  ring

lemma calabiContraction_swap_tensors (A B C : Matrix (Fin n) (Fin n) ℝ)
    (T U : Fin n → Fin n → Fin n → ℝ) (hA : A.IsSymm) (hB : B.IsSymm) (hC : C.IsSymm) :
    calabiContraction A B C T U = calabiContraction A B C U T := by
  unfold calabiContraction
  apply Fintype.sum_equiv (Equiv.prodComm _ _)
  intro p
  apply Fintype.sum_equiv (Equiv.prodComm _ _)
  intro q
  apply Fintype.sum_equiv (Equiv.prodComm _ _)
  intro r
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [hA.apply p.1 p.2, hB.apply q.1 q.2, hC.apply r.1 r.2]
  ring

lemma coordinateDerivative_prod_five {f g h j k : CoordinateSpace n → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (hh : Differentiable ℝ h)
    (hj : Differentiable ℝ j) (hk : Differentiable ℝ k) (l : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative l (fun y => f y * g y * h y * j y * k y) x =
      coordinateDerivative l f x * g x * h x * j x * k x +
      f x * coordinateDerivative l g x * h x * j x * k x +
      f x * g x * coordinateDerivative l h x * j x * k x +
      f x * g x * h x * coordinateDerivative l j x * k x +
      f x * g x * h x * j x * coordinateDerivative l k x := by
  rw [coordinateDerivative_mul (((hf.fun_mul hg).fun_mul hh).fun_mul hj) hk,
    coordinateDerivative_mul ((hf.fun_mul hg).fun_mul hh) hj,
    coordinateDerivative_mul (hf.fun_mul hg) hh, coordinateDerivative_mul hf hg]
  ring

/-- Leibniz's rule for the actual five-linear cubic contraction. -/
theorem coordinateDerivative_calabiContraction
    {A B C : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {T U : CoordinateSpace n → Fin n → Fin n → Fin n → ℝ}
    (hA : ∀ a b, Differentiable ℝ (fun y => A y a b))
    (hB : ∀ a b, Differentiable ℝ (fun y => B y a b))
    (hC : ∀ a b, Differentiable ℝ (fun y => C y a b))
    (hT : ∀ a b c, Differentiable ℝ (fun y => T y a b c))
    (hU : ∀ a b c, Differentiable ℝ (fun y => U y a b c))
    (l : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative l (fun y => calabiContraction (A y) (B y) (C y) (T y) (U y)) x =
      calabiContraction (matrixCoordinateDerivative A l x) (B x) (C x) (T x) (U x) +
      calabiContraction (A x) (matrixCoordinateDerivative B l x) (C x) (T x) (U x) +
      calabiContraction (A x) (B x) (matrixCoordinateDerivative C l x) (T x) (U x) +
      calabiContraction (A x) (B x) (C x) (fun a b c => coordinateDerivative l (fun y => T y a b c) x) (U x) +
      calabiContraction (A x) (B x) (C x) (T x) (fun a b c => coordinateDerivative l (fun y => U y a b c) x) := by
  let F := fun (p q r : Fin n × Fin n) (y : CoordinateSpace n) =>
    A y p.1 p.2 * B y q.1 q.2 * C y r.1 r.2 * T y p.1 q.1 r.1 * U y p.2 q.2 r.2
  have hF (p q r : Fin n × Fin n) : Differentiable ℝ (F p q r) :=
    ((((hA _ _).mul (hB _ _)).mul (hC _ _)).mul (hT _ _ _)).mul (hU _ _ _)
  change coordinateDerivative l (fun y => ∑ p, ∑ q, ∑ r, F p q r y) x = _
  rw [coordinateDerivative_sum _ (fun p => Differentiable.fun_sum (fun q _ =>
    Differentiable.fun_sum (fun r _ => hF p q r)))]
  simp_rw [coordinateDerivative_sum _ (fun q => Differentiable.fun_sum (fun r _ => hF _ q r)),
    coordinateDerivative_sum _ (hF _ _)]
  dsimp [F]
  simp_rw [coordinateDerivative_prod_five (hA _ _) (hB _ _) (hC _ _) (hT _ _ _) (hU _ _ _)]
  simp only [Finset.sum_add_distrib]
  rfl

lemma differentiable_calabiContraction
    {A B C : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {T U : CoordinateSpace n → Fin n → Fin n → Fin n → ℝ}
    (hA : ∀ a b, Differentiable ℝ (fun y => A y a b))
    (hB : ∀ a b, Differentiable ℝ (fun y => B y a b))
    (hC : ∀ a b, Differentiable ℝ (fun y => C y a b))
    (hT : ∀ a b c, Differentiable ℝ (fun y => T y a b c))
    (hU : ∀ a b c, Differentiable ℝ (fun y => U y a b c)) :
    Differentiable ℝ (fun y => calabiContraction (A y) (B y) (C y) (T y) (U y)) := by
  unfold calabiContraction
  apply Differentiable.fun_sum; intro p _
  apply Differentiable.fun_sum; intro q _
  apply Differentiable.fun_sum; intro r _
  exact ((((hA _ _).mul (hB _ _)).mul (hC _ _)).mul (hT _ _ _)).mul (hU _ _ _)

lemma calabiTensorSymm_coordinateDerivative
    {T : CoordinateSpace n → Fin n → Fin n → Fin n → ℝ}
    (hT : ∀ y, calabiTensorSymm (T y)) (l : Fin n) (x : CoordinateSpace n) :
    calabiTensorSymm (fun a b c => coordinateDerivative l (fun y => T y a b c) x) := by
  constructor
  · intro a b c
    exact congrArg (fun f => coordinateDerivative l f x) (funext (fun y => (hT y).1 a b c))
  · intro a b c
    exact congrArg (fun f => coordinateDerivative l f x) (funext (fun y => (hT y).2 a b c))

lemma calabiTensorSymm_actual {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) (x : CoordinateSpace n) :
    calabiTensorSymm (coordinateThirdDerivative u x) :=
  ⟨coordinateThirdDerivative_symm (contDiff_infty.mp hu 2) x,
    coordinateThirdDerivative_swap_last (contDiff_infty.mp hu 3) x⟩

lemma matrixDerivative_symm {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ y, (A y).IsSymm) (l : Fin n) (x : CoordinateSpace n) :
    (matrixCoordinateDerivative A l x).IsSymm := by
  ext a b
  change coordinateDerivative l (fun y => A y b a) x = coordinateDerivative l (fun y => A y a b) x
  congr 1
  exact funext (fun y => (hA y).apply a b)

lemma calabiContraction_diagonal_eq (A : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Fin n → Fin n → ℝ) :
    calabiContraction A A A T T = cubicMetricEnergy A T := by
  unfold calabiContraction cubicMetricEnergy
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  calc
    (∑ i, ∑ j, ∑ c, ∑ k, A a i * A b j * A c k * T a b c * T i j k) =
        ∑ i, ∑ c, ∑ j, ∑ k, A a i * A b j * A c k * T a b c * T i j k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- The first derivative of a symmetric cubic metric contraction groups
into three metric derivatives and two cubic tensor derivatives. -/
theorem coordinateDerivative_calabiContraction_diagonal
    {K : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {T : CoordinateSpace n → Fin n → Fin n → Fin n → ℝ}
    (hK : ∀ a b, Differentiable ℝ (fun y => K y a b))
    (hT : ∀ a b c, Differentiable ℝ (fun y => T y a b c))
    (hKs : ∀ y, (K y).IsSymm) (hTs : ∀ y, calabiTensorSymm (T y))
    (l : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative l (fun y => calabiContraction (K y) (K y) (K y) (T y) (T y)) x =
      3 * calabiContraction (matrixCoordinateDerivative K l x) (K x) (K x) (T x) (T x) +
      2 * calabiContraction (K x) (K x) (K x)
        (fun a b c => coordinateDerivative l (fun y => T y a b c) x) (T x) := by
  rw [coordinateDerivative_calabiContraction hK hK hK hT hT]
  rw [calabiContraction_swap12 (K x) (matrixCoordinateDerivative K l x) (K x) (T x) (T x) (hTs x) (hTs x),
    calabiContraction_swap23 (K x) (K x) (matrixCoordinateDerivative K l x) (T x) (T x) (hTs x) (hTs x),
    calabiContraction_swap12 (K x) (matrixCoordinateDerivative K l x) (K x) (T x) (T x) (hTs x) (hTs x),
    calabiContraction_swap_tensors (K x) (K x) (K x) (T x) _ (hKs x) (hKs x) (hKs x)]
  ring

/-- The actual second derivative of the symmetric cubic metric energy.
This is a five-factor product rule with all permutation multiplicities proved. -/
theorem second_coordinateDerivative_calabiContraction_diagonal
    {K : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {T : CoordinateSpace n → Fin n → Fin n → Fin n → ℝ}
    (hK : ∀ a b, ContDiff ℝ ∞ (fun y => K y a b))
    (hT : ∀ a b c, ContDiff ℝ ∞ (fun y => T y a b c))
    (hKs : ∀ y, (K y).IsSymm) (hTs : ∀ y, calabiTensorSymm (T y))
    (l : Fin n) (x : CoordinateSpace n) :
    let K₁ := fun y => matrixCoordinateDerivative K l y
    let T₁ := fun y a b c => coordinateDerivative l (fun z => T z a b c) y
    coordinateDerivative l (coordinateDerivative l
      (fun y => calabiContraction (K y) (K y) (K y) (T y) (T y))) x =
      3 * calabiContraction (matrixCoordinateDerivative K₁ l x) (K x) (K x) (T x) (T x) +
      6 * calabiContraction (K₁ x) (K₁ x) (K x) (T x) (T x) +
      12 * calabiContraction (K₁ x) (K x) (K x) (T₁ x) (T x) +
      2 * calabiContraction (K x) (K x) (K x)
        (fun a b c => coordinateDerivative l (fun y => T₁ y a b c) x) (T x) +
      2 * calabiContraction (K x) (K x) (K x) (T₁ x) (T₁ x) := by
  let K₁ := fun y => matrixCoordinateDerivative K l y
  let T₁ := fun y a b c => coordinateDerivative l (fun z => T z a b c) y
  have hKd a b := (hK a b).differentiable (by simp)
  have hTd a b c := (hT a b c).differentiable (by simp)
  have hK₁ a b : Differentiable ℝ (fun y => K₁ y a b) :=
    (smooth_coordinateDerivative (hK a b) l).differentiable (by simp)
  have hT₁ a b c : Differentiable ℝ (fun y => T₁ y a b c) :=
    (smooth_coordinateDerivative (hT a b c) l).differentiable (by simp)
  have hK₁s : (K₁ x).IsSymm := matrixDerivative_symm hKs l x
  have hT₁s : calabiTensorSymm (T₁ x) := calabiTensorSymm_coordinateDerivative hTs l x
  have he : coordinateDerivative l
      (fun y => calabiContraction (K y) (K y) (K y) (T y) (T y)) =
      (fun y => 3 * calabiContraction (K₁ y) (K y) (K y) (T y) (T y) +
        2 * calabiContraction (K y) (K y) (K y) (T₁ y) (T y)) := by
    funext y
    exact coordinateDerivative_calabiContraction_diagonal hKd hTd hKs hTs l y
  rw [he]
  have hF := differentiable_calabiContraction hK₁ hKd hKd hTd hTd
  have hG := differentiable_calabiContraction hKd hKd hKd hT₁ hTd
  rw [coordinateDerivative_add (hF.const_mul 3) (hG.const_mul 2),
    coordinateDerivative_const_mul hF, coordinateDerivative_const_mul hG,
    coordinateDerivative_calabiContraction hK₁ hKd hKd hTd hTd,
    coordinateDerivative_calabiContraction hKd hKd hKd hT₁ hTd]
  change 3 * (_ + _ + calabiContraction (K₁ x) (K x) (K₁ x) (T x) (T x) +
      _ + calabiContraction (K₁ x) (K x) (K x) (T x) (T₁ x)) +
    2 * (_ + calabiContraction (K x) (K₁ x) (K x) (T₁ x) (T x) +
      calabiContraction (K x) (K x) (K₁ x) (T₁ x) (T x) + _ + _) = _
  rw [calabiContraction_swap23 (K₁ x) (K x) (K₁ x) (T x) (T x) (hTs x) (hTs x),
    calabiContraction_swap_tensors (K₁ x) (K x) (K x) (T x) (T₁ x) hK₁s (hKs x) (hKs x),
    calabiContraction_swap12 (K x) (K₁ x) (K x) (T₁ x) (T x) hT₁s (hTs x),
    calabiContraction_swap23 (K x) (K x) (K₁ x) (T₁ x) (T x) hT₁s (hTs x),
    calabiContraction_swap12 (K x) (K₁ x) (K x) (T₁ x) (T x) hT₁s (hTs x)]
  ring

lemma hessian_adjugate_symm {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) (x : CoordinateSpace n) :
    (coordinateHessian u x).adjugate.IsSymm := by
  change (coordinateHessian u x).adjugateᵀ = (coordinateHessian u x).adjugate
  rw [Matrix.adjugate_transpose, (coordinateHessian_isSymm (contDiff_infty.mp hu 2) x).eq]

/-- The actual second coordinate derivative of the smooth adjugate Calabi
energy, before imposing the determinant equation or normalizing the Hessian. -/
theorem coordinateHessian_calabiAdjugateEnergy_diagonal {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (l : Fin n) (x : CoordinateSpace n) :
    let K := fun y => (coordinateHessian u y).adjugate
    let K₁ := fun y => matrixCoordinateDerivative K l y
    let T := coordinateThirdDerivative u x
    let T₁ := fun a b c => coordinateFourthDerivative u x a b c l
    coordinateHessian (calabiAdjugateEnergy u) x l l =
      3 * calabiContraction (matrixCoordinateDerivative K₁ l x) (K x) (K x) T T +
      6 * calabiContraction (K₁ x) (K₁ x) (K x) T T +
      12 * calabiContraction (K₁ x) (K x) (K x) T₁ T +
      2 * calabiContraction (K x) (K x) (K x)
        (fun a b c => coordinateFifthDerivative u x a b c l l) T +
      2 * calabiContraction (K x) (K x) (K x) T₁ T₁ := by
  have he : calabiAdjugateEnergy u = fun y => calabiContraction
      (coordinateHessian u y).adjugate (coordinateHessian u y).adjugate
      (coordinateHessian u y).adjugate (coordinateThirdDerivative u y) (coordinateThirdDerivative u y) := by
    funext y
    exact (calabiContraction_diagonal_eq _ _).symm
  rw [he]
  exact second_coordinateDerivative_calabiContraction_diagonal
    (smooth_hessian_adjugate hu) (smooth_coordinateThirdDerivative hu)
    (hessian_adjugate_symm hu) (calabiTensorSymm_actual hu) l x

/-- The actual normalized Laplacian expansion, retaining the fifth derivative
until the third differentiated determinant identity is substituted. -/
theorem linearized_calabiAdjugateEnergy_at_identity {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) {x : CoordinateSpace n}
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = 1)
    (hI : coordinateHessian u x = 1) :
    let T := coordinateThirdDerivative u x
    let Tl : Fin n → Matrix (Fin n) (Fin n) ℝ := fun l a b => coordinateThirdDerivative u x a b l
    let Ql := fun l a b c => coordinateFourthDerivative u x a b c l
    let Qll : Fin n → Matrix (Fin n) (Fin n) ℝ := fun l a b => coordinateFourthDerivative u x a b l l
    linearizedMA (1 : Matrix (Fin n) (Fin n) ℝ) (calabiAdjugateEnergy u) x =
      ∑ l, (3 * calabiContraction ((2 : ℝ) • (Tl l * Tl l) - Qll l) 1 1 T T +
        6 * calabiContraction (-Tl l) (-Tl l) 1 T T +
        12 * calabiContraction (-Tl l) 1 1 (Ql l) T +
        2 * calabiContraction 1 1 1 (fun a b c => coordinateFifthDerivative u x a b c l l) T +
        2 * calabiContraction 1 1 1 (Ql l) (Ql l)) := by
  unfold linearizedMA
  rw [Matrix.one_mul]
  change (∑ l, coordinateHessian (calabiAdjugateEnergy u) x l l) = _
  apply Finset.sum_congr rfl
  intro l _
  rw [coordinateHessian_calabiAdjugateEnergy_diagonal hu]
  dsimp only
  rw [constant_density_adjugate_second_at_identity hu hMA hI,
    constant_density_adjugate_first hu hMA]
  rw [hI]
  simp only [Matrix.adjugate_one, Matrix.one_mul, Matrix.mul_one]
  rfl

end GaussianTilt.MomentMapRegularity
