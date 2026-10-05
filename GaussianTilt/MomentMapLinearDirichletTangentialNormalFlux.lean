import GaussianTilt.MomentMapLinearDirichletTangentialNormalWeakProduct

/-! # Genuine normal flux recovery from the literal weak divergence equation

All non-normal weak derivatives are supplied by actual tangential H¹
regularity. The divergence equation determines the remaining weak flux
derivative, so the continuous weak-gradient theorem makes the normal
flux C¹. Division by the positive normal coefficient is then legitimate.
-/
noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- The non-normal differentiated divergence terms. -/
def nonNormalDivergence (q : Fin n)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (G : CoordinateSpace n → CoordinateSpace n)
    (H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (x : CoordinateSpace n) : ℝ :=
  ∑ p ∈ Finset.univ.erase (q,q),
    (coordinateDerivative p.1 (fun y=>A y p.1 p.2) x*G x p.2+A x p.1 p.2*H x p.2 p.1)

def normalFluxGradient (q : Fin n)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (G : CoordinateSpace n → CoordinateSpace n)
    (H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (f : CoordinateSpace n→ℝ)
    (x : CoordinateSpace n) (i : Fin n) : ℝ :=
  if i=q then -f x-nonNormalDivergence q A G H x
  else coordinateDerivative i (fun y=>A y q q) x*G x q+A x q q*H x q i

lemma continuousOn_nonNormalDivergence {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (q : Fin n) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {G : CoordinateSpace n → CoordinateSpace n} {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i k, ContDiffOn ℝ ∞ (fun x=>A x i k) U)
    (hG : ∀ k, ContinuousOn (fun x=>G x k) U)
    (hH : ∀ k i, ContinuousOn (fun x=>H x k i) U) :
    ContinuousOn (nonNormalDivergence q A G H) U := by
  apply continuousOn_finset_sum
  intro p _
  exact ((continuousOn_coordinateDerivative_local hU (hA p.1 p.2) p.1).mul (hG p.2)).add
    ((hA p.1 p.2).continuousOn.mul (hH p.2 p.1))

lemma continuousOn_normalFluxGradient {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (q : Fin n) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {G : CoordinateSpace n → CoordinateSpace n} {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {f : CoordinateSpace n→ℝ}
    (hA : ∀ i k, ContDiffOn ℝ ∞ (fun x=>A x i k) U)
    (hG : ∀ k, ContinuousOn (fun x=>G x k) U)
    (hH : ∀ k i, ContinuousOn (fun x=>H x k i) U) (hf : ContinuousOn f U) :
    ContinuousOn (normalFluxGradient q A G H f) U := by
  apply continuousOn_pi.mpr
  intro i
  by_cases hi : i=q
  · simp only [normalFluxGradient,if_pos hi]
    exact hf.neg.sub (continuousOn_nonNormalDivergence hU q hA hG hH)
  · simp only [normalFluxGradient,if_neg hi]
    exact ((continuousOn_coordinateDerivative_local hU (hA q q) i).mul (hG q)).add
      ((hA q q).continuousOn.mul (hH q i))

/-- The original divergence equation supplies the missing normal weak
flux derivative. This is an exact compact-test identity. -/
theorem normalFlux_weak_derivatives {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (q : Fin n) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {G : CoordinateSpace n → CoordinateSpace n} {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {f : CoordinateSpace n→ℝ}
    (hA : ∀ i k, ContDiffOn ℝ ∞ (fun x=>A x i k) U)
    (hG : ∀ k, ContinuousOn (fun x=>G x k) U)
    (hH : ∀ k i, ContinuousOn (fun x=>H x k i) U) (hf : ContinuousOn f U)
    (hknown : ∀ i k, i≠q ∨ k≠q → HasLocalWeakDerivative U (fun x=>G x k) (fun x=>H x k i) i)
    (hweak : ∀ ψ : smoothCompactCore n, tsupport ψ.1⊆U →
      (∫ x, ∑ i : Fin n, ∑ k : Fin n, A x i k*G x k*coordinateDerivative i ψ.1 x)=∫ x,f x*ψ.1 x) :
    ∀ i, HasLocalWeakDerivative U (fun x=>A x q q*G x q)
      (fun x=>normalFluxGradient q A G H f x i) i := by
  intro i
  by_cases hi : i=q
  · subst i
    intro ψ hψ
    let P := fun (p : Fin n×Fin n) (x : CoordinateSpace n)=>
      coordinateDerivative p.1 (fun y=>A y p.1 p.2) x*G x p.2+A x p.1 p.2*H x p.2 p.1
    let I := fun (p : Fin n×Fin n)=>(∫ x,A x p.1 p.2*G x p.2*coordinateDerivative p.1 ψ.1 x)
    let J := fun (p : Fin n×Fin n)=>(∫ x,P p x*ψ.1 x)
    let T : Finset (Fin n×Fin n) := Finset.univ.erase (q,q)
    have hPI (p : Fin n×Fin n) : ContinuousOn (P p) U :=
      ((continuousOn_coordinateDerivative_local hU (hA p.1 p.2) p.1).mul (hG p.2)).add
        ((hA p.1 p.2).continuousOn.mul (hH p.2 p.1))
    have hI (p : Fin n×Fin n) : Integrable (fun x=>A x p.1 p.2*G x p.2*coordinateDerivative p.1 ψ.1 x) volume :=
      integrable_local_mul_compact hU ((hA p.1 p.2).continuousOn.mul (hG p.2))
        (smooth_coordinateDerivative ψ.2.1 p.1).continuous (ψ.2.2.fderiv_apply (𝕜:=ℝ) _)
        ((coordinateDerivative_tsupport_subset ψ.1 p.1).trans hψ)
    have hJ (p : Fin n×Fin n) : Integrable (fun x=>P p x*ψ.1 x) volume :=
      integrable_local_mul_compact hU (hPI p) ψ.2.1.continuous ψ.2.2 hψ
    have hIJ (p : Fin n×Fin n) (hp : p∈T) : I p= -J p := by
      have hpne : p≠(q,q) := (Finset.mem_erase.mp hp).1
      have hor : p.1≠q ∨ p.2≠q := by
        by_contra hn
        simp only [not_or,not_not] at hn
        exact hpne (Prod.ext hn.1 hn.2)
      exact (hknown p.1 p.2 hor).mul_smooth hU (hG p.2) (hH p.2 p.1) (hA p.1 p.2) ψ hψ
    have htotal : (∑ p : Fin n×Fin n,I p)=∫ x,f x*ψ.1 x := by
      rw [show (∑ p : Fin n×Fin n,I p)=∫ x,∑ p : Fin n×Fin n,
        A x p.1 p.2*G x p.2*coordinateDerivative p.1 ψ.1 x from
          (integral_finset_sum _ (fun p _=>hI p)).symm]
      simpa only [Fintype.sum_prod_type] using hweak ψ hψ
    have hsplit : (∑ p∈T,I p)+I (q,q)=∫ x,f x*ψ.1 x := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ (q,q))]
      exact htotal
    have hsum : (∑ p∈T,I p)= -(∑ p∈T,J p) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl hIJ
    have hJsum : (∑ p∈T,J p)=∫ x,nonNormalDivergence q A G H x*ψ.1 x := by
      rw [show (∑ p∈T,J p)=∫ x,∑ p∈T,P p x*ψ.1 x from
        (integral_finset_sum _ (fun p _=>hJ p)).symm]
      apply integral_congr_ae
      apply ae_of_all
      intro x
      simp only [nonNormalDivergence,Finset.sum_mul,P,T]
    rw [hsum,hJsum] at hsplit
    have hF := integrable_local_mul_compact hU hf ψ.2.1.continuous ψ.2.2 hψ
    have hN := integrable_local_mul_compact hU (continuousOn_nonNormalDivergence hU q hA hG hH)
      ψ.2.1.continuous ψ.2.2 hψ
    have hout : (∫ x,normalFluxGradient q A G H f x q*ψ.1 x)=
        -(∫ x,f x*ψ.1 x)-(∫ x,nonNormalDivergence q A G H x*ψ.1 x) := by
      have he := integral_sub hF.neg hN
      simp only [Pi.neg_apply] at he
      rw [← integral_neg,← he]
      apply integral_congr_ae
      apply ae_of_all
      intro x
      simp only [normalFluxGradient,ite_true]
      ring
    rw [hout]
    change I (q,q)=_
    linarith
  · simpa only [normalFluxGradient,if_neg hi] using
      (hknown i q (Or.inl hi)).mul_smooth hU (hG q) (hH q i) (hA q q)

/-- The normal component becomes genuinely C¹ by recovering its flux,
then dividing by the actual nonzero elliptic normal coefficient. -/
theorem normal_component_contDiffOn_one_of_nonNormalWeakDerivatives
    {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (q : Fin n) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {G : CoordinateSpace n → CoordinateSpace n} {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {f : CoordinateSpace n→ℝ}
    (hA : ∀ i k, ContDiffOn ℝ ∞ (fun x=>A x i k) U)
    (hG : ∀ k, ContinuousOn (fun x=>G x k) U)
    (hH : ∀ k i, ContinuousOn (fun x=>H x k i) U) (hf : ContinuousOn f U)
    (hknown : ∀ i k, i≠q ∨ k≠q → HasLocalWeakDerivative U (fun x=>G x k) (fun x=>H x k i) i)
    (hweak : ∀ ψ : smoothCompactCore n, tsupport ψ.1⊆U →
      (∫ x, ∑ i : Fin n, ∑ k : Fin n, A x i k*G x k*coordinateDerivative i ψ.1 x)=∫ x,f x*ψ.1 x)
    (hneq : ∀ x∈U,A x q q≠0) :
    ContDiffOn ℝ 1 (fun x=>G x q) U := by
  have hD := normalFlux_weak_derivatives hU q hA hG hH hf hknown hweak
  obtain ⟨hQ,_⟩ := contDiffOn_one_of_continuous_coordinate_weak_components hU
    ((hA q q).continuousOn.mul (hG q)) (continuousOn_normalFluxGradient hU q hA hG hH hf) hD
  have ha1 : ContDiffOn ℝ 1 (fun x=>A x q q) U := (hA q q).of_le (by simp)
  apply (hQ.div ha1 hneq).congr
  intro x hx
  dsimp only
  exact (mul_div_cancel_left₀ (G x q) (hneq x hx)).symm

/-- The actual normal Hessian row, obtained from the flux derivative and
positive coefficient division. It is continuous wherever the input
coefficient/first/non-normal fields are continuous. -/
def recoveredNormalRow (q : Fin n)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (G : CoordinateSpace n → CoordinateSpace n)
    (H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (f : CoordinateSpace n→ℝ)
    (x : CoordinateSpace n) (i : Fin n) : ℝ :=
  (normalFluxGradient q A G H f x i-coordinateDerivative i (fun y=>A y q q) x*G x q)/A x q q

/-- The recovered normal row is the genuine Fréchet derivative of the
normal first-derivative component. -/
theorem normal_component_hasFDerivAt_of_nonNormalWeakDerivatives
    {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (q : Fin n) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {G : CoordinateSpace n → CoordinateSpace n} {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {f : CoordinateSpace n→ℝ}
    (hA : ∀ i k, ContDiffOn ℝ ∞ (fun x=>A x i k) U)
    (hG : ∀ k, ContinuousOn (fun x=>G x k) U)
    (hH : ∀ k i, ContinuousOn (fun x=>H x k i) U) (hf : ContinuousOn f U)
    (hknown : ∀ i k, i≠q ∨ k≠q → HasLocalWeakDerivative U (fun x=>G x k) (fun x=>H x k i) i)
    (hweak : ∀ ψ : smoothCompactCore n, tsupport ψ.1⊆U →
      (∫ x, ∑ i : Fin n, ∑ k : Fin n, A x i k*G x k*coordinateDerivative i ψ.1 x)=∫ x,f x*ψ.1 x)
    (hneq : ∀ x∈U,A x q q≠0) {x : CoordinateSpace n} (hx : x∈U) :
    HasFDerivAt (fun y=>G y q) (coordinateCovector (recoveredNormalRow q A G H f x)) x := by
  have hQweak := normalFlux_weak_derivatives hU q hA hG hH hf hknown hweak
  obtain ⟨_,hQ⟩ := contDiffOn_one_of_continuous_coordinate_weak_components hU
    ((hA q q).continuousOn.mul (hG q)) (continuousOn_normalFluxGradient hU q hA hG hH hf) hQweak
  have hg1 := normal_component_contDiffOn_one_of_nonNormalWeakDerivatives hU q hA hG hH hf hknown hweak hneq
  have hdg := (hg1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hda := ((hA q q).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have he := (hda.hasFDerivAt.mul hdg.hasFDerivAt).unique (hQ x hx)
  have hrow : coordinateGradient (fun y=>G y q) x=recoveredNormalRow q A G H f x := by
    funext i
    have hh := congrArg (fun L : CoordinateSpace n→L[ℝ]ℝ=>L (Pi.single i 1)) he
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
      coordinateCovector_single] at hh
    change coordinateDerivative i (fun y=>G y q) x=_
    unfold recoveredNormalRow
    apply (eq_div_iff (hneq x hx)).mpr
    change coordinateDerivative i (fun y=>G y q) x*A x q q=
      normalFluxGradient q A G H f x i-coordinateDerivative i (fun y=>A y q q) x*G x q
    change A x q q*coordinateDerivative i (fun y=>G y q) x+
      G x q*coordinateDerivative i (fun y=>A y q q) x=normalFluxGradient q A G H f x i at hh
    linarith
  have hd := hdg.hasFDerivAt
  rw [← coordinateCovector_gradient,hrow] at hd
  exact hd

end GaussianTilt.MomentMapLinearDirichlet
