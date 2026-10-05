import GaussianTilt.MomentMapSchauderGlobalFlattenedFields

/-! # The literal scaled curved-chart equation and its true boundary trace -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2200000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.HolderSpace
variable {n : ℕ}

lemma euclideanEllipticOperator_smul_coefficient (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (u : KernelSpace n → ℝ) (x : KernelSpace n) :
    euclideanEllipticOperator (c • A) u x=c*euclideanEllipticOperator A u x := by
  simp only [euclideanEllipticOperator,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

lemma euclideanEllipticOperator_comp_smul_at (A : Matrix (Fin n) (Fin n) ℝ)
    {u : KernelSpace n → ℝ} (r : ℝ) (x : KernelSpace n) (hu : ContDiffAt ℝ 2 u (r • x)) :
    euclideanEllipticOperator A (fun y => u (r • y)) x=r^2*euclideanEllipticOperator A u (r • x) := by
  have hu' : ContDiffAt ℝ 2 u (r • x+(0 : KernelSpace n)) := by simpa only [add_zero] using hu
  have hh := secondFrechet_comp_dilate_translate_at (0 : KernelSpace n) x r hu'
  simp only [add_zero] at hh
  simp only [euclideanEllipticOperator,hh,ContinuousLinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The scaled flattening map has the exact curvature drift; this is the
actual second chain rule, with only local C² regularity of the unknown. -/
theorem ellipticOperator_comp_scaled_flattening_at (A : Matrix (Fin n) (Fin n) ℝ)
    {v w : KernelSpace n → ℝ} (a : KernelSpace n) (j : Fin n) (s : ℝ) {x : KernelSpace n}
    (hw : ContDiffAt ℝ 2 w x) (hv : ContDiffAt ℝ 2 v (scaledFlatteningMap w a j s x)) :
    euclideanEllipticOperator A (v ∘ scaledFlatteningMap w a j s) x=
      euclideanEllipticOperator ((s⁻¹)^2 • flatteningCoefficient A w j x) v (scaledFlatteningMap w a j s x)+
        fderiv ℝ v (scaledFlatteningMap w a j s x)
          ((-s⁻¹*euclideanEllipticOperator A w x) • EuclideanSpace.basisFun (Fin n) ℝ j) := by
  let q := fun z : KernelSpace n => v (s⁻¹ • z)
  have hv0 : ContDiffAt ℝ 2 v (s⁻¹ • flatteningMap w a j x) := hv
  have hq : ContDiffAt ℝ 2 q (flatteningMap w a j x) := hv0.comp _
    ((contDiff_const (c := s⁻¹)).smul (contDiff_id : ContDiff ℝ 2 (id : KernelSpace n → KernelSpace n))).contDiffAt
  have hh := ellipticOperator_comp_flattening_at A a j hw hq
  have hd : fderiv ℝ q (flatteningMap w a j x)=s⁻¹ • fderiv ℝ v (scaledFlatteningMap w a j s x) := by
    have hv' : ContDiffAt ℝ 2 v (s⁻¹ • flatteningMap w a j x+(0 : KernelSpace n)) := by simpa only [add_zero] using hv
    simpa only [add_zero] using fderiv_comp_dilate_translate_at (0 : KernelSpace n) (flatteningMap w a j x) s⁻¹ hv'
  change euclideanEllipticOperator A (q ∘ flatteningMap w a j) x=_
  rw [hh,euclideanEllipticOperator_comp_smul_at _ s⁻¹ _ hv,hd,euclideanEllipticOperator_smul_coefficient]
  simp only [ContinuousLinearMap.smul_apply,map_smul,smul_eq_mul]
  dsimp only [scaledFlatteningMap]
  ring

/-- A true local inverse and literal closed-set value agreement yield
an ambient neighborhood identity at every interior point. -/
lemma chart_value_recovery_germ {O T : Set (KernelSpace n)} (hO : IsOpen O)
    {u v : KernelSpace n → ℝ} {φ ψ : KernelSpace n → KernelSpace n} (hφ : Continuous φ)
    (hleft : ∀ x ∈ O, φ x ∈ T → ψ (φ x)=x)
    (hvalue : ∀ z ∈ T, v z=u (ψ z)) {x : KernelSpace n}
    (hx : x ∈ O) (hz : φ x ∈ interior T) : u =ᶠ[𝓝 x] (v ∘ φ) := by
  have hn := hφ.tendsto x (isOpen_interior.mem_nhds hz)
  filter_upwards [hO.mem_nhds hx,hn] with y hy hyT
  change u y=v (φ y)
  rw [hvalue _ (interior_subset hyT),hleft y hy (interior_subset hyT)]

/-- The literal equation reaches the closed boundary by continuity of
actual jet fields. No ambient C² boundary extension is needed. -/
theorem closed_jet_equation_of_interior
    {S : Set (KernelSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty)
    {α : ℝ} (hα : 0 < α) (J : Jet (KernelSpace n) ℝ hS α)
    (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ) (b : KernelSpace n → KernelSpace n) (f : KernelSpace n → ℝ)
    (hAc : ∀ i k, ContinuousOn (fun x => A x i k) S) (hbc : ContinuousOn b S) (hfc : ContinuousOn f S)
    (heq : ∀ x ∈ interior S,
      euclideanEllipticOperator (A x) (extendValue α (jetValue (KernelSpace n) ℝ hS α J)) x+
        fderiv ℝ (extendValue α (jetValue (KernelSpace n) ℝ hS α J)) x (b x)=f x) :
    ∀ x ∈ S,
      matrixContraction (A x) (bilinearEntryMatrix (extendValue α (jetSecond (KernelSpace n) ℝ hS α J) x))+
        extendValue α (jetFirst (KernelSpace n) ℝ hS α J) x (b x)=f x := by
  let D := extendValue α (jetFirst (KernelSpace n) ℝ hS α J)
  let B := extendValue α (jetSecond (KernelSpace n) ℝ hS α J)
  let g := fun x => matrixContraction (A x) (bilinearEntryMatrix (B x))+D x (b x)
  have hDc : ContinuousOn D S := continuousOn_extendValue α _
  have hBc : ContinuousOn B S := continuousOn_extendValue α _
  have hgc : ContinuousOn g S := by
    apply ContinuousOn.add
    · apply continuousOn_finset_sum
      intro i _
      apply continuousOn_finset_sum
      intro k _
      exact (hAc i k).mul ((hBc.clm_apply continuousOn_const).clm_apply continuousOn_const)
    · exact hDc.clm_apply hbc
  have heI : EqOn g f (interior S) := by
    intro x hx
    have hD := (jet_hasFDerivAt hS hα J hx).fderiv
    have hB := jet_second_eq_fderiv_fderiv hS hα J hx
    have hh := heq x hx
    change matrixContraction (A x) (bilinearEntryMatrix (B x))+D x (b x)=f x
    change euclideanEllipticOperator (A x) _ x+_=f x at hh
    simpa only [euclideanEllipticOperator,matrixContraction,bilinearEntryMatrix,hD,hB,D,B] using hh
  have hcl : closure (interior S)=S := (hS.closure_interior_eq_closure_of_nonempty_interior hint).trans hSc.closure_eq
  exact heI.of_subset_closure hgc hfc interior_subset (by rw [hcl])

end GaussianTilt.MomentMapSchauder
