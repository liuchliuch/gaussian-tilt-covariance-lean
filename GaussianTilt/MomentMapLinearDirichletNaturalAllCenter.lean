import GaussianTilt.MomentMapLinearDirichletNaturalCampanatoEstimates
import GaussianTilt.MomentMapLinearDirichletBoundaryInteriorCampanatoCover

/-! # Genuine all-center Campanato estimates from the literal weak equation -/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- Boundary normal means and actual affine harmonic replacement remove the
height dependence of the interior starting scale. All approximation estimates
are derived from the displayed weak PDE. -/
theorem natural_all_center_campanato [NeZero n]
    (j : Fin n) {R lam Λ D β : ℝ} (hR : 0<R) (hlam : 0<lam) (hΛ : 0≤Λ) (hD : 0≤D)
    (hβ : 0<β) (hβ1 : β≤1) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {KA : ℝ}
    (hA : WeakBallCoefficientBounds A KA R lam Λ D β)
    {Ω : Set (CoordinateSpace n)} (hΩ : Ω⊆{x|0<x j}) (u : dirichletSobolev Ω)
    (hDomain : coordinateHalfBall j R⊆Ω)
    {F H : ℝ} {f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))}
    {G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))} {g : KernelSpace n → Fin n → ℝ}
    (hLoad : WeakHalfBallLoadBounds j R β F H f G g)
    (heq : ∀v:dirichletSobolev (coordinateHalfBall j R),
      variableJetEnergy A hA.measurable hA.nonneg hA.bound u.1 v.1=variableScalarVectorLoad (coordinateHalfBall j R) f G v) :
    ∃ s C : ℝ,0<s ∧ s≤R ∧ 0≤C ∧ ∀x:KernelSpace n,‖x‖≤s/4 → 0≤x j →
      ∀r:ℝ,0<r → r≤s → ∃p:KernelSpace n,
      (∫y in upperCampanatoBall j x r,‖euclideanWeakGradient u.1 y-p‖^2)≤C*r^((n:ℝ)+β) := by
  obtain ⟨rB,Cb,hrB,hrBR,hCb,hBoundary⟩ :=
    natural_boundary_normal_excess j hR hlam hΛ hD hβ hβ1 hA hΩ u hDomain hLoad heq
  obtain ⟨ρ,Ci₀,N,hρ,hρ1,hCi₀,hN,hInterior⟩ :=
    natural_affine_interior_excess j hR hlam hΛ hD hβ hβ1 hA u hDomain hLoad heq
  let W₀ := euclideanWeakGradient u.1
  have hW₀ : MemLp W₀ 2 volume := euclideanWeakGradient_memLp u.1
  let M₀ := dirichletEnergy Ω u u
  have hM₀ : 0≤M₀ := by dsimp [M₀]; rw [dirichletEnergy_eq_gradientNorm_sq]; positivity
  let Z : Set (KernelSpace n) := {z|‖z‖≤R/4 ∧ z j=0}
  have hZplane : ∀z∈Z,z j=0 := fun _ hz=>hz.2
  have hZE : ∀z∈Z,(∫y in upperCampanatoBall j z rB,‖W₀ y‖^2)≤M₀ := by
    intro z hz
    dsimp [M₀]
    rw [dirichletEnergy_eq_gradientNorm_sq,←integral_euclideanWeakGradient_sq]
    exact setIntegral_le_integral (hW₀.integrable_norm_pow (p:=2) (by norm_num))
      (ae_of_all _ (fun _=>sq_nonneg _))
  obtain ⟨L,hL,hStart⟩ := exists_uniform_normal_interior_start (n:=n) hrB hCb hβ hM₀
  have hStart' := hStart j Z W₀ hZplane (fun z _=>hW₀.restrict _) hZE
    (fun z hz=>hBoundary z hz.1 hz.2)
  let a₀ := min (R/16) (min (rB/8) (1/8))
  have ha₀ : 0<a₀ := by dsimp [a₀]; positivity
  have haR : a₀≤R/16 := min_le_left _ _
  have haB : a₀≤rB/8 := (min_le_right _ _).trans (min_le_left _ _)
  have ha1 : a₀≤1/8 := (min_le_right _ _).trans (min_le_right _ _)
  let W : Set (KernelSpace n) := {x|‖x‖≤a₀ ∧ 0≤x j}
  have hProj : ∀x∈W,(x-x j • EuclideanSpace.basisFun (Fin n) ℝ j)∈Z := by
    intro x hx
    constructor
    · have ht:=norm_sub_le x (x j • EuclideanSpace.basisFun (Fin n) ℝ j)
      rw [norm_smul,Real.norm_eq_abs,(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one] at ht
      have hh : |x j|≤‖x‖ := PiLp.norm_apply_le x j
      linarith [hx.1]
    · simp
  let η := ρ/2
  have hη : 0<η := by dsimp [η]; positivity
  let M := Cb*(8:ℝ)^((n:ℝ)+β)
  have hM : 0≤M := by dsimp [M]; positivity
  let Ci := Ci₀*(M+N*(2*F+(n:ℝ)*(H+(n:ℝ)*D*L))^2)
  have hCi : 0≤Ci := by dsimp [Ci]; positivity
  have hi : ∀x∈W,∀r:ℝ,0<r → r≤η*x j → ∃p:KernelSpace n,
      (∫y in Metric.ball x r,‖W₀ y-p‖^2)≤Ci*r^((n:ℝ)+β) := by
    intro x hx r hr hrr
    have hxj : 0<x j := by nlinarith [hx.2]
    have hxjn : x j≤‖x‖ := (le_abs_self _).trans (PiLp.norm_apply_le x j)
    have hxB : 4*x j≤rB := by linarith [hx.1]
    obtain ⟨t,ht,hInit⟩ := hStart' x hxj hxB (hProj x hx)
    have hp : ‖t • EuclideanSpace.basisFun (Fin n) ℝ j‖≤L := by
      simpa only [norm_smul,Real.norm_eq_abs,(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one] using ht
    have hInit' : (∫y in Metric.ball x (x j/2),‖W₀ y-t • EuclideanSpace.basisFun (Fin n) ℝ j‖^2)
        ≤M*(x j/2)^((n:ℝ)+β) := by
      convert hInit using 1
      dsimp [M]
      rw [mul_assoc,←Real.mul_rpow (by norm_num : (0:ℝ)≤8) (by positivity : 0≤x j/2)]
      congr 2
      ring
    have hBall : coordinateFullBall x (2*(x j/2))⊆coordinateHalfBall j R := by
      intro y hy
      have hyx : ‖(dirichletCoordinateEquiv n).symm y-x‖<x j := by
        simpa only [coordinateFullBall,mem_preimage,Metric.mem_ball,dist_eq_norm,show 2*(x j/2)=x j by ring] using hy
      have hcoord : |((dirichletCoordinateEquiv n).symm y) j-x j|≤‖(dirichletCoordinateEquiv n).symm y-x‖ :=
        PiLp.norm_apply_le ((dirichletCoordinateEquiv n).symm y-x) j
      constructor
      · change ‖(dirichletCoordinateEquiv n).symm y‖<R
        have hn : ‖(dirichletCoordinateEquiv n).symm y‖≤‖(dirichletCoordinateEquiv n).symm y-x‖+‖x‖ := by
          simpa only [sub_add_cancel] using norm_add_le ((dirichletCoordinateEquiv n).symm y-x) x
        linarith [hx.1]
      · have hcoord' : ((dirichletCoordinateEquiv n).symm y) j=y j := rfl
        rw [hcoord'] at hcoord
        linarith [neg_abs_le (y j-x j)]
    have hres:=hInterior x (t • EuclideanSpace.basisFun (Fin n) ℝ j) (x j/2) M L
      (by linarith [hx.1]) hx.2 (by positivity) (by linarith [hx.1]) hM hL hp hBall hInit' r hr
      (by dsimp [η] at hrr; nlinarith)
    exact ⟨ballMeanGradient u.1 x r,hres⟩
  have hb : ∀z∈Z,∀r:ℝ,0<r → r≤rB → ∃p:KernelSpace n,
      (∫y in upperCampanatoBall j z r,‖W₀ y-p‖^2)≤Cb*r^((n:ℝ)+β) := by
    intro z hz r hr hrr
    exact ⟨normalMean (volume.restrict (upperCampanatoBall j z r)) j W₀ •
      EuclideanSpace.basisFun (Fin n) ℝ j,hBoundary z hz.1 hz.2 r hr hrr⟩
  have hCover:=boundary_interior_campanato_cover_explicit hη hrB hCb hCi j W Z W₀ hW₀
    (fun _ hx=>hx.2) hProj hb hi
  let s := min (rB/(1+η⁻¹)) (4*a₀)
  have hs : 0<s := by dsimp [s]; positivity
  have hsr : s≤rB/(1+η⁻¹) := min_le_left _ _
  have hsa : s≤4*a₀ := min_le_right _ _
  refine ⟨s,max Ci (Cb*(1+η⁻¹)^((n:ℝ)+β)),hs,by linarith,
    hCi.trans (le_max_left _ _),?_⟩
  intro x hx hxj r hr hrr
  exact hCover x ⟨by linarith,hxj⟩ r hr (hrr.trans hsr)

end GaussianTilt.MomentMapLinearDirichlet
