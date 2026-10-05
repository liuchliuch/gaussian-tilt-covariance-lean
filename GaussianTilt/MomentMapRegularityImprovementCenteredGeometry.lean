import GaussianTilt.MomentMapAffineNormalization
import GaussianTilt.MomentMapRegularityAffineSectionBalance

/-! # Centering genuine affine sections at the original source point -/
noncomputable section
open Set Metric
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma centered_ball_of_reflection {S : Set (E n)} (hc : Convex ℝ S)
    (hball : closedBall (0:E n) 1⊆S) {x : E n} {η : ℝ} (hη : 0 < η)
    (hreflect : ∀ y∈S, x-η • (y-x)∈S) :
    closedBall x (η/(1+η))⊆S := by
  have hden : 0 < 1+η := by linarith
  have hzero : (0:E n)∈S := hball (by simp)
  have hxref : (1+η) • x∈S := by
    have hh := hreflect 0 hzero
    convert hh using 1 <;> module
  intro y hy
  let v : E n := ((1+η)/η) • (y-x)
  have hv : v∈closedBall (0:E n) 1 := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hden hη)]
    have hn : ‖y-x‖≤η/(1+η) := by simpa only [mem_closedBall,dist_eq_norm] using hy
    have hh := mul_le_mul_of_nonneg_left hn (div_pos hden hη).le
    have he : ((1+η)/η)*(η/(1+η))=1 := by field_simp
    simpa only [he] using hh
  have hcomb := hc (hball hv) hxref (show 0≤η/(1+η) by positivity)
    (show 0≤1/(1+η) by positivity) (by field_simp; ring : η/(1+η)+1/(1+η)=1)
  have he : (η/(1+η)) • v+(1/(1+η)) • ((1+η) • x)=y := by
    dsimp [v]
    rw [smul_smul,smul_smul]
    have h1 : η/(1+η)*((1+η)/η)=1 := by field_simp
    have h2 : 1/(1+η)*(1+η)=1 := by field_simp
    rw [h1,h2,one_smul,one_smul,sub_add_cancel]
  simpa only [he] using hcomb

/-- The max-simplex normalization can be centered at the actual supporting
point with a uniform positive inner radius supplied by the proved section
reflection balance. -/
theorem exists_centered_affine_normalization {S : Set (E n)}
    (hS : IsCompact S) (hc : Convex ℝ S) {x : E n} (hx : x∈interior S)
    {η : ℝ} (hη : 0 < η) (hreflect : ∀ y∈S, x-η • (y-x)∈S) :
    ∃ T : E n ≃L[ℝ] E n,
      closedBall (0:E n) (η/(2*(1+η)))⊆interior ((fun y=>T (y-x)) '' S) ∧
      (fun y=>T (y-x)) '' S⊆closedBall 0 (6*((n:ℝ)+1)^2) := by
  obtain ⟨a,T,hball,houter⟩ := exists_affine_normalization_explicit hS hc ⟨x,hx⟩
  let N := (fun y=>T (y-a)) '' S
  let z := T (x-a)
  have hNconv : Convex ℝ N := by
    have hh := (hc.translate (-a)).linear_image T.toLinearMap
    simpa only [image_image,Function.comp_def,neg_add_eq_sub] using hh
  have hz : z∈N := ⟨x,interior_subset hx,rfl⟩
  have hNreflect : ∀ y∈N, z-η • (y-z)∈N := by
    rintro y ⟨q,hq,rfl⟩
    refine ⟨x-η • (q-x),hreflect q hq,?_⟩
    dsimp [z]
    simp only [map_sub,map_smul]
    module
  have hcenter := centered_ball_of_reflection hNconv hball hη hNreflect
  have hden : 0 < 1+η := by linarith
  have he : (fun y=>T (y-x)) '' S=(fun y=>y-z) '' N := by
    rw [image_image]
    congr 1
    funext y
    dsimp [z]
    simp only [map_sub]
    abel
  refine ⟨T,?_,?_⟩
  · have hinner : closedBall (0:E n) (η/(1+η))⊆(fun y=>T (y-x)) '' S := by
      intro y hy
      rw [he]
      refine ⟨y+z,hcenter ?_,by simp⟩
      simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_right,sub_zero] using hy
    have hr : 0 < η/(1+η) := div_pos hη hden
    apply (closedBall_subset_ball (by
      convert half_lt_self hr using 1 <;> field_simp <;> ring : η/(2*(1+η))<η/(1+η))).trans
    exact interior_maximal (ball_subset_closedBall.trans hinner) isOpen_ball
  · intro y hy
    rw [he] at hy
    obtain ⟨q,hq,rfl⟩ := hy
    have hqnorm : ‖q‖≤3*((n:ℝ)+1)^2 := by simpa using houter hq
    have hznorm : ‖z‖≤3*((n:ℝ)+1)^2 := by simpa using houter hz
    rw [mem_closedBall,dist_zero_right]
    exact (norm_sub_le q z).trans (by linarith)

end GaussianTilt.MomentMapRegularity
