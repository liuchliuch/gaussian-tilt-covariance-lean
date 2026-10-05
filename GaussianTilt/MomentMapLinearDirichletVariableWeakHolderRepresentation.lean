import GaussianTilt.MomentMapLinearDirichletVariableWeakHolderLoads

/-! # True Hölder representatives of the differentiated L² vector load -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 1000

/-- Replacing the original weak derivative by its actually constructed
Hölder representative produces a literal Hölder representative of the
actual differentiated L² load. The two exponents may differ initially. -/
theorem differentiated_vector_load_holder_representative
    {S U:Set (CoordinateSpace n)} (a:Fin n)
    (u:VolumeJet n) (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (D:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (G:Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (hG:∀ i,∀ᵐ x∂volume,x∈U → G i x= -(if i=a then f x else 0)-∑ k:Fin n,D x i k*u k.succ x)
    {f₀:CoordinateSpace n → ℝ} {q:CoordinateSpace n → CoordinateSpace n}
    (hf:∀ᵐ x∂volume,x∈U → f x=f₀ x)
    (hq:∀ k,∀ᵐ x∂volume,x∈U → u k.succ x=q x k)
    {α γ β:ℝ} (hβ:0≤β) (hβα:β≤α) (hβγ:β≤γ)
    (hfH:BoundedHolderOn α f₀ S)
    (hqH:∀ k,BoundedHolderOn γ (fun x=>q x k) S)
    (hDH:∀ i k,BoundedHolderOn β (fun x=>D x i k) S) :
    ∃ g:CoordinateSpace n → CoordinateSpace n,
      BoundedHolderOn β g S ∧ (∀ i,∀ᵐ x∂volume,x∈U → G i x=g x i) ∧
      ∀ x i,g x i= -(if i=a then f₀ x else 0)-∑ k:Fin n,D x i k*q x k := by
  let g := differentiatedLoadFunction a f₀ D q
  have hgH := boundedHolderOn_differentiatedLoad a (boundedHolderOn_lower_exponent hβ hβα hfH)
    hDH (fun k=>boundedHolderOn_lower_exponent hβ hβγ (hqH k))
  refine ⟨g,BoundedHolderOn.pi hgH,?_,fun _ _=>rfl⟩
  intro i
  filter_upwards [hG i,hf,ae_all_iff.mpr hq] with x hGi hfi hqi hx
  rw [hGi hx,hfi hx]
  change _= -(if i=a then f₀ x else 0)-∑ k:Fin n,D x i k*q x k
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [hqi k hx]

/-- The actual Hölder representative supplies the radius-scaled centered
oscillation bound used by harmonic replacement, uniformly in every center
of the compact coordinate patch. -/
theorem centered_load_bound_of_holder_representative
    {S U:Set (CoordinateSpace n)} {g:CoordinateSpace n → CoordinateSpace n} {β:ℝ} (hβ:0≤β)
    (hg:BoundedHolderOn β g S)
    (G:Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (hG:∀ k,∀ᵐ x∂volume,x∈U → G k x=g x k) :
    ∃ H:ℝ,0<H ∧ ∀ a∈S,∀ (Ω:Set (CoordinateSpace n)),Ω⊆U → Ω⊆S →
      ∀ r:ℝ,0≤r → (∀ x∈Ω,‖x-a‖≤r) →
        ∀ k,∀ᵐ x∂volume,x∈Ω → |G k x-g a k|≤H*r^β := by
  obtain ⟨C,hC,hb,hh⟩ := hg
  refine ⟨C+1,by linarith,?_⟩
  intro a ha Ω hΩU hΩS r hr hrad k
  filter_upwards [hG k] with x hx hxΩ
  rw [hx (hΩU hxΩ)]
  have he : |g x k-g a k|≤‖g x-g a‖ := norm_le_pi_norm (g x-g a) k
  have hp := Real.rpow_le_rpow (norm_nonneg (x-a)) (hrad x hxΩ) hβ
  exact he.trans ((hh x (hΩS hxΩ) a ha).trans
    ((mul_le_mul_of_nonneg_left hp hC).trans
      (mul_le_mul_of_nonneg_right (by linarith : C≤C+1) (Real.rpow_nonneg hr β))))

end GaussianTilt.MomentMapLinearDirichlet
