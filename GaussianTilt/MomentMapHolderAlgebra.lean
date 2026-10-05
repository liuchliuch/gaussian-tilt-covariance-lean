import GaussianTilt.MomentMapHolderSpace

/-! # Actual continuous multiplication in the Hölder Banach space -/
noncomputable section
open Set
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable (X : Type*) [MetricSpace X]

lemma product_holder_bound (α : ℝ) (f g : Space X ℝ α) (x y : X) :
    ‖value X ℝ α f x * value X ℝ α g x - value X ℝ α f y * value X ℝ α g y‖ ≤
      (2 * ‖f‖ * ‖g‖) * dist x y ^ α := by
  have hf := norm_value_sub_le X ℝ α f x y
  have hg := norm_value_sub_le X ℝ α g x y
  have hfx := norm_value_apply_le X ℝ α f x
  have hgy := norm_value_apply_le X ℝ α g y
  have he : value X ℝ α f x * value X ℝ α g x - value X ℝ α f y * value X ℝ α g y =
      value X ℝ α f x * (value X ℝ α g x - value X ℝ α g y) +
        (value X ℝ α f x - value X ℝ α f y) * value X ℝ α g y := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  have h₁ := mul_le_mul hfx hg (norm_nonneg _) (norm_nonneg f)
  have h₂ := mul_le_mul hf hgy (norm_nonneg _) (mul_nonneg (norm_nonneg f) (Real.rpow_nonneg dist_nonneg α))
  nlinarith

def product (α : ℝ) (f g : Space X ℝ α) : Space X ℝ α :=
  ofBounded X ℝ α (value X ℝ α f * value X ℝ α g) (2 * ‖f‖ * ‖g‖)
    (product_holder_bound X α f g)

@[simp] lemma value_product (α : ℝ) (f g : Space X ℝ α) :
    value X ℝ α (product X α f g) = value X ℝ α f * value X ℝ α g := rfl

lemma norm_product_le (α : ℝ) (f g : Space X ℝ α) :
    ‖product X α f g‖ ≤ 2 * ‖f‖ * ‖g‖ := by
  apply (norm_ofBounded_le X ℝ α _ (by positivity) _).trans
  apply max_le ?_ le_rfl
  calc
    ‖value X ℝ α f * value X ℝ α g‖ ≤ ‖value X ℝ α f‖ * ‖value X ℝ α g‖ := norm_mul_le _ _
    _ ≤ ‖f‖ * ‖g‖ := mul_le_mul (norm_value_le X ℝ α f) (norm_value_le X ℝ α g)
      (norm_nonneg _) (norm_nonneg _)
    _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg f) (norm_nonneg g)]

def productLinear (α : ℝ) : Space X ℝ α →ₗ[ℝ] Space X ℝ α →ₗ[ℝ] Space X ℝ α :=
  LinearMap.mk₂ ℝ (product X α)
    (by
      intro f g h
      apply value_injective X ℝ α
      simp only [value_product, map_add, add_mul])
    (by
      intro c f g
      apply value_injective X ℝ α
      simp only [value_product, map_smul, smul_mul_assoc])
    (by
      intro f g h
      apply value_injective X ℝ α
      simp only [value_product, map_add, mul_add])
    (by
      intro c f g
      apply value_injective X ℝ α
      simp only [value_product, map_smul, mul_smul_comm])

/-- Pointwise multiplication is a genuine bounded bilinear map on the
constructed complete Hölder space. -/
def productCLM (α : ℝ) : Space X ℝ α →L[ℝ] Space X ℝ α →L[ℝ] Space X ℝ α :=
  (productLinear X α).mkContinuous₂ 2 (norm_product_le X α)

@[simp] lemma productCLM_apply (α : ℝ) (f g : Space X ℝ α) :
    productCLM X α f g = product X α f g := rfl

end GaussianTilt.HolderSpace
