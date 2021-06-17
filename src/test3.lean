import measure_theory.prod
import measure_theory.giry_monad
import measure_theory.measurable_space_def
import .dp
import .missing_integration

--TODO: move
@[measurability]
protected theorem measurable_prod_swap (α β : Type*) [measurable_space α] [measurable_space β] : 
  measurable (@prod.swap α β) :=
by unfold prod.swap; measurability

open measure_theory ennreal

variables {Ω₁ Ω₂ : Type} [measurable_space Ω₁] [measurable_space Ω₂]

variables (P₁ : measure Ω₁) (P₂ : measure Ω₂) [hP₁ : probability_measure P₁] [hP₂ : probability_measure P₂]

local infix ` ⊗ `:50  := measure.prod

section part1

variables (V W : set (Ω₁ × Ω₂)) (ε δ : ennreal) {hV : measurable_set V} {hW : measurable_set W}

include hP₁ hP₂ hV hW

lemma part1_step1 (h : ∀ ω₁ : Ω₁, P₂ (prod.mk ω₁ ⁻¹' V) ≤ ε * P₂ (prod.mk ω₁ ⁻¹' W) + δ) :
  (P₁ ⊗ P₂) V ≤
    ε * (P₁ ⊗ P₂) W + δ := 
calc 
  (P₁ ⊗ P₂) V = ∫⁻ (ω₁ : Ω₁), P₂ (prod.mk ω₁ ⁻¹' V) ∂P₁ : 
  begin
    rw measure.prod_apply hV,
    apply_instance
  end
  ... ≤ ∫⁻ (ω₁ : Ω₁), ε * P₂ (prod.mk ω₁ ⁻¹' W) + δ ∂P₁ : 
  begin
    apply lintegral_mono,
    apply h,
  end
  ... = ε * ∫⁻ (ω₁ : Ω₁), P₂ (prod.mk ω₁ ⁻¹' W) ∂P₁ + δ : 
  begin
    have : measurable (λ (ω : Ω₁), P₂ (prod.mk ω ⁻¹' W)) := sorry,
    rw lintegral_add,
    rw lintegral_const,
    rw [probability_measure.measure_univ, mul_one],
    rw lintegral_const_mul,
    measurability,
  end
  ... = 
    ε * (P₁ ⊗ P₂) W + δ :
  begin
    rw measure.prod_apply hW,
    apply_instance
  end

lemma part1_step2 
  (h : ∀ ω₂ : Ω₂, P₁ ((λ ω₁, prod.mk ω₁ ω₂) ⁻¹' V) 
    ≤ ε * P₁ ((λ ω₁, prod.mk ω₁ ω₂) ⁻¹' W) + δ) :
  (P₁ ⊗ P₂) V ≤
    ε * (P₁ ⊗ P₂) W + δ := 
begin
  rw [← measure.prod_swap, measure.map_apply, measure.map_apply],
  apply part1_step1,
  measurability!
end

end part1

section part2

-- Type of possible databases:
variables {X : Type} [database_type X] (x₀ x₁ : X) (hx : database_type.neighboring x₀ x₁)

-- Possible outputs:
variables {O₁ O₂ : Type} [hO₁ : measurable_space O₁] [hO₂ : measurable_space O₂]

-- Mechanisms:
variables (M₁ : X → Ω₁ → O₁) [hM₁ : ∀ x : X, measurable (M₁ x)] 
          (M₂ : O₁ → X → Ω₂ → O₂) [hM₂ : ∀ (o₁ : O₁) (x : X), measurable (M₂ o₁ x)]

-- Set of views:
variables (𝒱 : set (O₁ × O₂))

variables (ε₁ ε₂ δ₁ δ₂ : ennreal)

include x₁ ε₂ δ₂ hP₁ hP₂ hO₁ hO₂ hx

lemma part2_step1 (hdp₂ : ∀ o₁, diff_private P₂ (M₂ o₁) ε₂ δ₂):
  (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₀ ω.2) ∈ 𝒱} ≤
    exp ε₂ * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₁ ω.2) ∈ 𝒱} + δ₂ := 
begin
  apply part1_step1,
  sorry, -- measurability
  sorry, -- measurability
  exact λ ω₁, hdp₂ (M₁ x₀ ω₁) x₀ x₁ {o₂ : O₂ | (M₁ x₀ ω₁, o₂) ∈ 𝒱} hx,
end

lemma part2_step2 (hdp₁ : diff_private P₁ M₁ ε₁ δ₁):
  (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₁ ω.2) ∈ 𝒱} ≤
    exp ε₁ * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.1, M₂ (M₁ x₁ ω.1) x₁ ω.2) ∈ 𝒱} + δ₁ := 
begin
  apply part1_step2,
  sorry, -- measurability
  sorry, -- measurability
  exact λ ω₁, hdp₁ x₀ x₁ {o₁ : O₁ | (o₁, M₂ o₁ x₁ ω₁) ∈ 𝒱} hx
end

end part2

section part3




end part3