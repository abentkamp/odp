import measure_theory.prod
import .notes

open measure_theory

-- Underlying probablity spaces:
variables {Ω₁ Ω₂ : Type} [measurable_space Ω₁] [measurable_space Ω₂]

variables (μ₁ : measure Ω₁) (μ₂ : measure Ω₂) {hμ₁ : sigma_finite μ₁} {hμ₂ : sigma_finite μ₂}

-- Type of possible databases:
variables {X : Type} (x₀ x₁ : X)

-- Possible outputs:
variables {O : Type} [hO : measurable_space O]

-- Mechanisms:
variables (M₁ : X → Ω₁ → O) [hM₁ : ∀ x : X, measurable (M₁ x)] 
          (M₂ : X → (O × Ω₂) → O) [hM₂ : ∀ x : X, measurable (M₂ x)]

-- Set of views:
variables (𝒱' : set (O × O))

variables (ε₁ ε₂ δ₁ δ₂ : ennreal)

#check 
let V₀ : Ω₁ × Ω₂ → O × O := λ ω, (M₁ x₀ ω.1, M₂ x₀ (M₁ x₀ ω.1, ω.2)) in
λ ω : Ω₁ × Ω₂, V₀ ω ∈ 𝒱' 

#check (μ₁.prod μ₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ x₀ (M₁ x₀ ω.1, ω.2)) ∈ 𝒱'}

lemma meas1 : measurable_set {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ x₀ (M₁ x₀ ω.1, ω.2)) ∈ 𝒱'} := sorry



lemma aux (o₁ : O) : μ₂ {ω₂ : Ω₂ | (o₁, M₂ x₀ (o₁, ω₂)) ∈ 𝒱'} 
  ≤ ε₂ * μ₂ {ω₂ : Ω₂ | (o₁, M₂ x₁ (o₁, ω₂)) ∈ 𝒱'} + δ₂ := sorry

include x₁ ε₂ δ₂ hμ₂ hO

example : (μ₁.prod μ₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ x₀ (M₁ x₀ ω.1, ω.2)) ∈ 𝒱'} ≤
  sorry := 
  calc 
    (μ₁.prod μ₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ x₀ (M₁ x₀ ω.1, ω.2)) ∈ 𝒱'} 
      = ∫⁻ (ω₁ : Ω₁), μ₂ {ω₂ : Ω₂ | (M₁ x₀ ω₁, M₂ x₀ (M₁ x₀ ω₁, ω₂)) ∈ 𝒱'} ∂μ₁ : 
    begin
      rw measure.prod_apply (meas1 _ _ _ _),
      simp only [set.preimage_set_of_eq], 
      apply hμ₂ 
    end
    ... = ∫⁻ (o₁ : O), μ₂ {ω₂ : Ω₂ | (o₁, M₂ x₀ (o₁, ω₂)) ∈ 𝒱'} 
            ∂(measure.map (λ ω₁, M₁ x₀ ω₁)) μ₁ : begin
      have :=  (@lintegral_map _ _ _ μ₁ _ (λ (o₁ : O), μ₂ {ω₂ : Ω₂ | (o₁, M₂ x₀ (o₁, ω₂)) ∈ 𝒱'}) (λ ω₁, M₁ x₀ ω₁) _ _).symm,
      apply this,
      sorry, -- measurability
      sorry -- measurability
    end
   ... ≤ ∫⁻ (o₁ : O), ε₂ * μ₂ {ω₂ : Ω₂ | (o₁, M₂ x₁ (o₁, ω₂)) ∈ 𝒱'} + δ₂
           ∂(measure.map (λ ω₁, M₁ x₀ ω₁)) μ₁ :
    begin
      apply lintegral_mono,
      intro ω₁,
      apply aux,
    end
   ... = ∫⁻ (a : O),
      ε₂ * μ₂ {ω₂ : Ω₂ | (a, M₂ x₁ (a, ω₂)) ∈ 𝒱'} ∂⇑(measure.map
           (λ (ω₁ : Ω₁), M₁ x₀ ω₁))
        μ₁ +
    δ₂ * μ₁ (set.univ):
    begin
      rw lintegral_add,
      rw lintegral_const,
      rw measure.map_apply,
      rw set.preimage_univ,
      measurability,
      sorry, -- measurability
      sorry -- measurability
    end
   ... ≤ sorry : sorry