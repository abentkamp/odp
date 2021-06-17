import measure_theory.prod

open measure_theory

-- Underlying probablity spaces:
variables {Ω₁ Ω₂ : Type} [measurable_space Ω₁] [measurable_space Ω₂]

variables (P₁ : measure Ω₁) (P₂ : measure Ω₂) {hP₁ : sigma_finite P₁} {hP₂ : sigma_finite P₂}

-- Type of possible databases:
variables {X : Type} (x₀ x₁ : X)

-- Possible outputs:
variables {O₁ O₂ : Type} [hO₁ : measurable_space O₁] [hO₂ : measurable_space O₂]

-- Mechanisms:
variables (M₁ : X → Ω₁ → O₁) [hM₁ : ∀ x : X, measurable (M₁ x)] 
          (M₂ : O₁ → X → Ω₂ → O₂) [hM₂ : ∀ (o₁ : O₁) (x : X), measurable (M₂ o₁ x)]

-- Set of views:
variables (𝒱' : set (O₁ × O₂))

variables (ε₁ ε₂ δ₁ δ₂ : ennreal)

#check 
let V₀ : Ω₁ × Ω₂ → O₁ × O₂ := λ ω, (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₀ ω.2) in
λ ω : Ω₁ × Ω₂, V₀ ω ∈ 𝒱' 

#check (P₁.prod P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₀ ω.2) ∈ 𝒱'}

lemma meas1 : measurable_set {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₀ ω.2) ∈ 𝒱'} := sorry

lemma aux (v₁ : O₁) : P₂ {ω₂ : Ω₂ | (v₁, M₂ v₁ x₀ ω₂) ∈ 𝒱'} 
  ≤ ε₂ * P₂ {ω₂ : Ω₂ | (v₁, M₂ v₁ x₁ ω₂) ∈ 𝒱'} + δ₂ := sorry

include x₁ ε₂ δ₂ hP₂

example : (P₁.prod P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₀ ω.2) ∈ 𝒱'} ≤
  sorry := 
begin
  calc 
    (P₁.prod P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂ (M₁ x₀ ω.1) x₀ ω.2) ∈ 𝒱'} 
      = ∫⁻ (ω₁ : Ω₁), P₂ {ω₂ : Ω₂ | (M₁ x₀ ω₁, M₂ (M₁ x₀ ω₁) x₀ ω₂) ∈ 𝒱'} ∂P₁ : 
    begin
      rw measure.prod_apply (meas1 _ _ _ _),
      simp only [set.preimage_set_of_eq], 
      apply hP₂ 
    end
   ... ≤ ∫⁻ (ω₁ : Ω₁), ε₂ * P₂ {ω₂ : Ω₂ | (M₁ x₀ ω₁, M₂ (M₁ x₀ ω₁) x₁ ω₂) ∈ 𝒱'} + δ₂ ∂P₁ : 
    begin
      apply lintegral_mono,
      intro ω₁,
      apply aux,
    end
   ... = ∫⁻ (ω₁ : Ω₁), ε₂ * P₂ {ω₂ : Ω₂ | (M₁ x₀ ω₁, M₂ (M₁ x₀ ω₁) x₁ ω₂) ∈ 𝒱'} ∂P₁ +
           δ₂ * P₁ set.univ :
    begin
      rw lintegral_add,
      rw lintegral_const,
      measurability,
      sorry -- measurability
    end
   ... ≤ sorry : sorry
end