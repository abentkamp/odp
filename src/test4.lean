import .adversary

open measure_theory ennreal database_type
open_locale ennreal

variables {Ω₁ Ω₂ : Type} [measurable_space Ω₁] [measurable_space Ω₂] 

variables (P₁ : measure Ω₁) (P₂ : measure Ω₂) 

variables (O₁ O₂ : Type) [measurable_space O₁] [measurable_space O₂]

variables (X : Type) [database_type X] (x₀ x₁ : X) (hx : neighboring x₀ x₁)

variables (M₁ : X → Ω₁ → O₁) (p : odp_partition P₁ M₁)

variables (ε δ : ℝ≥0∞) 

variables (M₂₀ M₂₁ : O₁ → Ω₂ → O₂) 
  

local infix ` ⊗ `:50  := measure.prod

lemma induction_step 
  (hM₂ : ∀ o₁ : O₁, diff_private_aux P₂ (M₂₀ o₁) (M₂₁ o₁) 
    (ε - εusage p o₁) (δ - δusage p o₁)) : 
  diff_private_aux (P₁ ⊗ P₂) 
    (λ ω, prod.mk (M₁ x₀ ω.1) (M₂₀ (M₁ x₀ ω.1) ω.2))
    (λ ω, prod.mk (M₁ x₁ ω.1) (M₂₁ (M₁ x₁ ω.1) ω.2)) ε δ := sorry
